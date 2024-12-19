use crate::utils::arithmetic::{g_to_lagrange, parallelize};
use crate::utils::SerdeFormat;

use ff::{Field, PrimeField};
use group::{prime::PrimeCurveAffine, Curve, Group};
use halo2curves::pairing::Engine;
use rand_core::RngCore;
use std::fmt::Debug;

use crate::utils::helpers::ProcessedSerdeObject;
use halo2curves::CurveAffine;
use std::io;

/// These are the public parameters for the polynomial commitment scheme.
#[derive(Debug, Clone)]
pub struct ParamsKZG<E: Engine> {
    pub(crate) g: Vec<E::G1Affine>,
    pub(crate) g_lagrange: Vec<E::G1Affine>,
    pub(crate) g2: E::G2Affine,
    pub(crate) s_g2: E::G2Affine,
}

impl<E: Engine + Debug> ParamsKZG<E> {
    /// Initializes parameters for the curve, draws toxic secret from given rng.
    /// MUST NOT be used in production.
    pub fn unsafe_setup<R: RngCore>(k: u32, rng: R) -> Self {
        // Largest root of unity exponent of the Engine is `2^E::Fr::S`, so we can
        // only support FFTs of polynomials below degree `2^E::Fr::S`.
        assert!(k <= E::Fr::S);
        let n: u64 = 1 << k;

        // Calculate g = [G1, [s] G1, [s^2] G1, ..., [s^(n-1)] G1] in parallel.
        let g1 = E::G1Affine::generator();
        let s = <E::Fr>::random(rng);

        let mut g_projective = vec![E::G1::identity(); n as usize];
        parallelize(&mut g_projective, |g, start| {
            let mut current_g: E::G1 = g1.into();
            current_g *= s.pow_vartime([start as u64]);
            for g in g.iter_mut() {
                *g = current_g;
                current_g *= s;
            }
        });

        let g = {
            let mut g = vec![E::G1Affine::identity(); n as usize];
            parallelize(&mut g, |g, starts| {
                E::G1::batch_normalize(&g_projective[starts..(starts + g.len())], g);
            });
            g
        };

        let mut g_lagrange_projective = vec![E::G1::identity(); n as usize];
        let mut root = E::Fr::ROOT_OF_UNITY;
        for _ in k..E::Fr::S {
            root = root.square();
        }
        let n_inv = E::Fr::from(n)
            .invert()
            .expect("inversion should be ok for n = 1<<k");
        let multiplier = (s.pow_vartime([n]) - E::Fr::ONE) * n_inv;
        parallelize(&mut g_lagrange_projective, |g, start| {
            for (idx, g) in g.iter_mut().enumerate() {
                let offset = start + idx;
                let root_pow = root.pow_vartime([offset as u64]);
                let scalar = multiplier * root_pow * (s - root_pow).invert().unwrap();
                *g = g1 * scalar;
            }
        });

        let g_lagrange = {
            let mut g_lagrange = vec![E::G1Affine::identity(); n as usize];
            parallelize(&mut g_lagrange, |g_lagrange, start| {
                let end = start + g_lagrange.len();
                E::G1::batch_normalize(&g_lagrange_projective[start..end], g_lagrange);
            });
            drop(g_lagrange_projective);
            g_lagrange
        };

        let g2 = <E::G2Affine as PrimeCurveAffine>::generator();
        let s_g2 = (g2 * s).into();

        Self {
            g,
            g_lagrange,
            g2,
            s_g2,
        }
    }

    /// Initializes parameters for the curve through existing parameters
    /// k, g, g_lagrange (optional), g2, s_g2
    pub fn from_parts(
        &self,
        k: u32,
        g: Vec<E::G1Affine>,
        g_lagrange: Option<Vec<E::G1Affine>>,
        g2: E::G2Affine,
        s_g2: E::G2Affine,
    ) -> Self {
        Self {
            g_lagrange: match g_lagrange {
                Some(g_l) => g_l,
                None => g_to_lagrange(g.iter().map(PrimeCurveAffine::to_curve).collect(), k),
            },
            g,
            g2,
            s_g2,
        }
    }

    /// Returns gernerator on G2
    pub fn g2(&self) -> E::G2Affine {
        self.g2
    }

    /// Returns first power of secret on G2
    pub fn s_g2(&self) -> E::G2Affine {
        self.s_g2
    }

    /// Writes parameters to buffer
    pub fn write_custom<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()>
    where
        E::G1Affine: CurveAffine + ProcessedSerdeObject,
        E::G2Affine: CurveAffine + ProcessedSerdeObject,
    {
        writer.write_all(&(self.g.len() as u64).to_le_bytes())?;
        for el in self.g.iter() {
            el.write(writer, format)?;
        }
        for el in self.g_lagrange.iter() {
            el.write(writer, format)?;
        }
        self.g2.write(writer, format)?;
        self.s_g2.write(writer, format)?;
        Ok(())
    }

    /// Reads params from a buffer.
    pub fn read_custom<R: io::Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self>
    where
        E::G1Affine: CurveAffine + ProcessedSerdeObject,
        E::G2Affine: CurveAffine + ProcessedSerdeObject,
    {
        let mut n = [0u8; 8];
        reader.read_exact(&mut n[..])?;
        let n = u64::from_le_bytes(n) as usize;

        let (g, g_lagrange) = match format {
            SerdeFormat::Processed => {
                use group::GroupEncoding;
                let load_points_from_file_parallelly =
                    |reader: &mut R| -> io::Result<Vec<Option<E::G1Affine>>> {
                        let mut points_compressed =
                            vec![<<E as Engine>::G1Affine as GroupEncoding>::Repr::default(); n];
                        for points_compressed in points_compressed.iter_mut() {
                            reader.read_exact((*points_compressed).as_mut())?;
                        }

                        let mut points = vec![Option::<E::G1Affine>::None; n];
                        parallelize(&mut points, |points, chunks| {
                            for (i, point) in points.iter_mut().enumerate() {
                                *point = Option::from(E::G1Affine::from_bytes(
                                    &points_compressed[chunks + i],
                                ));
                            }
                        });
                        Ok(points)
                    };

                let g = load_points_from_file_parallelly(reader)?;
                let g: Vec<<E as Engine>::G1Affine> = g
                    .iter()
                    .map(|point| {
                        point.ok_or_else(|| {
                            io::Error::new(io::ErrorKind::Other, "invalid point encoding")
                        })
                    })
                    .collect::<Result<_, _>>()?;
                let g_lagrange = load_points_from_file_parallelly(reader)?;
                let g_lagrange: Vec<<E as Engine>::G1Affine> = g_lagrange
                    .iter()
                    .map(|point| {
                        point.ok_or_else(|| {
                            io::Error::new(io::ErrorKind::Other, "invalid point encoding")
                        })
                    })
                    .collect::<Result<_, _>>()?;
                (g, g_lagrange)
            }
            SerdeFormat::RawBytes => {
                let g = (0..n)
                    .map(|_| <E::G1Affine as ProcessedSerdeObject>::read(reader, format))
                    .collect::<Result<Vec<_>, _>>()?;
                let g_lagrange = (0..n)
                    .map(|_| <E::G1Affine as ProcessedSerdeObject>::read(reader, format))
                    .collect::<Result<Vec<_>, _>>()?;
                (g, g_lagrange)
            }
            SerdeFormat::RawBytesUnchecked => {
                // avoid try branching for performance
                let g = (0..n)
                    .map(|_| <E::G1Affine as ProcessedSerdeObject>::read(reader, format).unwrap())
                    .collect::<Vec<_>>();
                let g_lagrange = (0..n)
                    .map(|_| <E::G1Affine as ProcessedSerdeObject>::read(reader, format).unwrap())
                    .collect::<Vec<_>>();
                (g, g_lagrange)
            }
        };

        let g2 = E::G2Affine::read(reader, format)?;
        let s_g2 = E::G2Affine::read(reader, format)?;

        Ok(Self {
            g,
            g_lagrange,
            g2,
            s_g2,
        })
    }
}

// TODO: see the issue at https://github.com/appliedzkp/halo2/issues/45
// So we probably need much smaller verifier key. However for new bases in g1 should be in verifier keys.
/// KZG multi-open verification parameters
#[derive(Debug)]
pub struct ParamsVerifierKZG<E: Engine> {
    pub(crate) s_g2: E::G2Affine,
}

impl<E: Engine + Debug> ParamsVerifierKZG<E>
where
    E::G1Affine: CurveAffine + ProcessedSerdeObject,
    E::G2Affine: CurveAffine + ProcessedSerdeObject,
{
    /// Writes parameters to buffer
    pub fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()> {
        self.s_g2.write(writer, format)?;
        Ok(())
    }

    /// Reads params from a buffer.
    pub fn read<R: io::Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self> {
        let s_g2 = E::G2Affine::read(reader, format)?;

        Ok(Self { s_g2 })
    }
}

impl<E: Engine + Debug> ParamsKZG<E> {
    /// Consume the prover parameters into verifier parameters. Need to specify the size of
    /// public inputs.
    pub fn verifier_params(&self) -> ParamsVerifierKZG<E> {
        ParamsVerifierKZG { s_g2: self.s_g2 }
    }
}

#[cfg(test)]
mod test {
    use crate::poly::commitment::PolynomialCommitmentScheme;
    use crate::poly::kzg::params::ParamsKZG;
    use crate::poly::kzg::KZGCommitmentScheme;
    use crate::utils::SerdeFormat;
    use rand_core::OsRng;

    #[test]
    fn test_commit_lagrange() {
        const K: u32 = 6;

        use crate::poly::EvaluationDomain;
        use halo2curves::bn256::{Bn256, Fr};

        let params: ParamsKZG<Bn256> = ParamsKZG::unsafe_setup(K, OsRng);
        let domain = EvaluationDomain::new(1, K);

        let mut a = domain.empty_lagrange();

        for (i, a) in a.iter_mut().enumerate() {
            *a = Fr::from(i as u64);
        }

        let b = domain.lagrange_to_coeff(a.clone());

        let tmp = KZGCommitmentScheme::commit_lagrange(&params, &a);
        let commitment = KZGCommitmentScheme::commit(&params, &b);

        assert_eq!(commitment, tmp);
    }

    #[test]
    fn test_parameter_serialisation_roundtrip() {
        const K: u32 = 4;

        use crate::halo2curves::bn256::Bn256;

        let params0: ParamsKZG<Bn256> = ParamsKZG::unsafe_setup(K, OsRng);
        let mut data = vec![];
        ParamsKZG::write_custom(&params0, &mut data, SerdeFormat::RawBytesUnchecked).unwrap();
        let params1 =
            ParamsKZG::<Bn256>::read_custom::<_>(&mut &data[..], SerdeFormat::RawBytesUnchecked)
                .unwrap();

        assert_eq!(params0.g.len(), params1.g.len());
        assert_eq!(params0.g_lagrange.len(), params1.g_lagrange.len());

        assert_eq!(params0.g, params1.g);
        assert_eq!(params0.g_lagrange, params1.g_lagrange);
        assert_eq!(params0.g2, params1.g2);
        assert_eq!(params0.s_g2, params1.s_g2);
    }
}
