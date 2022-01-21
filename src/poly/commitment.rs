//! This module contains an implementation of the polynomial commitment scheme
//! described in the [Halo][halo] paper.
//!
//! [halo]: https://eprint.iacr.org/2019/1021

use super::{Coeff, LagrangeCoeff, Polynomial, MSM};
use crate::arithmetic::{
    best_fft, best_multiexp, parallelize, CurveAffine, CurveExt, Engine, FieldExt, Group,
};
use crate::helpers::CurveRead;

use ff::{Field, PrimeField};
use group::{prime::PrimeCurveAffine, Curve, Group as _, GroupEncoding};
use rand::RngCore;
use std::marker::PhantomData;
use std::ops::{Add, AddAssign, Mul, MulAssign};

use std::io;

/// These are the prover parameters for the polynomial commitment scheme.
#[derive(Debug)]
pub struct Params<C: CurveAffine> {
    pub(crate) k: u32,
    pub(crate) n: u64,
    pub(crate) g: Vec<C>,
    pub(crate) g_lagrange: Vec<C>,
    pub(crate) additional_data: Vec<u8>,
}

/// These are the verifier parameters for the polynomial commitment scheme.
#[derive(Debug)]
pub struct ParamsVerifier<E: Engine> {
    pub(crate) k: u32,
    pub(crate) n: u64,
    pub(crate) g1: E::G1Affine,
    pub(crate) g2: E::G2Affine,
    pub(crate) s_g2: E::G2Affine,
    pub(crate) g_lagrange: Vec<E::G1Affine>,
}

/// Helps to specify the engine we use to generate parameters
#[derive(Debug)]
pub struct Setup<E: Engine> {
    _marker: PhantomData<E>,
}

impl<E: Engine> Setup<E> {
    /// Initializes parameters for the curve, given a random oracle to draw
    /// points from.
    #[allow(clippy::new_ret_no_self)]
    pub fn new(k: u32, mut rng: impl RngCore) -> Params<E::G1Affine> {
        // TODO: Make this function only available in test mod
        // Largest root of unity exponent of the Engine is `2^E::Scalar::S`, so we can
        // only support FFTs of polynomials below degree `2^E::Scalar::S`.
        assert!(k <= E::Scalar::S);
        let n: u64 = 1 << k;

        let s = E::Scalar::random(&mut rng);

        let mut g_projective: Vec<E::G1> = Vec::with_capacity(n as usize);
        let g1 = <E::G1Affine as PrimeCurveAffine>::generator();
        g_projective.push(g1.into());
        // g = [G1, [s] G1, [s^2] G1, ..., [s^(n-1)] G1]
        for i in 1..(n as usize) {
            g_projective.push(g_projective[i - 1] * s);
        }

        let g = {
            let mut g = vec![E::G1Affine::identity(); n as usize];
            parallelize(&mut g, |g, starts| {
                E::G1::batch_normalize(&g_projective[starts..(starts + g.len())], g);
            });
            g
        };

        // Let's evaluate all of the Lagrange basis polynomials
        // using an inverse FFT.
        let mut alpha_inv = E::Scalar::ROOT_OF_UNITY_INV;
        for _ in k..E::Scalar::S {
            alpha_inv = alpha_inv.square();
        }
        let mut g_lagrange_projective = g_projective;
        best_fft(&mut g_lagrange_projective, alpha_inv, k);
        let minv = E::Scalar::TWO_INV.pow_vartime(&[k as u64, 0, 0, 0]);
        parallelize(&mut g_lagrange_projective, |g, _| {
            for g in g.iter_mut() {
                *g *= minv;
            }
        });

        let g_lagrange = {
            let mut g_lagrange = vec![E::G1Affine::identity(); n as usize];
            parallelize(&mut g_lagrange, |g_lagrange, starts| {
                E::G1::batch_normalize(
                    &g_lagrange_projective[starts..(starts + g_lagrange.len())],
                    g_lagrange,
                );
            });
            drop(g_lagrange_projective);
            g_lagrange
        };

        let g2 = <E::G2Affine as PrimeCurveAffine>::generator();
        let s_g2 = g2 * s;
        let additional_data = Vec::from(s_g2.to_bytes().as_ref());
        Params {
            k,
            n,
            g,
            g_lagrange,
            additional_data,
        }
    }

    /// Returns verifier params with size of lagrage bases equal to number of public inputs
    pub fn verifier_params(
        params: &Params<E::G1Affine>,
        public_inputs_size: usize,
    ) -> io::Result<ParamsVerifier<E>> {
        assert!(public_inputs_size < params.n as usize);
        let g_lagrange = params.g_lagrange[..public_inputs_size].to_vec();
        let g2 = <E::G2Affine as PrimeCurveAffine>::generator();

        let additional_data = params.additional_data.clone();

        let s_g2 = E::G2Affine::read(&mut additional_data.as_slice())?;

        Ok(ParamsVerifier {
            k: params.k,
            n: params.n,
            g1: params.g[0],
            g_lagrange,
            g2,
            s_g2,
        })
    }
}

impl<C: CurveAffine> Params<C> {
    /// This computes a commitment to a polynomial described by the provided
    /// slice of coefficients. The commitment will be blinded by the blinding
    /// factor `r`.
    pub fn commit(&self, poly: &Polynomial<C::Scalar, Coeff>) -> C::Curve {
        let mut scalars = Vec::with_capacity(poly.len());
        scalars.extend(poly.iter());
        let bases = &self.g;
        let size = scalars.len();
        assert!(bases.len() >= size);
        best_multiexp(&scalars, &bases[0..size])
    }

    /// This commits to a polynomial using its evaluations over the $2^k$ size
    /// evaluation domain. The commitment will be blinded by the blinding factor
    /// `r`.
    pub fn commit_lagrange(&self, poly: &Polynomial<C::Scalar, LagrangeCoeff>) -> C::Curve {
        let mut scalars = Vec::with_capacity(poly.len());
        scalars.extend(poly.iter());
        let bases = &self.g_lagrange;
        let size = scalars.len();
        assert!(bases.len() >= size);
        best_multiexp(&scalars, &bases[0..size])
    }

    /// Generates an empty multiscalar multiplication struct using the
    /// appropriate params.
    pub fn empty_msm(&self) -> MSM<C> {
        MSM::new()
    }

    /// Getter for g generators
    pub fn get_g(&self) -> Vec<C> {
        self.g.clone()
    }

    /// Writes params to a buffer.
    pub fn write<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        writer.write_all(&self.k.to_le_bytes())?;
        for el in &self.g {
            writer.write_all(el.to_bytes().as_ref())?;
        }
        for el in &self.g_lagrange {
            writer.write_all(el.to_bytes().as_ref())?;
        }
        let additional_data_len = self.additional_data.len() as u32;
        writer.write_all(&additional_data_len.to_le_bytes())?;
        writer.write_all(&self.additional_data)?;
        Ok(())
    }

    /// Reads params from a buffer.
    pub fn read<R: io::Read>(mut reader: R) -> io::Result<Self> {
        let mut k = [0u8; 4];
        reader.read_exact(&mut k[..])?;
        let k = u32::from_le_bytes(k);
        let n = 1 << k;

        let g: Vec<C> = (0..n)
            .map(|_| C::read(&mut reader))
            .collect::<Result<_, _>>()?;
        let g_lagrange: Vec<C> = (0..n)
            .map(|_| C::read(&mut reader))
            .collect::<Result<_, _>>()?;

        let mut additional_data_len = [0u8; 4];
        reader.read_exact(&mut additional_data_len[..])?;
        let additional_data_len = u32::from_le_bytes(additional_data_len);
        let mut additional_data = vec![0u8; additional_data_len as usize];

        reader.read_exact(&mut additional_data[..])?;

        Ok(Params {
            k,
            n,
            g,
            g_lagrange,
            additional_data,
        })
    }
}

/// Wrapper type around a blinding factor.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Blind<F>(pub F);

impl<F: FieldExt> Default for Blind<F> {
    fn default() -> Self {
        Blind(F::one())
    }
}

impl<F: FieldExt> Add for Blind<F> {
    type Output = Self;

    fn add(self, rhs: Blind<F>) -> Self {
        Blind(self.0 + rhs.0)
    }
}

impl<F: FieldExt> Mul for Blind<F> {
    type Output = Self;

    fn mul(self, rhs: Blind<F>) -> Self {
        Blind(self.0 * rhs.0)
    }
}

impl<F: FieldExt> AddAssign for Blind<F> {
    fn add_assign(&mut self, rhs: Blind<F>) {
        self.0 += rhs.0;
    }
}

impl<F: FieldExt> MulAssign for Blind<F> {
    fn mul_assign(&mut self, rhs: Blind<F>) {
        self.0 *= rhs.0;
    }
}

impl<F: FieldExt> AddAssign<F> for Blind<F> {
    fn add_assign(&mut self, rhs: F) {
        self.0 += rhs;
    }
}

impl<F: FieldExt> MulAssign<F> for Blind<F> {
    fn mul_assign(&mut self, rhs: F) {
        self.0 *= rhs;
    }
}

impl<E: Engine> ParamsVerifier<E> {
    /// Returns maximum public input size allowed
    pub fn public_inputs_size(&self) -> usize {
        self.g_lagrange.len()
    }

    /// Generates an empty multiscalar multiplication struct using the
    /// appropriate params.
    pub fn empty_msm(&self) -> MSM<E::G1Affine> {
        MSM::new()
    }

    /// Commits to a polynomial using its evaluations over the $2^k$ size
    /// evaluation domain.
    pub fn commit_lagrange(&self, scalars: Vec<E::Scalar>) -> E::G1 {
        let bases = &self.g_lagrange;
        let size = scalars.len();
        assert!(bases.len() >= size);
        best_multiexp(&scalars, &bases[0..size])
    }

    /// Writes params to a buffer.
    pub fn write<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        writer.write_all(&self.k.to_le_bytes())?;
        let public_inputs_size = self.public_inputs_size() as u32;
        writer.write_all(&public_inputs_size.to_le_bytes())?;

        writer.write_all(self.g1.to_bytes().as_ref())?;
        writer.write_all(self.g2.to_bytes().as_ref())?;
        writer.write_all(self.s_g2.to_bytes().as_ref())?;
        for el in &self.g_lagrange {
            writer.write_all(el.to_bytes().as_ref())?;
        }
        Ok(())
    }

    /// Reads params from a buffer.
    pub fn read<R: io::Read>(mut reader: R) -> io::Result<Self> {
        let mut k = [0u8; 4];
        reader.read_exact(&mut k[..])?;
        let k = u32::from_le_bytes(k);

        let mut public_inputs_size = [0u8; 4];
        reader.read_exact(&mut public_inputs_size[..])?;
        let public_inputs_size = u32::from_le_bytes(public_inputs_size);

        let n = 1 << k;

        let g1 = E::G1Affine::read(&mut reader)?;
        let g2 = E::G2Affine::read(&mut reader)?;
        let s_g2 = E::G2Affine::read(&mut reader)?;
        let g_lagrange: Vec<E::G1Affine> = (0..public_inputs_size)
            .map(|_| E::G1Affine::read(&mut reader))
            .collect::<Result<_, _>>()?;

        Ok(ParamsVerifier {
            k,
            n,
            g1,
            g2,
            s_g2,
            g_lagrange,
        })
    }
}

#[cfg(test)]
use pairing::bn256::{Bn256, Fr, G1Affine};
#[cfg(test)]
use rand::SeedableRng;
#[cfg(test)]
use rand_xorshift::XorShiftRng;

#[test]
fn test_parameter_serialization() {
    const K: u32 = 4;

    let rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    // Initialize the polynomial commitment parameters
    let params0 = Setup::<Bn256>::new(K, rng);
    let mut data: Vec<u8> = Vec::new();
    params0.write(&mut data).unwrap();
    let params1: Params<G1Affine> = Params::read(&data[..]).unwrap();

    assert_eq!(params0.k, params1.k);
    assert_eq!(params0.n, params1.n);
    assert_eq!(params0.g.len(), params1.g.len());
    assert_eq!(params0.g_lagrange.len(), params1.g_lagrange.len());

    assert_eq!(params0.g, params1.g);
    assert_eq!(params0.g_lagrange, params1.g_lagrange);
    assert_eq!(params0.additional_data, params1.additional_data);

    let public_inputs_size = 2;
    let verifier_params0 = Setup::<Bn256>::verifier_params(&params0, public_inputs_size).unwrap();

    assert_eq!(verifier_params0.k, params1.k);
    assert_eq!(verifier_params0.n, params1.n);
    assert_eq!(verifier_params0.g_lagrange.len(), public_inputs_size);
    assert_eq!(
        verifier_params0.s_g2.to_bytes().as_ref(),
        params0.additional_data
    );

    let mut data: Vec<u8> = Vec::new();
    verifier_params0.write(&mut data).unwrap();
    let verifier_params1: ParamsVerifier<Bn256> = ParamsVerifier::read(&data[..]).unwrap();
    assert_eq!(verifier_params0.k, verifier_params1.k);
    assert_eq!(verifier_params0.n, verifier_params1.n);
    assert_eq!(verifier_params0.g1, verifier_params1.g1);
    assert_eq!(verifier_params0.g2, verifier_params1.g2);
    assert_eq!(verifier_params0.s_g2, verifier_params1.s_g2);
    assert_eq!(verifier_params0.g_lagrange, verifier_params1.g_lagrange);
}

#[test]
fn test_commit_lagrange() {
    const K: u32 = 6;

    let rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    // Initialize the polynomial commitment parameters
    let params = Setup::<Bn256>::new(K, rng);

    let domain = super::EvaluationDomain::new(1, K);

    let mut a = domain.empty_lagrange();

    for (i, a) in a.iter_mut().enumerate() {
        *a = Fr::from(i as u64);
    }

    let b = domain.lagrange_to_coeff(a.clone());
    assert_eq!(params.commit(&b), params.commit_lagrange(&a));
}
