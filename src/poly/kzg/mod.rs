use halo2curves::pairing::Engine;
use std::marker::PhantomData;

/// Multiscalar multiplication engines
pub mod msm;
/// KZG commitment scheme
pub mod params;

use std::fmt::Debug;

use crate::arithmetic::{best_multiexp, kate_division, powers, MSM};
use crate::poly::kzg::msm::{DualMSM, MSMKZG};
use crate::poly::kzg::params::{ParamsKZG, ParamsVerifierKZG};
use crate::poly::query::Query;
use crate::poly::query::VerifierQuery;
use crate::poly::{Coeff, Error, Polynomial, ProverQuery};

use crate::poly::commitment::PolynomialCommitmentScheme;
use crate::transcript::{Hashable, Sampleable, Transcript};
use ff::Field;
use group::prime::PrimeCurveAffine;
use halo2curves::pairing::MultiMillerLoop;
use halo2curves::serde::SerdeObject;

#[derive(Clone, Debug)]
/// KZG verifier
pub struct KZGCommitmentScheme<E: Engine> {
    _marker: PhantomData<E>,
}

impl<E: MultiMillerLoop> PolynomialCommitmentScheme<E::Fr> for KZGCommitmentScheme<E>
where
    E::Fr: SerdeObject,
    E::G1Affine: Default + SerdeObject,
{
    type Parameters = ParamsKZG<E>;
    type VerifierParameters = ParamsVerifierKZG<E>;
    type Commitment = E::G1Affine;

    /// Unsafe function - do not use in production
    fn setup(k: u32) -> ParamsKZG<E> {
        ParamsKZG::new(k)
    }

    fn commit(
        params: &Self::Parameters,
        polynomial: &Polynomial<E::Fr, Coeff>,
    ) -> Self::Commitment {
        let mut scalars = Vec::with_capacity(polynomial.len());
        scalars.extend(polynomial.iter());
        let bases = &params.g;
        let size = scalars.len();
        assert!(bases.len() >= size);
        best_multiexp(&scalars, &bases[0..size]).into()
    }

    fn open<'com, T: Transcript, I>(
        params: &Self::Parameters,
        prover_query: I,
        transcript: &mut T,
    ) -> Result<(), Error>
    where
        I: IntoIterator<Item = ProverQuery<'com, E::Fr>> + Clone,
        E::Fr: Sampleable<T::Hash>,
        E::G1Affine: Hashable<T::Hash>,
    {
        let v: E::Fr = transcript.squeeze_challenge();
        let commitment_data = construct_intermediate_sets(prover_query);

        for commitment_at_a_point in commitment_data.iter() {
            let z = commitment_at_a_point.point;
            let (poly_batch, eval_batch) = commitment_at_a_point
                .queries
                .iter()
                .zip(powers(v))
                .map(|(query, power_of_v)| {
                    assert_eq!(query.get_point(), z);

                    let poly = query.get_commitment().poly;
                    let eval = query.get_eval();

                    (poly.clone() * power_of_v, eval * power_of_v)
                })
                .reduce(|(poly_acc, eval_acc), (poly, eval)| (poly_acc + &poly, eval_acc + eval))
                .unwrap();

            let poly_batch = &poly_batch - eval_batch;
            let witness_poly = Polynomial {
                values: kate_division(&poly_batch.values, z),
                _marker: PhantomData,
            };
            let w = Self::commit(params, &witness_poly);

            transcript.write(&w).map_err(|_| Error::OpeningError)?;
        }

        Ok(())
    }

    fn verify<T: Transcript, I>(
        params: &Self::VerifierParameters,
        verifier_query: I,
        transcript: &mut T,
    ) -> Result<(), Error>
    where
        E::Fr: Sampleable<T::Hash>,
        E::G1Affine: Hashable<T::Hash>,
        I: IntoIterator<Item = VerifierQuery<E::Fr, KZGCommitmentScheme<E>>> + Clone,
    {
        let v: E::Fr = transcript.squeeze_challenge();

        let commitment_data = construct_intermediate_sets(verifier_query);

        let w = (0..commitment_data.len())
            .map(|_| transcript.read().map_err(|_| Error::SamplingError))
            .collect::<Result<Vec<E::G1Affine>, Error>>()?;

        let u: E::Fr = transcript.squeeze_challenge();

        let mut commitment_multi = MSMKZG::<E>::new();
        let mut eval_multi = E::Fr::ZERO;

        let mut witness = MSMKZG::<E>::new();
        let mut witness_with_aux = MSMKZG::<E>::new();

        for ((commitment_at_a_point, wi), power_of_u) in
            commitment_data.iter().zip(w.into_iter()).zip(powers(u))
        {
            assert!(!commitment_at_a_point.queries.is_empty());
            let z = commitment_at_a_point.point;

            let (mut commitment_batch, eval_batch) = commitment_at_a_point
                .queries
                .iter()
                .zip(powers(v))
                .map(|(query, power_of_v)| {
                    assert_eq!(query.get_point(), z);

                    let mut commitment = MSMKZG::<E>::new();
                    commitment.append_term(power_of_v, query.get_commitment().to_curve());

                    let eval = power_of_v * query.get_eval();

                    (commitment, eval)
                })
                .reduce(|(mut commitment_acc, eval_acc), (commitment, eval)| {
                    commitment_acc.add_msm(&commitment);
                    (commitment_acc, eval_acc + eval)
                })
                .unwrap();

            commitment_batch.scale(power_of_u);
            commitment_multi.add_msm(&commitment_batch);
            eval_multi += power_of_u * eval_batch;

            witness_with_aux.append_term(power_of_u * z, wi.to_curve());
            witness.append_term(power_of_u, wi.to_curve());
        }

        let mut msm = DualMSM::new(params);

        msm.left.add_msm(&witness);

        msm.right.add_msm(&witness_with_aux);
        msm.right.add_msm(&commitment_multi);
        let g0: E::G1 = params.g[0].to_curve();
        msm.right.append_term(eval_multi, -g0);

        if msm.check() {
            Ok(())
        } else {
            Err(Error::OpeningError)
        }
    }
}

#[derive(Debug)]
struct CommitmentData<F: Field, Q: Query<F>> {
    queries: Vec<Q>,
    point: F,
    _marker: PhantomData<F>,
}

fn construct_intermediate_sets<F: Field, I, Q: Query<F>>(queries: I) -> Vec<CommitmentData<F, Q>>
where
    I: IntoIterator<Item = Q> + Clone,
{
    let mut point_query_map: Vec<(F, Vec<Q>)> = Vec::new();
    for query in queries {
        if let Some(pos) = point_query_map
            .iter()
            .position(|(point, _)| *point == query.get_point())
        {
            let (_, queries) = &mut point_query_map[pos];
            queries.push(query);
        } else {
            point_query_map.push((query.get_point(), vec![query]));
        }
    }

    point_query_map
        .into_iter()
        .map(|(point, queries)| CommitmentData {
            queries,
            point,
            _marker: PhantomData,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::arithmetic::eval_polynomial;
    use crate::poly::commitment::PolynomialCommitmentScheme;
    use crate::poly::kzg::params::{ParamsKZG, ParamsVerifierKZG};
    use crate::poly::kzg::KZGCommitmentScheme;
    use crate::poly::{
        query::{ProverQuery, VerifierQuery},
        Error, EvaluationDomain,
    };
    use crate::transcript::{CircuitTranscript, Hashable, Sampleable, Transcript};
    use blake2b_simd::State as Blake2bState;
    use halo2curves::pairing::{Engine, MultiMillerLoop};
    use halo2curves::serde::SerdeObject;
    use halo2curves::CurveAffine;

    #[test]
    fn test_roundtrip_gwc() {
        use crate::poly::kzg::KZGCommitmentScheme;
        use halo2curves::bn256::Bn256;

        const K: u32 = 4;

        let params = KZGCommitmentScheme::<Bn256>::setup(K);

        let proof = create_proof::<_, CircuitTranscript<Blake2bState>>(&params);

        verify::<_, CircuitTranscript<Blake2bState>>(&params, &proof[..], false);

        verify::<Bn256, CircuitTranscript<Blake2bState>>(&params, &proof[..], true);
    }

    fn verify<E: MultiMillerLoop, T: Transcript>(
        verifier_params: &ParamsVerifierKZG<E>,
        proof: &[u8],
        should_fail: bool,
    ) where
        E::Fr: SerdeObject + Hashable<T::Hash> + Sampleable<T::Hash>,
        E::G1Affine: CurveAffine<ScalarExt = <E as Engine>::Fr, CurveExt = <E as Engine>::G1>
            + SerdeObject
            + Hashable<T::Hash>,
    {
        let mut transcript = T::parse(proof);

        let a: E::G1Affine = transcript.read().unwrap();
        let b: E::G1Affine = transcript.read().unwrap();
        let c: E::G1Affine = transcript.read().unwrap();

        let x: E::Fr = transcript.squeeze_challenge();
        let y: E::Fr = transcript.squeeze_challenge();

        let avx: E::Fr = transcript.read().unwrap();
        let bvx: E::Fr = transcript.read().unwrap();
        let cvy: E::Fr = transcript.read().unwrap();

        let valid_queries = std::iter::empty()
            .chain(Some(VerifierQuery::new(x, a, avx)))
            .chain(Some(VerifierQuery::new(x, b, bvx)))
            .chain(Some(VerifierQuery::new(y, c, cvy)));

        let invalid_queries = std::iter::empty()
            .chain(Some(VerifierQuery::new(x, a, avx)))
            .chain(Some(VerifierQuery::new(x, b, avx)))
            .chain(Some(VerifierQuery::new(y, c, cvy)));

        let queries = if should_fail {
            invalid_queries
        } else {
            valid_queries
        };

        let result = KZGCommitmentScheme::verify(verifier_params, queries, &mut transcript)
            .map_err(|_| Error::OpeningError);

        if should_fail {
            assert!(result.is_err());
        } else {
            assert!(result.is_ok());
        }
    }

    fn create_proof<E: MultiMillerLoop, T: Transcript>(kzg_params: &ParamsKZG<E>) -> Vec<u8>
    where
        E::Fr: SerdeObject + Hashable<T::Hash> + Sampleable<T::Hash>,
        E::G1Affine: SerdeObject + Hashable<T::Hash> + Default,
    {
        let domain = EvaluationDomain::new(1, kzg_params.k);

        let mut ax = domain.empty_coeff();
        for (i, a) in ax.iter_mut().enumerate() {
            *a = <E::Fr>::from(10 + i as u64);
        }

        let mut bx = domain.empty_coeff();
        for (i, a) in bx.iter_mut().enumerate() {
            *a = <E::Fr>::from(100 + i as u64);
        }

        let mut cx = domain.empty_coeff();
        for (i, a) in cx.iter_mut().enumerate() {
            *a = <E::Fr>::from(100 + i as u64);
        }

        let mut transcript = T::init();

        let a = KZGCommitmentScheme::commit(kzg_params, &ax);
        let b = KZGCommitmentScheme::commit(kzg_params, &bx);
        let c = KZGCommitmentScheme::commit(kzg_params, &cx);

        transcript.write(&a).unwrap();
        transcript.write(&b).unwrap();
        transcript.write(&c).unwrap();

        let x: E::Fr = transcript.squeeze_challenge();
        let y = transcript.squeeze_challenge();

        let avx = eval_polynomial(&ax, x);
        let bvx = eval_polynomial(&bx, x);
        let cvy = eval_polynomial(&cx, y);

        transcript.write(&avx).unwrap();
        transcript.write(&bvx).unwrap();
        transcript.write(&cvy).unwrap();

        let queries = [
            ProverQuery {
                point: x,
                poly: &ax,
            },
            ProverQuery {
                point: x,
                poly: &bx,
            },
            ProverQuery {
                point: y,
                poly: &cx,
            },
        ]
        .into_iter();

        KZGCommitmentScheme::open(kzg_params, queries, &mut transcript).unwrap();

        transcript.finalize()
    }
}
