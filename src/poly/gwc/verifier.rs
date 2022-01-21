use ff::Field;
use rand::rngs::OsRng;

use super::super::{commitment::Params, Error};
use super::{
    construct_intermediate_sets, ChallengeU, ChallengeV, CommitmentReference, Query, VerifierQuery,
};
use crate::arithmetic::{eval_polynomial, lagrange_interpolate, CurveAffine, FieldExt};
use crate::poly::commitment::ParamsVerifier;
use crate::transcript::{EncodedChallenge, TranscriptRead};
use group::Group;
use pairing::arithmetic::{MillerLoopResult, MultiMillerLoop};
use subtle::Choice;

/// Verify a multi-opening proof
pub fn verify_proof<
    'r,
    'params: 'r,
    I,
    C: MultiMillerLoop,
    E: EncodedChallenge<C::G1Affine>,
    T: TranscriptRead<C::G1Affine, E>,
>(
    params: &'params ParamsVerifier<C>,
    transcript: &mut T,
    queries: I,
) -> Result<Choice, Error>
where
    I: IntoIterator<Item = VerifierQuery<'r, C::G1Affine>> + Clone,
{
    let v: ChallengeV<_> = transcript.squeeze_challenge_scalar();
    let u: ChallengeU<_> = transcript.squeeze_challenge_scalar();

    let commitment_data = construct_intermediate_sets(queries);

    let mut commitment_multi = params.empty_msm();
    let mut eval_multi = C::Scalar::zero();

    let mut witness = params.empty_msm();
    let mut witness_with_aux = params.empty_msm();

    for commitment_at_a_point in commitment_data.iter() {
        assert!(!commitment_at_a_point.queries.is_empty());
        let z = commitment_at_a_point.point;

        let wi = transcript.read_point().map_err(|_| Error::SamplingError)?;

        witness_with_aux.scale(*u);
        witness_with_aux.append_term(z, wi);
        witness.scale(*u);
        witness.append_term(C::Scalar::one(), wi);
        commitment_multi.scale(*u);
        eval_multi = eval_multi * *u;

        let mut commitment_batch = params.empty_msm();
        let mut eval_batch = C::Scalar::zero();

        for query in commitment_at_a_point.queries.iter() {
            assert_eq!(query.get_point(), z);

            let commitment = query.get_commitment();
            let eval = query.get_eval();

            commitment_batch.scale(*v);
            // let a = commitment
            // commitment_batch.append_term(C::Scalar::one(), *commitment.0);
            match commitment {
                CommitmentReference::Commitment(c) => {
                    commitment_batch.append_term(C::Scalar::one(), *c);
                }
                CommitmentReference::MSM(msm) => {
                    commitment_batch.add_msm(msm);
                }
            }

            eval_batch = eval_batch * *v + eval;
        }

        commitment_multi.add_msm(&commitment_batch);
        eval_multi += eval_batch;
    }

    let e = (-params.g1 * eval_multi).into();
    let f = commitment_multi.eval();
    let w = witness.eval();
    let zw = witness_with_aux.eval();

    let s_g2_prepared = C::G2Prepared::from(params.s_g2);
    let n_g2_prepared = C::G2Prepared::from(-params.g2);

    let term_1 = (&w, &s_g2_prepared);
    let term_2 = (&(zw + e + f).into(), &n_g2_prepared);

    Ok(C::multi_miller_loop(&[term_1, term_2])
        .final_exponentiation()
        .is_identity())
}

#[doc(hidden)]
#[derive(Copy, Clone)]
pub struct CommitmentPointer<'a, C>(&'a C);

impl<'a, C> PartialEq for CommitmentPointer<'a, C> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}

impl<'a, 'b, C: CurveAffine> Query<C::Scalar> for VerifierQuery<'a, C> {
    type Commitment = CommitmentReference<'a, C>;
    type Scalar = C::Scalar;

    fn get_point(&self) -> C::Scalar {
        self.point
    }
    fn get_eval(&self) -> C::Scalar {
        self.eval
    }
    fn get_commitment(&self) -> Self::Commitment {
        self.commitment
    }
}
