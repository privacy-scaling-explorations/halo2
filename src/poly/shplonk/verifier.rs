use std::marker::PhantomData;

use ff::Field;
use rand::rngs::OsRng;

use super::super::{commitment::Params, Coeff, Error, Polynomial};
use super::{
    construct_intermediate_sets, ChallengeU, ChallengeV, CommitmentReference, Query, VerifierQuery,
};
use crate::arithmetic::{
    eval_polynomial, lagrange_interpolate, vanishing_polynomial, CurveAffine, FieldExt,
};
use crate::poly::commitment::ParamsVerifier;
use crate::transcript::{EncodedChallenge, TranscriptRead};
use group::prime::PrimeCurveAffine;
use group::{Curve, Group};
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
    let (commitment_data, all_points) = construct_intermediate_sets(queries);

    let calculate_low_degree_equivalent =
        |points: &[C::Scalar], evals: &[C::Scalar]| -> Polynomial<C::Scalar, Coeff> {
            let values = lagrange_interpolate(points, evals);
            Polynomial {
                values,
                _marker: PhantomData,
            }
        };

    let v: ChallengeV<_> = transcript.squeeze_challenge_scalar();

    let h1 = transcript.read_point().map_err(|_| Error::SamplingError)?;
    let u: ChallengeU<_> = transcript.squeeze_challenge_scalar();

    let h2 = transcript.read_point().map_err(|_| Error::SamplingError)?;

    let zt_x = vanishing_polynomial(&all_points[..]);
    let zt_eval = eval_polynomial(&zt_x[..], *u);

    let low_degree_equivalent_commitments: Vec<C::G1Affine> = commitment_data
        .iter()
        .map(|commitment_data| {
            let queries = &commitment_data.points;

            let evals: Vec<C::Scalar> = queries.iter().map(|(_, eval)| *eval).collect();
            let points: Vec<_> = queries
                .iter()
                .map(|(evaluation_point, _)| *evaluation_point)
                .collect();

            let r_x = calculate_low_degree_equivalent(&points[..], &evals[..]);
            let r_eval = eval_polynomial(&r_x.values, *u);

            (params.g1 * r_eval).into()
        })
        .collect();

    let (contribs_projective, z): (Vec<C::G1>, Vec<C::Scalar>) = commitment_data
        .iter()
        .zip(low_degree_equivalent_commitments.iter())
        .map(|(commitment_data, low_degree_equivalent)| {
            let z_diff = vanishing_polynomial(&commitment_data.diffs[..]);
            let z_i = eval_polynomial(&z_diff[..], *u);

            let contrib = match commitment_data.commitment {
                CommitmentReference::Commitment(c) => *c - *low_degree_equivalent,
                CommitmentReference::MSM(msm) => msm.eval() - *low_degree_equivalent,
            };

            (contrib, z_i)
        })
        .unzip();

    let mut contribs = vec![C::G1Affine::identity(); contribs_projective.len()];
    C::G1::batch_normalize(&contribs_projective, &mut contribs);
    let mut combinator = params.empty_msm();
    for (contrib, z_i) in contribs.iter().zip(z.iter()) {
        combinator.append_term(*z_i, *contrib);
    }
    combinator.combine_with_base(*v);
    combinator.append_term(-zt_eval, h1);
    combinator.append_term(*u, h2);

    let l = combinator.eval();

    let s_g2 = C::G2Prepared::from(params.s_g2);
    let n_g2 = C::G2Prepared::from(-params.g2);

    let term_1 = (&h2, &s_g2);
    let term_2 = (&l, &n_g2);

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
