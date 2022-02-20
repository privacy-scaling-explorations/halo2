mod prover;
mod verifier;

use super::Query;
use crate::{
    arithmetic::{eval_polynomial, CurveAffine, FieldExt},
    poly::{
        commitment::{Params, ParamsVerifier},
        msm::MSM,
        Coeff, Polynomial,
    },
    transcript::ChallengeScalar,
};

use std::{
    collections::{BTreeMap, BTreeSet},
    marker::PhantomData,
};

pub use prover::create_proof;
pub use verifier::verify_proof;

#[derive(Clone, Copy, Debug)]
struct U {}
type ChallengeU<F> = ChallengeScalar<F, U>;

#[derive(Clone, Copy, Debug)]
struct V {}
type ChallengeV<F> = ChallengeScalar<F, V>;

struct CommitmentData<F: FieldExt, Q: Query<F>> {
    queries: Vec<Q>,
    point: F,
    _marker: PhantomData<F>,
}

fn construct_intermediate_sets<F: FieldExt, I, Q: Query<F>>(queries: I) -> Vec<CommitmentData<F, Q>>
where
    I: IntoIterator<Item = Q> + Clone,
{
    let mut commitment_map: Vec<CommitmentData<F, Q>> = vec![];

    for query in queries {
        if let Some(pos) = commitment_map
            .iter()
            .position(|commitment_data| commitment_data.point == query.get_point())
        {
            commitment_map[pos].queries.push(query)
        } else {
            commitment_map.push(CommitmentData {
                point: query.get_point(),
                queries: vec![query],
                _marker: PhantomData,
            });
        }
    }

    commitment_map
}
