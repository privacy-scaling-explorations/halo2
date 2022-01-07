//! This module contains an optimisation of the polynomial commitment opening
//! scheme described in the [Halo][halo] paper.
//!
//! [halo]: https://eprint.iacr.org/2019/1021

use std::collections::{BTreeMap, BTreeSet};

use super::*;
use crate::{
    arithmetic::{CurveAffine, FieldExt},
    transcript::ChallengeScalar,
};

mod prover;
mod verifier;

pub use prover::create_proof;
pub use verifier::verify_proof;

#[derive(Clone, Copy, Debug)]
struct U {}
type ChallengeU<F> = ChallengeScalar<F, U>;

#[derive(Clone, Copy, Debug)]
struct V {}
type ChallengeV<F> = ChallengeScalar<F, V>;

/// A polynomial query at a point
#[derive(Debug, Clone, Copy)]
pub struct ProverQuery<'a, C: CurveAffine> {
    /// point at which polynomial is queried
    pub point: C::Scalar,
    /// coefficients of polynomial
    pub poly: &'a Polynomial<C::Scalar, Coeff>,
}

/// A polynomial query at a point
#[derive(Debug, Clone, Copy)]
pub struct VerifierQuery<'r, C: CurveAffine> {
    /// point at which polynomial is queried
    point: C::Scalar,
    /// commitment to polynomial
    commitment: CommitmentReference<'r, C>,
    /// evaluation of polynomial at query point
    eval: C::Scalar,
}

impl<'r, 'params: 'r, C: CurveAffine> VerifierQuery<'r, C> {
    /// Create a new verifier query based on a commitment
    pub fn new_commitment(commitment: &'r C, point: C::Scalar, eval: C::Scalar) -> Self {
        VerifierQuery {
            point,
            eval,
            commitment: CommitmentReference::Commitment(commitment),
        }
    }

    /// Create a new verifier query based on a linear combination of commitments
    pub fn new_msm(msm: &'r MSM<C>, point: C::Scalar, eval: C::Scalar) -> Self {
        VerifierQuery {
            point,
            eval,
            commitment: CommitmentReference::MSM(msm),
        }
    }
}

#[derive(Copy, Clone, Debug)]
enum CommitmentReference<'r, C: CurveAffine> {
    Commitment(&'r C),
    MSM(&'r MSM<C>),
}

impl<'r, 'params: 'r, C: CurveAffine> PartialEq for CommitmentReference<'r, C> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (&CommitmentReference::Commitment(a), &CommitmentReference::Commitment(b)) => {
                std::ptr::eq(a, b)
            }
            (&CommitmentReference::MSM(a), &CommitmentReference::MSM(b)) => std::ptr::eq(a, b),
            _ => false,
        }
    }
}

// #[derive(Debug)]
// struct CommitmentData<F, T: PartialEq> {
//     commitment: T,
//     set_index: usize,
//     point_indices: Vec<usize>,
//     evals: Vec<F>,
// }

// impl<F, T: PartialEq> CommitmentData<F, T> {
//     fn new(commitment: T) -> Self {
//         CommitmentData {
//             commitment,
//             set_index: 0,
//             point_indices: vec![],
//             evals: vec![],
//         }
//     }
// }

// trait Query<F>: Sized {
//     type Commitment: PartialEq + Copy;
//     type Eval: Clone + Default;

//     fn get_point(&self) -> F;
//     fn get_eval(&self) -> Self::Eval;
//     fn get_commitment(&self) -> Self::Commitment;
// }

// type IntermediateSets<F, Q> = (
//     Vec<CommitmentData<<Q as Query<F>>::Eval, <Q as Query<F>>::Commitment>>,
//     Vec<Vec<F>>,
// );

// fn construct_intermediate_sets<F: FieldExt, I, Q: Query<F>>(queries: I) -> IntermediateSets<F, Q>
// where
//     I: IntoIterator<Item = Q> + Clone,
// {
//     // Construct sets of unique commitments and corresponding information about
//     // their queries.
//     let mut commitment_map: Vec<CommitmentData<Q::Eval, Q::Commitment>> = vec![];

//     // Also construct mapping from a unique point to a point_index. This defines
//     // an ordering on the points.
//     let mut point_index_map = BTreeMap::new();

//     // Iterate over all of the queries, computing the ordering of the points
//     // while also creating new commitment data.
//     for query in queries.clone() {
//         let num_points = point_index_map.len();
//         let point_idx = point_index_map
//             .entry(query.get_point())
//             .or_insert(num_points);

//         if let Some(pos) = commitment_map
//             .iter()
//             .position(|comm| comm.commitment == query.get_commitment())
//         {
//             commitment_map[pos].point_indices.push(*point_idx);
//         } else {
//             let mut tmp = CommitmentData::new(query.get_commitment());
//             tmp.point_indices.push(*point_idx);
//             commitment_map.push(tmp);
//         }
//     }

//     // Also construct inverse mapping from point_index to the point
//     let mut inverse_point_index_map = BTreeMap::new();
//     for (&point, &point_index) in point_index_map.iter() {
//         inverse_point_index_map.insert(point_index, point);
//     }

//     // Construct map of unique ordered point_idx_sets to their set_idx
//     let mut point_idx_sets = BTreeMap::new();
//     // Also construct mapping from commitment to point_idx_set
//     let mut commitment_set_map = Vec::new();

//     for commitment_data in commitment_map.iter() {
//         let mut point_index_set = BTreeSet::new();
//         // Note that point_index_set is ordered, unlike point_indices
//         for &point_index in commitment_data.point_indices.iter() {
//             point_index_set.insert(point_index);
//         }

//         // Push point_index_set to CommitmentData for the relevant commitment
//         commitment_set_map.push((commitment_data.commitment, point_index_set.clone()));

//         let num_sets = point_idx_sets.len();
//         point_idx_sets.entry(point_index_set).or_insert(num_sets);
//     }

//     // Initialise empty evals vec for each unique commitment
//     for commitment_data in commitment_map.iter_mut() {
//         let len = commitment_data.point_indices.len();
//         commitment_data.evals = vec![Q::Eval::default(); len];
//     }

//     // Populate set_index, evals and points for each commitment using point_idx_sets
//     for query in queries {
//         // The index of the point at which the commitment is queried
//         let point_index = point_index_map.get(&query.get_point()).unwrap();

//         // The point_index_set at which the commitment was queried
//         let mut point_index_set = BTreeSet::new();
//         for (commitment, point_idx_set) in commitment_set_map.iter() {
//             if query.get_commitment() == *commitment {
//                 point_index_set = point_idx_set.clone();
//             }
//         }
//         assert!(!point_index_set.is_empty());

//         // The set_index of the point_index_set
//         let set_index = point_idx_sets.get(&point_index_set).unwrap();
//         for commitment_data in commitment_map.iter_mut() {
//             if query.get_commitment() == commitment_data.commitment {
//                 commitment_data.set_index = *set_index;
//             }
//         }
//         let point_index_set: Vec<usize> = point_index_set.iter().cloned().collect();

//         // The offset of the point_index in the point_index_set
//         let point_index_in_set = point_index_set
//             .iter()
//             .position(|i| i == point_index)
//             .unwrap();

//         for commitment_data in commitment_map.iter_mut() {
//             if query.get_commitment() == commitment_data.commitment {
//                 // Insert the eval using the ordering of the point_index_set
//                 commitment_data.evals[point_index_in_set] = query.get_eval();
//             }
//         }
//     }

//     // Get actual points in each point set
//     let mut point_sets: Vec<Vec<F>> = vec![Vec::new(); point_idx_sets.len()];
//     for (point_idx_set, &set_idx) in point_idx_sets.iter() {
//         for &point_idx in point_idx_set.iter() {
//             let point = inverse_point_index_map.get(&point_idx).unwrap();
//             point_sets[set_idx].push(*point);
//         }
//     }

//     (commitment_map, point_sets)
// }

struct CommitmentData<F, Q: Query<F>> {
    queries: Vec<Q>,
    point: Q::Scalar,
    _marker: PhantomData<F>,
}

trait Query<F>: Sized + Copy {
    type Commitment: PartialEq + Copy;
    type Scalar: Clone + Default + Ord + Copy;

    fn get_point(&self) -> Self::Scalar;
    fn get_eval(&self) -> Self::Scalar;
    fn get_commitment(&self) -> Self::Commitment;
}

fn construct_intermediate_sets<F: FieldExt, I, Q: Query<F>>(queries: I) -> Vec<CommitmentData<F, Q>>
where
    I: IntoIterator<Item = Q> + Clone,
{
    let mut point_query_map: BTreeMap<Q::Scalar, Vec<Q>> = BTreeMap::new();
    for query in queries.clone() {
        if let Some(queries) = point_query_map.get_mut(&query.get_point()) {
            queries.push(query);
        } else {
            point_query_map.insert(query.get_point(), vec![query]);
        }
    }

    point_query_map
        .keys()
        .map(|point| {
            let queries = point_query_map.get(point).unwrap();
            CommitmentData {
                queries: queries.clone(),
                point: *point,
                _marker: PhantomData,
            }
        })
        .collect()
}

// #[cfg(test)]
// mod tests {
//     use super::{construct_intermediate_sets, Query};
//     use crate::arithmetic::FieldExt;
//     use pairing::bn256::Fr as Fp;

//     #[derive(Clone)]
//     struct MyQuery<F> {
//         commitment: usize,
//         point: F,
//         eval: F,
//     }

//     impl<F: Clone + Default> Query<F> for MyQuery<F> {
//         type Commitment = usize;
//         type Eval = F;

//         fn get_point(&self) -> F {
//             self.point.clone()
//         }
//         fn get_eval(&self) -> Self::Eval {
//             self.eval.clone()
//         }
//         fn get_commitment(&self) -> Self::Commitment {
//             self.commitment
//         }
//     }
// }

// #[cfg(test)]
// mod proptests {
//     use proptest::{
//         collection::vec,
//         prelude::*,
//         sample::{select, subsequence},
//         strategy::Strategy,
//     };

//     use super::construct_intermediate_sets;
//     use crate::poly::Rotation;
//     use pairing::{
//         arithmetic::{BaseExt, FieldExt},
//         bn256::Fr as Fp,
//     };

//     use std::collections::BTreeMap;
//     use std::convert::TryFrom;

//     #[derive(Debug, Clone)]
//     struct MyQuery<F> {
//         point: F,
//         eval: F,
//         commitment: usize,
//     }

//     impl super::Query<Fp> for MyQuery<Fp> {
//         type Commitment = usize;
//         type Eval = Fp;

//         fn get_point(&self) -> Fp {
//             self.point
//         }

//         fn get_eval(&self) -> Self::Eval {
//             self.eval
//         }

//         fn get_commitment(&self) -> Self::Commitment {
//             self.commitment
//         }
//     }

//     prop_compose! {
//         fn arb_point()(
//             bytes in vec(any::<u8>(), 64)
//         ) -> Fp {
//             Fp::from_bytes_wide(&<[u8; 64]>::try_from(bytes).unwrap())
//         }
//     }

//     prop_compose! {
//         fn arb_query(commitment: usize, point: Fp)(
//             eval in arb_point()
//         ) -> MyQuery<Fp> {
//             MyQuery {
//                 point,
//                 eval,
//                 commitment
//             }
//         }
//     }

//     prop_compose! {
//         // Mapping from column index to point index.
//         fn arb_queries_inner(num_points: usize, num_cols: usize, num_queries: usize)(
//             col_indices in vec(select((0..num_cols).collect::<Vec<_>>()), num_queries),
//             point_indices in vec(select((0..num_points).collect::<Vec<_>>()), num_queries)
//         ) -> Vec<(usize, usize)> {
//             col_indices.into_iter().zip(point_indices.into_iter()).collect()
//         }
//     }

//     prop_compose! {
//         fn compare_queries(
//             num_points: usize,
//             num_cols: usize,
//             num_queries: usize,
//         )(
//             points_1 in vec(arb_point(), num_points),
//             points_2 in vec(arb_point(), num_points),
//             mapping in arb_queries_inner(num_points, num_cols, num_queries)
//         )(
//             queries_1 in mapping.iter().map(|(commitment, point_idx)| arb_query(*commitment, points_1[*point_idx])).collect::<Vec<_>>(),
//             queries_2 in mapping.iter().map(|(commitment, point_idx)| arb_query(*commitment, points_2[*point_idx])).collect::<Vec<_>>(),
//         ) -> (
//             Vec<MyQuery<Fp>>,
//             Vec<MyQuery<Fp>>
//         ) {
//             (
//                 queries_1,
//                 queries_2,
//             )
//         }
//     }

//     proptest! {
//         #[test]
//         fn test_intermediate_sets(
//             (queries_1, queries_2) in compare_queries(8, 8, 16)
//         ) {
//             let (commitment_data, _point_sets) = construct_intermediate_sets(queries_1);
//             let set_indices = commitment_data.iter().map(|data| data.set_index).collect::<Vec<_>>();
//             let point_indices = commitment_data.iter().map(|data| data.point_indices.clone()).collect::<Vec<_>>();

//             // It shouldn't matter what the point or eval values are; we should get
//             // the same exact point set indices and point indices again.
//             let (new_commitment_data, _new_point_sets) = construct_intermediate_sets(queries_2);
//             let new_set_indices = new_commitment_data.iter().map(|data| data.set_index).collect::<Vec<_>>();
//             let new_point_indices = new_commitment_data.iter().map(|data| data.point_indices.clone()).collect::<Vec<_>>();

//             assert_eq!(set_indices, new_set_indices);
//             assert_eq!(point_indices, new_point_indices);
//         }
//     }
// }

#[test]
fn test_multiopen() {
    use crate::poly::commitment::Setup;
    use crate::transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, Transcript, TranscriptRead, TranscriptWrite,
    };
    use crate::{arithmetic::eval_polynomial, transcript::ChallengeScalar};
    use pairing::bn256::Bn256;
    use pairing::bn256::Fr;
    use pairing::bn256::G1Affine;
    use rand::RngCore;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    #[derive(Clone, Copy, Debug)]
    struct Z {}
    /// Challenge for keeping the multi-point quotient polynomial terms linearly independent.
    type ChallengeZ<F> = ChallengeScalar<F, Z>;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    fn rand_poly(n: usize, mut rng: impl RngCore) -> Polynomial<Fr, Coeff> {
        Polynomial {
            values: (0..n).into_iter().map(|_| Fr::random(&mut rng)).collect(),
            _marker: PhantomData,
        }
    }

    let k = 3;

    let params = Setup::<Bn256>::new(k, &mut rng);
    let params_verifier = Setup::<Bn256>::verifier_params(&params, 0).unwrap();

    // prover

    let p1_x = rand_poly(params.n as usize, &mut rng);
    let p2_x = rand_poly(params.n as usize, &mut rng);
    let p3_x = rand_poly(params.n as usize, &mut rng);
    let p4_x = rand_poly(params.n as usize, &mut rng);

    let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);
    let p1 = params.commit(&p1_x).into();
    transcript.write_point(p1).unwrap();
    let p2 = params.commit(&p2_x).into();
    transcript.write_point(p2).unwrap();
    let p3 = params.commit(&p3_x).into();
    transcript.write_point(p3).unwrap();
    let p4 = params.commit(&p4_x).into();
    transcript.write_point(p4).unwrap();

    let z0: ChallengeZ<_> = transcript.squeeze_challenge_scalar();
    let z1: ChallengeZ<_> = transcript.squeeze_challenge_scalar();

    let e01 = eval_polynomial(&p1_x, *z0);
    transcript.write_scalar(e01).unwrap();
    let e02 = eval_polynomial(&p2_x, *z0);
    transcript.write_scalar(e02).unwrap();
    let e03 = eval_polynomial(&p3_x, *z0);
    transcript.write_scalar(e03).unwrap();
    let e04 = eval_polynomial(&p4_x, *z0);
    transcript.write_scalar(e04).unwrap();

    let e13 = eval_polynomial(&p3_x, *z1);
    transcript.write_scalar(e13).unwrap();
    let e14 = eval_polynomial(&p4_x, *z1);
    transcript.write_scalar(e14).unwrap();

    let q0 = ProverQuery {
        poly: &p1_x,
        point: *z0,
    };
    let q1 = ProverQuery {
        poly: &p2_x,
        point: *z0,
    };
    let q2 = ProverQuery {
        poly: &p3_x,
        point: *z0,
    };
    let q3 = ProverQuery {
        poly: &p4_x,
        point: *z0,
    };
    let q4 = ProverQuery {
        poly: &p3_x,
        point: *z1,
    };
    let q5 = ProverQuery {
        poly: &p4_x,
        point: *z1,
    };

    let queries: Vec<ProverQuery<G1Affine>> = vec![q0, q1, q2, q3, q4, q5];
    create_proof(&params, &mut transcript, queries).unwrap();
    let proof = transcript.finalize();

    // verifier

    let mut transcript = Blake2bRead::<_, G1Affine, Challenge255<_>>::init(&proof[..]);
    let p1 = &transcript.read_point().unwrap();
    let p2 = &transcript.read_point().unwrap();
    let p3 = &transcript.read_point().unwrap();
    let p4 = &transcript.read_point().unwrap();

    let z0: ChallengeZ<_> = transcript.squeeze_challenge_scalar();
    let z1: ChallengeZ<_> = transcript.squeeze_challenge_scalar();

    let e01 = transcript.read_scalar().unwrap();
    let e02 = transcript.read_scalar().unwrap();
    let e03 = transcript.read_scalar().unwrap();
    let e04 = transcript.read_scalar().unwrap();
    let e13 = transcript.read_scalar().unwrap();
    let e14 = transcript.read_scalar().unwrap();

    let q0 = VerifierQuery::new_commitment(p1, *z0, e01);
    let q1 = VerifierQuery::new_commitment(p2, *z0, e02);
    let q2 = VerifierQuery::new_commitment(p3, *z0, e03);
    let q3 = VerifierQuery::new_commitment(p4, *z0, e04);
    let q4 = VerifierQuery::new_commitment(p3, *z1, e13);
    let q5 = VerifierQuery::new_commitment(p4, *z1, e14);

    let queries: Vec<VerifierQuery<G1Affine>> = vec![q0, q1, q2, q3, q4, q5];
    assert!(bool::from(
        verify_proof(&params_verifier, &mut transcript, queries).unwrap()
    ));
}
