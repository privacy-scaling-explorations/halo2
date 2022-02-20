mod prover;
mod verifier;

use super::Query;
use crate::{
    arithmetic::{eval_polynomial, lagrange_interpolate, CurveAffine, FieldExt},
    poly::{msm::MSM, Coeff, Polynomial},
    transcript::ChallengeScalar,
};

use std::{
    collections::{btree_map::Entry, BTreeMap, BTreeSet},
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

#[derive(Clone, Copy, Debug)]
struct Y {}
type ChallengeY<F> = ChallengeScalar<F, Y>;

#[derive(Clone)]
struct Commitment<F: FieldExt, T: PartialEq + Clone>((T, Vec<F>));

impl<F: FieldExt, T: PartialEq + Clone> Commitment<F, T> {
    fn get(&self) -> T {
        self.0 .0.clone()
    }

    fn evals(&self) -> Vec<F> {
        self.0 .1.clone()
    }
}

#[derive(Clone)]
struct RotationSet<F: FieldExt, T: PartialEq + Clone> {
    commitments: Vec<Commitment<F, T>>,
    point_indices: Vec<usize>,
}

impl<F: FieldExt, T: PartialEq + Clone> RotationSet<F, T> {
    fn points(&self, super_point_set: &[F]) -> Vec<F> {
        self.point_indices
            .iter()
            .map(|idx| super_point_set[*idx])
            .collect()
    }

    fn diffs(&self, super_point_set: &[F]) -> Vec<F> {
        super_point_set
            .iter()
            .enumerate()
            .filter(|(idx, _)| !self.point_indices.contains(idx))
            .map(|(_, point)| *point)
            .collect()
    }
}

struct IntermediateSets<F: FieldExt, Q: Query<F>> {
    rotation_sets: Vec<RotationSet<F, Q::Commitment>>,
    super_point_set: Vec<F>,
}

fn construct_intermediate_sets<F: FieldExt, I, Q: Query<F>>(queries: I) -> IntermediateSets<F, Q>
where
    I: IntoIterator<Item = Q> + Clone,
{
    // Construct sets of unique commitments and corresponding queried points.
    let mut commitment_map: Vec<(Q::Commitment, Vec<usize>)> = vec![];

    // Also construct mapping from a unique point to a point_index. This defines
    // an ordering on the points.
    let mut point_index_map = BTreeMap::new();

    // Collect all different points as a super set.
    let mut super_point_set = vec![];

    // Iterate over all of the queries, computing the ordering of the points
    // while also creating new commitment data.
    for query in queries.clone() {
        let num_points = point_index_map.len();
        let point_index = match point_index_map.entry(query.get_point()) {
            Entry::Occupied(entry) => *entry.get(),
            Entry::Vacant(entry) => {
                super_point_set.push(*entry.key());
                *entry.insert(num_points)
            }
        };

        if let Some(pos) = commitment_map
            .iter()
            .position(|(commitment, _)| *commitment == query.get_commitment())
        {
            let (_, point_indices) = &mut commitment_map[pos];
            if !point_indices.iter().any(|idx| *idx == point_index) {
                point_indices.push(point_index);
            }
        } else {
            commitment_map.push((query.get_commitment(), vec![point_index]));
        };
    }

    // Construct rotation set
    let mut rotation_sets = vec![];
    // Also construct mapping from commitment to index of rotation_sets
    let commitment_set_idx_map = {
        // Construct map of unique ordered point_indices_sets to their set_index
        let mut point_indices_sets = BTreeMap::new();

        commitment_map
            .into_iter()
            .map(|(commitment, point_indices)| {
                let num_points = point_indices.len();
                let point_index_set = point_indices.iter().cloned().collect::<BTreeSet<_>>();
                debug_assert!(num_points == point_index_set.len());

                let num_sets = point_indices_sets.len();
                let set_index = match point_indices_sets.entry(point_index_set) {
                    Entry::Vacant(entry) => {
                        rotation_sets.push(RotationSet {
                            commitments: vec![],
                            point_indices,
                        });
                        *entry.insert(num_sets)
                    }
                    Entry::Occupied(entry) => *entry.get(),
                };

                let commitment_index = rotation_sets[set_index].commitments.len();
                rotation_sets[set_index].commitments.push(Commitment((
                    commitment.clone(),
                    vec![F::zero(); num_points],
                )));

                (commitment, set_index, commitment_index)
            })
            .collect::<Vec<_>>()
    };

    // Populate evals for each commitment in each rotation_set
    for query in queries {
        // The index of the point at which the commitment is queried
        let point_index = point_index_map.get(&query.get_point()).unwrap();

        let (_, set_index, commitment_index) = commitment_set_idx_map
            .iter()
            .find(|(commitment, _, _)| query.get_commitment() == *commitment)
            .unwrap();

        let rotation_set = &mut rotation_sets[*set_index];
        let Commitment((_, evals)) = &mut rotation_set.commitments[*commitment_index];

        let point_index_in_set = rotation_set
            .point_indices
            .iter()
            .position(|i| i == point_index)
            .unwrap();
        evals[point_index_in_set] = query.get_eval();
    }

    IntermediateSets {
        rotation_sets,
        super_point_set,
    }
}

#[cfg(test)]
mod tests {
    use super::{construct_intermediate_sets, IntermediateSets};
    use crate::arithmetic::{eval_polynomial, FieldExt};
    use crate::pairing::bn256::{Bn256, Fr, G1Affine};
    use crate::poly::{
        commitment::{Params, ParamsVerifier},
        multiopen::{create_proof, verify_proof},
        multiopen::{ProverQuery, Query, VerifierQuery},
        Coeff, Polynomial,
    };
    use crate::transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, ChallengeScalar, Transcript, TranscriptRead,
        TranscriptWrite,
    };

    use ff::Field;
    use rand::RngCore;
    use rand_core::OsRng;
    use std::collections::BTreeSet;
    use std::marker::PhantomData;

    #[derive(Clone)]
    pub(super) struct MyQuery<F> {
        commitment: usize,
        point: F,
        eval: F,
    }

    impl<F: FieldExt> Query<F> for MyQuery<F> {
        type Commitment = usize;

        fn get_point(&self) -> F {
            self.point
        }
        fn get_eval(&self) -> F {
            self.eval
        }
        fn get_commitment(&self) -> Self::Commitment {
            self.commitment
        }
    }

    fn rotation_set(points: Vec<u64>) -> Vec<Fr> {
        points.into_iter().map(Fr::from).collect()
    }

    fn make_query(commitment: usize, point: Fr) -> MyQuery<Fr> {
        MyQuery {
            commitment,
            point,
            eval: point + Fr::from(commitment as u64),
        }
    }

    #[test]
    fn test_intermediate_sets() {
        fn vec_to_set<T: Ord>(v: Vec<T>) -> BTreeSet<T> {
            let mut set = BTreeSet::new();
            for el in v {
                set.insert(el);
            }
            set
        }

        let rotation_sets_init = vec![vec![1u64, 2, 3], vec![2, 3, 4], vec![4, 5, 6, 7], vec![8]];
        let number_of_sets = rotation_sets_init.len();
        let rotation_sets: Vec<Vec<Fr>> = rotation_sets_init
            .clone()
            .into_iter()
            .map(rotation_set)
            .collect();
        let mut super_point_set: Vec<Fr> = rotation_sets.clone().into_iter().flatten().collect();
        super_point_set.sort();
        super_point_set.dedup();

        let commitment_per_set = 3;
        let number_of_commitments = commitment_per_set * rotation_sets.len();

        let mut queries: Vec<MyQuery<Fr>> = vec![];

        for i in 0..number_of_commitments {
            let rotation_set = &rotation_sets[i % rotation_sets.len()];
            for point in rotation_set.iter() {
                let query = make_query(i, *point);
                queries.push(query);
            }
        }

        let intermediate_sets = construct_intermediate_sets(queries);
        assert_eq!(intermediate_sets.rotation_sets.len(), rotation_sets.len());
        assert_eq!(intermediate_sets.super_point_set, super_point_set);

        let IntermediateSets {
            rotation_sets,
            super_point_set,
        } = intermediate_sets;

        for (i, rotation_set) in rotation_sets.iter().enumerate() {
            let commitments = rotation_set.commitments.clone();
            assert_eq!(commitments.len(), commitment_per_set);
            for (j, commitment) in commitments.iter().enumerate() {
                let commitment_id: usize = commitment.get();
                assert_eq!(commitment_id, number_of_sets * j + i);
            }

            let points: Vec<Fr> = rotation_set.points(&super_point_set);
            let diffs: Vec<Fr> = rotation_set.diffs(&super_point_set);

            assert_eq!(points.len(), rotation_sets_init[i].len());

            let points = vec_to_set(points);
            let diffs = vec_to_set(diffs);
            assert_eq!(points.intersection(&diffs).cloned().count(), 0);
            let union: Vec<Fr> = points.union(&diffs).cloned().collect();
            assert_eq!(union, super_point_set);
        }
    }
}
