//! This module contains an optimisation of the polynomial commitment opening
//! scheme described in the [Halo][halo] paper.
//!
//! [halo]: https://eprint.iacr.org/2019/1021

use std::collections::{BTreeMap, BTreeSet};

use super::*;
use crate::{
    arithmetic::{lagrange_interpolate, CurveAffine, FieldExt},
    poly::commitment::Setup,
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

#[derive(Debug)]
struct CommitmentData<F, T: PartialEq> {
    commitment: T,
    points: Vec<(F, F)>,
    diffs: Vec<F>,
}

trait Query<F>: Sized {
    type Commitment: PartialEq + Copy;

    fn get_point(&self) -> F;
    fn get_eval(&self) -> F;
    fn get_commitment(&self) -> Self::Commitment;
}

type IntermediateSets<F, Q> = (Vec<CommitmentData<F, <Q as Query<F>>::Commitment>>, Vec<F>);

fn construct_intermediate_sets<F: FieldExt, I, Q: Query<F>>(queries: I) -> IntermediateSets<F, Q>
where
    I: IntoIterator<Item = Q> + Clone,
{
    // 1. all points
    let mut point_set = BTreeSet::new();
    for query in queries.clone() {
        point_set.insert(query.get_point());
    }

    // 2. id commitments
    let mut commitment_ids = vec![];
    let mut id = 1usize;
    for query in queries.clone() {
        let mut found = false;
        for (_, commitment) in commitment_ids.iter() {
            if *commitment == query.get_commitment() {
                found = true;
            }
        }
        if !found {
            commitment_ids.push((id, query.get_commitment()));
            id += 1;
        }
    }

    // 3. map points to commitments
    let mut commitment_point_map = BTreeMap::new();

    let mut query_map = BTreeMap::new();
    for query in queries.clone() {
        let mut id = 0usize;
        for (_id, commitment) in commitment_ids.iter() {
            if query.get_commitment() == *commitment {
                id = *_id;
            }

            // TODO: there won't be any duplicates but best to skip if id is processed
            commitment_point_map.entry(id).or_insert_with(BTreeSet::new);
            let point_map = commitment_point_map.get_mut(&id).unwrap();
            point_map.insert(query.get_point());

            query_map.entry(id).or_insert_with(BTreeSet::new);
            let entry = query_map.get_mut(&id).unwrap();
            entry.insert((query.get_point(), query.get_eval()));
        }
    }

    // 4. find diff points
    let mut diff_point_map: BTreeMap<usize, Vec<F>> = BTreeMap::new();

    for query in queries.clone() {
        let mut id = 0usize;
        for (_id, commitment) in commitment_ids.iter() {
            if query.get_commitment() == *commitment {
                id = *_id;
            }

            // TODO: there won't be any duplicates but best to skip if id is processed
            let point_map = commitment_point_map.get(&id).unwrap();
            diff_point_map
                .entry(id)
                .or_insert_with(|| point_set.difference(point_map).cloned().collect());
        }
    }

    let commitment_data = commitment_ids
        .into_iter()
        .map(|(id, commitment)| {
            let query_set = query_map.get(&id).unwrap();
            let points: Vec<(F, F)> = query_set.iter().cloned().collect();
            let diffs = diff_point_map.get(&id).unwrap().clone();

            CommitmentData {
                commitment,
                points,
                diffs: (*diffs).to_vec(),
            }
        })
        .collect();

    let all_points = point_set.iter().cloned().collect();

    (commitment_data, all_points)
}

#[cfg(test)]
mod tests {
    use std::{
        collections::{BTreeMap, BTreeSet},
        iter::FromIterator,
    };

    use super::{construct_intermediate_sets, Query};
    use crate::arithmetic::FieldExt;
    use pairing::bn256::Fr as Fp;

    #[derive(Clone)]
    struct MyQuery<F> {
        commitment: usize,
        point: F,
        eval: F,
    }

    impl<F: Clone + Default> Query<F> for MyQuery<F> {
        type Commitment = usize;

        fn get_point(&self) -> F {
            self.point.clone()
        }
        fn get_eval(&self) -> F {
            self.eval.clone()
        }
        fn get_commitment(&self) -> Self::Commitment {
            self.commitment
        }
    }

    #[test]
    fn test_intermediate_sets() {
        fn make_query(commitment: usize, point: Fp) -> MyQuery<Fp> {
            MyQuery {
                commitment,
                point,
                eval: point + Fp::one(),
            }
        }

        let points_0: Vec<Fp> = vec![0x10, 0x20, 0x30].into_iter().map(Fp::from).collect();
        let points_1: Vec<Fp> = vec![0x30, 0x40, 0x50].into_iter().map(Fp::from).collect();
        let points_2: Vec<Fp> = vec![0x40, 0x50, 0x60, 0x70, 0x80]
            .into_iter()
            .map(Fp::from)
            .collect();

        let points = vec![points_0, points_1, points_2];
        let queries: Vec<Vec<MyQuery<Fp>>> = points
            .iter()
            .enumerate()
            .map(|(i, points)| points.iter().map(|point| make_query(i, *point)).collect())
            .collect();

        let mut all_queries: Vec<MyQuery<Fp>> = vec![];
        for query_vec in queries.clone().into_iter() {
            all_queries.extend(query_vec);
        }

        let (commitment_data, all_points) = construct_intermediate_sets(all_queries.clone());

        // for c in commitment_data {
        //     println!("{:?}", c.commitment);
        //     for (point, eval) in c.points {
        //         println!("point {:?}", point);
        //         println!("eval {:?}", eval);
        //     }
        //     for dif in c.diffs {
        //         println!("dif {:?}", dif);
        //     }
        // }

        assert_eq!(commitment_data.len(), queries.len());

        let all_points_set = BTreeSet::from_iter(all_points);
        for query in all_queries.iter() {
            assert!(all_points_set.contains(&query.point));
        }

        for (i, (commitment_data, queries)) in
            commitment_data.into_iter().zip(queries.iter()).enumerate()
        {
            assert_eq!(commitment_data.commitment, i);
            let points = commitment_data.points;
            assert_eq!(points.len(), queries.len());

            let points = BTreeMap::from_iter(points);
            for query in queries {
                let eval = points.get(&query.point).unwrap();
                assert_eq!(*eval, query.eval);
            }
        }
    }
}

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

    let points_0: Vec<Fr> = vec![0x10, 0x20, 0x30].into_iter().map(Fr::from).collect();
    let points_1: Vec<Fr> = vec![0x20, 0x30, 0x40].into_iter().map(Fr::from).collect();
    let points_2: Vec<Fr> = vec![0x40, 0x50, 0x60, 0x70]
        .into_iter()
        .map(Fr::from)
        .collect();

    // prover

    let p0_x = rand_poly(params.n as usize, &mut rng);
    let p1_x = rand_poly(params.n as usize, &mut rng);
    let p2_x = rand_poly(params.n as usize, &mut rng);

    let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);
    let p0 = &params.commit(&p0_x).into();
    let p1 = &params.commit(&p1_x).into();
    let p2 = &params.commit(&p2_x).into();

    let (queries_0, evals_0): (Vec<ProverQuery<G1Affine>>, Vec<Fr>) = points_0
        .iter()
        .map(|point| {
            let e = eval_polynomial(&p0_x, *point);
            (
                ProverQuery {
                    poly: &p0_x,
                    point: *point,
                },
                e,
            )
        })
        .unzip();

    let (queries_1, evals_1): (Vec<ProverQuery<G1Affine>>, Vec<Fr>) = points_1
        .iter()
        .map(|point| {
            let e = eval_polynomial(&p1_x, *point);
            (
                ProverQuery {
                    poly: &p1_x,
                    point: *point,
                },
                e,
            )
        })
        .unzip();

    let (queries_2, evals_2): (Vec<ProverQuery<G1Affine>>, Vec<Fr>) = points_2
        .iter()
        .map(|point| {
            let e = eval_polynomial(&p2_x, *point);
            (
                ProverQuery {
                    poly: &p2_x,
                    point: *point,
                },
                e,
            )
        })
        .unzip();

    let mut queries: Vec<ProverQuery<G1Affine>> = vec![];
    queries.extend(queries_0.iter());
    queries.extend(queries_1.iter());
    queries.extend(queries_2.iter());

    create_proof(&params, &mut transcript, queries).unwrap();
    let proof = transcript.finalize();

    // verifier

    let mut transcript = Blake2bRead::<_, G1Affine, Challenge255<_>>::init(&proof[..]);

    let queries_0: Vec<VerifierQuery<G1Affine>> = points_0
        .iter()
        .zip(evals_0.iter())
        .map(|(point, eval)| VerifierQuery::new_commitment(p0, *point, *eval))
        .collect();

    let queries_1: Vec<VerifierQuery<G1Affine>> = points_1
        .iter()
        .zip(evals_1.iter())
        .map(|(point, eval)| VerifierQuery::new_commitment(p1, *point, *eval))
        .collect();

    let queries_2: Vec<VerifierQuery<G1Affine>> = points_2
        .iter()
        .zip(evals_2.iter())
        .map(|(point, eval)| VerifierQuery::new_commitment(p2, *point, *eval))
        .collect();

    let mut queries: Vec<VerifierQuery<G1Affine>> = vec![];
    queries.extend(queries_0.iter());
    queries.extend(queries_1.iter());
    queries.extend(queries_2.iter());

    assert!(bool::from(
        verify_proof(&params_verifier, &mut transcript, queries).unwrap()
    ));
}
