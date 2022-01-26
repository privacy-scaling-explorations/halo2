//! This module contains an optimisation of the polynomial commitment opening
//! scheme described in the [Halo][halo] paper.
//!
//! [halo]: https://eprint.iacr.org/2019/1021

use std::collections::BTreeMap;

use super::*;
use crate::{
    arithmetic::{CurveAffine, FieldExt},
    transcript::ChallengeScalar,
};

mod prover;
mod verifier;

pub use prover::create_proof;
pub use verifier::verify_proof;
use crate::plonk::create_domain;

use super::msm::MSM;

#[derive(Clone, Copy, Debug)]
struct U {}
type ChallengeU<F> = ChallengeScalar<F, U>;

#[derive(Clone, Copy, Debug)]
struct V {}
type ChallengeV<F> = ChallengeScalar<F, V>;

/// A polynomial query at a point
#[derive(Debug, Clone, Copy)]
pub struct ProverQuery<'a, C: CurveAffine> {
    /// rotation at which polynomial is queried
    pub rot: Rotation,
    /// coefficients of polynomial
    pub poly: &'a Polynomial<C::Scalar, Coeff>,
}

/// A polynomial query at a point
#[derive(Debug, Clone, Copy)]
pub struct VerifierQuery<'r, C: CurveAffine> {
    /// rotation at which polynomial is queried
    rot: Rotation,
    /// commitment to polynomial
    commitment: CommitmentReference<'r, C>,
    /// evaluation of polynomial at query point
    eval: C::Scalar,
}

impl<'r, 'params: 'r, C: CurveAffine> VerifierQuery<'r, C> {
    /// Create a new verifier query based on a commitment
    pub fn new_commitment(commitment: &'r C, rot: Rotation, eval: C::Scalar) -> Self {
        VerifierQuery {
            rot,
            eval,
            commitment: CommitmentReference::Commitment(commitment),
        }
    }

    /// Create a new verifier query based on a linear combination of commitments
    pub fn new_msm(msm: &'r MSM<C>, rot: Rotation, eval: C::Scalar) -> Self {
        VerifierQuery {
            rot,
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

struct CommitmentData<F, Q: Query<F>> {
    queries: Vec<Q>,
    rot: Rotation,
    _marker: PhantomData<F>,
}

trait Query<F>: Sized + Copy {
    type Commitment: PartialEq + Copy;
    type Scalar: Clone + Default + Ord + Copy;

    fn get_rot(&self) -> Rotation;
    fn get_eval(&self, point: Self::Scalar) -> Self::Scalar;
    fn get_commitment(&self) -> Self::Commitment;
}

fn construct_intermediate_sets<F: FieldExt, I, Q: Query<F>>(queries: I) -> Vec<CommitmentData<F, Q>>
where
    I: IntoIterator<Item = Q> + Clone,
{
    let mut point_query_map: BTreeMap<Rotation, Vec<Q>> = BTreeMap::new();
    for query in queries.clone() {
        if let Some(queries) = point_query_map.get_mut(&query.get_rot()) {
            queries.push(query);
        } else {
            point_query_map.insert(query.get_rot(), vec![query]);
        }
    }

    point_query_map
        .keys()
        .map(|rot| {
            let queries = point_query_map.get(rot).unwrap();
            CommitmentData {
                queries: queries.clone(),
                rot: rot.clone(),
                _marker: PhantomData,
            }
        })
        .collect()
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
    let domain = EvaluationDomain::new(2, params.k);
    let z1 = domain.rotate_omega(z0.deref().clone(), Rotation::next());

    let e01 = eval_polynomial(&p1_x, *z0);
    transcript.write_scalar(e01).unwrap();
    let e02 = eval_polynomial(&p2_x, *z0);
    transcript.write_scalar(e02).unwrap();
    let e03 = eval_polynomial(&p3_x, *z0);
    transcript.write_scalar(e03).unwrap();
    let e04 = eval_polynomial(&p4_x, *z0);
    transcript.write_scalar(e04).unwrap();

    let e13 = eval_polynomial::<Fr>(&p3_x, z1);
    transcript.write_scalar(e13).unwrap();
    let e14 = eval_polynomial::<Fr>(&p4_x, z1);
    transcript.write_scalar(e14).unwrap();

    let q0 = ProverQuery {
        poly: &p1_x,
        rot: Rotation::cur(),
    };
    let q1 = ProverQuery {
        poly: &p2_x,
        rot: Rotation::cur(),
    };
    let q2 = ProverQuery {
        poly: &p3_x,
        rot: Rotation::cur(),
    };
    let q3 = ProverQuery {
        poly: &p4_x,
        rot: Rotation::cur(),
    };
    let q4 = ProverQuery {
        poly: &p3_x,
        rot: Rotation::next(),
    };
    let q5 = ProverQuery {
        poly: &p4_x,
        rot: Rotation::next(),
    };

    let queries: Vec<ProverQuery<G1Affine>> = vec![q0, q1, q2, q3, q4, q5];
    create_proof(&params, &domain, z0.deref().clone(), &mut transcript, queries).unwrap();
    let proof = transcript.finalize();

    // verifier

    let mut transcript = Blake2bRead::<_, G1Affine, Challenge255<_>>::init(&proof[..]);
    let p1 = &transcript.read_point().unwrap();
    let p2 = &transcript.read_point().unwrap();
    let p3 = &transcript.read_point().unwrap();
    let p4 = &transcript.read_point().unwrap();

    let z0: ChallengeZ<_> = transcript.squeeze_challenge_scalar();
    let r0 = Rotation::cur();
    let r1 = Rotation::next();

    let e01 = transcript.read_scalar().unwrap();
    let e02 = transcript.read_scalar().unwrap();
    let e03 = transcript.read_scalar().unwrap();
    let e04 = transcript.read_scalar().unwrap();
    let e13 = transcript.read_scalar().unwrap();
    let e14 = transcript.read_scalar().unwrap();

    let q0 = VerifierQuery::new_commitment(p1, r0, e01);
    let q1 = VerifierQuery::new_commitment(p2, r0, e02);
    let q2 = VerifierQuery::new_commitment(p3, r0, e03);
    let q3 = VerifierQuery::new_commitment(p4, r0, e04);
    let q4 = VerifierQuery::new_commitment(p3, r1, e13);
    let q5 = VerifierQuery::new_commitment(p4, r1, e14);

    let queries: Vec<VerifierQuery<G1Affine>> = vec![q0, q1, q2, q3, q4, q5];
    assert!(bool::from(
        verify_proof(&params_verifier, &domain, z0.deref().clone(), &mut transcript, queries).unwrap()
    ));
}
