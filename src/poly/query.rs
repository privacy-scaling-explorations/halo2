use ff::PrimeField;
use std::fmt::Debug;

use crate::poly::commitment::PolynomialCommitmentScheme;
use crate::{
    poly::{Coeff, Polynomial},
    utils::arithmetic::eval_polynomial,
};

pub trait Query<F>: Sized + Clone + Send + Sync {
    type Commitment: PartialEq + Copy + Send + Sync;
    type Eval: Clone + Default + Debug;

    fn get_point(&self) -> F;
    fn get_eval(&self) -> Self::Eval;
    fn get_commitment(&self) -> Self::Commitment;
}

/// A polynomial query at a point
#[derive(Debug, Clone, Copy)]
pub struct ProverQuery<'com, F: PrimeField> {
    /// Point at which polynomial is queried
    pub(crate) point: F,
    /// Coefficients of polynomial
    pub(crate) poly: &'com Polynomial<F, Coeff>,
}

impl<'com, F> ProverQuery<'com, F>
where
    F: PrimeField,
{
    /// Create a new prover query based on a polynomial
    pub fn new(point: F, poly: &'com Polynomial<F, Coeff>) -> Self {
        ProverQuery { point, poly }
    }
}

#[doc(hidden)]
#[derive(Copy, Clone)]
pub struct PolynomialPointer<'com, F: PrimeField> {
    pub(crate) poly: &'com Polynomial<F, Coeff>,
}

impl<'com, F: PrimeField> PartialEq for PolynomialPointer<'com, F> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.poly, other.poly)
    }
}

impl<'com, F: PrimeField> Query<F> for ProverQuery<'com, F> {
    type Commitment = PolynomialPointer<'com, F>;
    type Eval = F;

    fn get_point(&self) -> F {
        self.point
    }
    fn get_eval(&self) -> Self::Eval {
        eval_polynomial(&self.poly[..], self.get_point())
    }
    fn get_commitment(&self) -> Self::Commitment {
        PolynomialPointer { poly: self.poly }
    }
}

// impl<'com, F: PrimeField, CS: PolynomialCommitmentScheme<F>> VerifierQuery<'com, F, CS> {
//     /// Create a new verifier query based on a commitment
//     pub fn new_commitment(commitment: &'com C, point: C::Scalar, eval: C::Scalar) -> Self {
//         VerifierQuery {
//             point,
//             eval,
//             commitment: CommitmentReference::Commitment(commitment),
//         }
//     }
//
//     /// Create a new verifier query based on a linear combination of commitments
//     pub fn new_msm(msm: &'com M, point: C::Scalar, eval: C::Scalar) -> VerifierQuery<'com, C, M> {
//         VerifierQuery {
//             point,
//             eval,
//             commitment: CommitmentReference::MSM(msm),
//         }
//     }
// }

/// A polynomial query at a point
#[derive(Debug, Clone, Copy)]
pub struct VerifierQuery<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    /// Point at which polynomial is queried
    pub(crate) point: F,
    /// Commitment to polynomial
    pub(crate) commitment: CS::Commitment,
    /// Evaluation of polynomial at query point
    pub(crate) eval: F,
}

impl<F, CS> VerifierQuery<F, CS>
where
    F: PrimeField,
    CS: PolynomialCommitmentScheme<F>,
{
    /// Create a new verifier query based on a commitment
    pub fn new(point: F, commitment: CS::Commitment, eval: F) -> Self {
        VerifierQuery {
            point,
            commitment,
            eval,
        }
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> Query<F> for VerifierQuery<F, CS> {
    type Commitment = CS::Commitment;
    type Eval = F;

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
