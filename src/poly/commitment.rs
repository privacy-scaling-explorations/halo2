//! Trait for a commitment scheme
use crate::poly::{Coeff, Error, LagrangeCoeff, Polynomial, ProverQuery, VerifierQuery};
use crate::transcript::{Hashable, Sampleable, Transcript};
use crate::utils::helpers::ProcessedSerdeObject;
use ff::PrimeField;
use std::fmt::Debug;

/// Public interface for a Polynomial Commitment Scheme (PCS)
pub trait PolynomialCommitmentScheme<F: PrimeField>: Clone + Debug {
    /// Parameters needed to generate a proof in the PCS
    type Parameters: Params;

    /// Parameters needed to verify a proof in the PCS
    type VerifierParameters;

    /// Type of a committed polynomial
    type Commitment: Clone + Copy + Debug + Default + PartialEq + ProcessedSerdeObject + Send + Sync;

    /// Verification guard. Allows for batch verification
    type VerificationGuard: Guard<F, Self>;

    /// Generates the parameters of the polynomial commitment scheme
    fn gen_params(k: u32) -> Self::Parameters;

    /// Extract the `VerifierParameters` from `Parameters`
    fn get_verifier_params(params: &Self::Parameters) -> Self::VerifierParameters;

    /// Commit to a polynomial in coefficient form
    fn commit(params: &Self::Parameters, polynomial: &Polynomial<F, Coeff>) -> Self::Commitment;

    /// Commit to a polynomial expressed in Lagrange evaluations form (over the underlying domain
    /// specified in params).
    fn commit_lagrange(
        params: &Self::Parameters,
        poly: &Polynomial<F, LagrangeCoeff>,
    ) -> Self::Commitment;

    /// Create an opening proof at a specific query
    fn open<'com, T: Transcript, I>(
        params: &Self::Parameters,
        prover_query: I,
        transcript: &mut T,
    ) -> Result<(), Error>
    where
        I: IntoIterator<Item = ProverQuery<'com, F>> + Clone,
        F: Sampleable<T::Hash>,
        Self::Commitment: Hashable<T::Hash>;

    /// Verify an opening proof at a given query
    fn prepare<T: Transcript, I>(
        verifier_query: I,
        transcript: &mut T,
    ) -> Result<Self::VerificationGuard, Error>
    where
        I: IntoIterator<Item = VerifierQuery<F, Self>> + Clone,
        F: Sampleable<T::Hash>,
        Self::Commitment: Hashable<T::Hash>;
}

/// Interface for verifier finalizer
pub trait Guard<F: PrimeField, CS: PolynomialCommitmentScheme<F>>: Sized {
    /// Finalize the verification guard
    fn verify(self, params: &CS::VerifierParameters) -> Result<(), Error>;

    /// Finalize a batch of verification guards
    fn batch_verify<'a, I, J>(guards: I, params: J) -> Result<(), Error>
    where
        I: ExactSizeIterator<Item = Self>,
        J: ExactSizeIterator<Item = &'a CS::VerifierParameters>,
        CS::VerifierParameters: 'a,
    {
        assert_eq!(guards.len(), params.len());
        guards
            .into_iter()
            .zip(params)
            .try_for_each(|(guard, params)| guard.verify(params))
    }
}

/// Interface for PCS params
pub trait Params {
    /// Returns the max size of polynomials that these parameters can commit to
    fn max_k(&self) -> u32;
}
