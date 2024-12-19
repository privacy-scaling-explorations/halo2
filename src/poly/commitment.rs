//! Trait for a commitment scheme
use crate::poly::{Coeff, Error, LagrangeCoeff, Polynomial, ProverQuery, VerifierQuery};
use crate::transcript::{Hashable, Sampleable, Transcript};
use crate::utils::helpers::ProcessedSerdeObject;
use ff::PrimeField;
use std::fmt::Debug;

/// Public interface for a Polynomial Commitment Scheme (PCS)
pub trait PolynomialCommitmentScheme<F: PrimeField>: Clone + Debug {
    /// Parameters needed to generate a proof in the PCS
    type Parameters: Params<F, Self>;

    /// Parameters needed to verify a proof in the PCS
    type VerifierParameters: Params<F, Self>;

    /// Type of a committed polynomial
    type Commitment: Clone + Copy + Debug + Default + PartialEq + ProcessedSerdeObject + Send + Sync;

    /// Setup the parameters for the PCS
    fn setup(k: u32) -> Self::Parameters;

    /// Commit to a polynomial in coefficient form
    fn commit(params: &Self::Parameters, polynomial: &Polynomial<F, Coeff>) -> Self::Commitment;

    /// Create an opening proof at a specific query
    /// FIXME: We are not writing the queries to the transcript
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
    fn verify<T: Transcript, I>(
        params: &Self::VerifierParameters,
        verifier_query: I,
        transcript: &mut T,
    ) -> Result<(), Error>
    where
        I: IntoIterator<Item = VerifierQuery<F, Self>> + Clone,
        F: Sampleable<T::Hash>, // This is not necessarily part of a PCS
        Self::Commitment: Hashable<T::Hash>;
}

/// Interface for prover/verifier params
pub trait Params<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    /// Logarithmic size of polynomials that can be committed with these parameters
    fn k(&self) -> u32;

    /// Size of polynomials that can be committed with these parameters
    fn n(&self) -> u64;

    /// This commits to a polynomial using its evaluations over the $2^k$ size
    /// evaluation domain. The commitment will be blinded by the blinding factor
    /// `r`.
    fn commit_lagrange(&self, poly: &Polynomial<F, LagrangeCoeff>) -> CS::Commitment;
}
