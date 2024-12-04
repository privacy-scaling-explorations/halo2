//! Trait for a commitment scheme
use crate::poly::{Blind, Coeff, Error, Polynomial, ProverQuery, VerifierQuery};
use crate::transcript::{Hashable, Sampleable, Transcript};
use ff::PrimeField;
use halo2curves::serde::SerdeObject;

/// Public interface for a Polynomial Commitment Scheme (PCS)
pub trait PolynomialCommitmentScheme<F: PrimeField>: Clone {
    /// Parameters needed to generate a proof in the PCS
    type Parameters;
    /// Parameters needed to verify a proof in the PCS
    type VerifierParameters: From<Self::Parameters>;
    /// Type of a committed polynomial
    type Commitment: Clone + Copy + PartialEq + SerdeObject + Send + Sync; // Thinking of having an MSM here

    /// Setup the parameters for the PCS
    fn setup(k: u32) -> Self::Parameters;
    /// Create a new instantiation of the PCS
    fn new(params: Self::Parameters) -> Self;
    /// Commit to a polynomial
    fn commit(&self, polynomial: &Polynomial<F, Coeff>, blind: Blind<F>) -> Self::Commitment;
    /// Create an opening proof at a specific query
    fn open<T: Transcript>(
        &self,
        prover_query: Vec<ProverQuery<F>>,
        transcript: &mut T,
    ) -> Result<(), Error>
    where
        F: Sampleable<T::Hash>,
        Self::Commitment: Hashable<T::Hash>;
    /// Verify an opening proof at a given query
    fn verify<T: Transcript>(
        &self,
        verifier_query: Vec<VerifierQuery<F, Self>>,
        transcript: &mut T,
    ) -> Result<(), Error>
    where
        F: Sampleable<T::Hash>,
        Self::Commitment: Hashable<T::Hash>;
}
