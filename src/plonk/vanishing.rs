use ff::PrimeField;
use std::marker::PhantomData;

use crate::poly::commitment::PolynomialCommitmentScheme;

mod prover;
mod verifier;

/// A vanishing argument.
pub(crate) struct Argument<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    _marker: PhantomData<(F, CS)>,
}
