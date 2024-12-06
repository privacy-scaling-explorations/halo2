use ff::PrimeField;
use std::marker::PhantomData;

use crate::poly::commitment::PolynomialCommitmentScheme;

mod prover;
mod verifier;

/// A vanishing argument.
/// todo: do we need to have the PCS here?
pub(crate) struct Argument<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    _marker: PhantomData<(F, CS)>,
}
