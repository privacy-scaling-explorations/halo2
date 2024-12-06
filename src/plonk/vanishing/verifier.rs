use std::iter;

use ff::{PrimeField, WithSmallOrderMulGroup};
use halo2curves::serde::SerdeObject;

use crate::poly::commitment::PolynomialCommitmentScheme;
use crate::transcript::{read_n, Hashable, Transcript};
use crate::{
    plonk::{Error, VerifyingKey},
    poly::VerifierQuery,
};

use super::Argument;

pub struct Committed<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    random_poly_commitment: CS::Commitment,
}

pub struct Constructed<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    h_commitments: Vec<CS::Commitment>,
    random_poly_commitment: CS::Commitment,
}

pub struct Evaluated<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    h_commitments: Vec<CS::Commitment>,
    random_poly_commitment: CS::Commitment,
    h_evals: Vec<F>,
    random_eval: F,
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> Argument<F, CS> {
    pub(in crate::plonk) fn read_commitments_before_y<T: Transcript>(
        transcript: &mut T,
    ) -> Result<Committed<F, CS>, Error>
    where
        CS::Commitment: Hashable<T::Hash> + SerdeObject,
    {
        let random_poly_commitment = transcript.read()?;

        Ok(Committed {
            random_poly_commitment,
        })
    }
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> Committed<F, CS> {
    pub(in crate::plonk) fn read_commitments_after_y<T: Transcript>(
        self,
        vk: &VerifyingKey<F, CS>,
        transcript: &mut T,
    ) -> Result<Constructed<F, CS>, Error>
    where
        CS::Commitment: Hashable<T::Hash> + SerdeObject,
    {
        // Obtain a commitment to h(X) in the form of multiple pieces of degree n - 1
        let h_commitments = read_n(transcript, vk.domain.get_quotient_poly_degree())?;

        Ok(Constructed {
            h_commitments,
            random_poly_commitment: self.random_poly_commitment,
        })
    }
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> Constructed<F, CS> {
    pub(in crate::plonk) fn evaluate_after_x<T: Transcript>(
        self,
        vk: &VerifyingKey<F, CS>,
        transcript: &mut T,
    ) -> Result<Evaluated<F, CS>, Error>
    where
        F: Hashable<T::Hash> + SerdeObject,
    {
        let h_evals = read_n(transcript, vk.domain.get_quotient_poly_degree())?;
        let random_eval = transcript.read()?;

        Ok(Evaluated {
            h_commitments: self.h_commitments,
            random_poly_commitment: self.random_poly_commitment,
            h_evals,
            random_eval,
        })
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> Evaluated<F, CS> {
    pub(in crate::plonk) fn verify(
        self,
        expressions: impl Iterator<Item = F>,
        y: F,
        xn: F,
    ) -> Result<Evaluated<F, CS>, Error> {
        let committed_h_eval = self
            .h_evals
            .iter()
            .rev()
            .fold(F::ZERO, |acc, eval| acc * xn + eval);

        let expected_h_eval = expressions.fold(F::ZERO, |h_eval, v| h_eval * &y + &v);
        let expected_h_eval = expected_h_eval * ((xn - F::ONE).invert().unwrap());

        if committed_h_eval != expected_h_eval {
            return Err(Error::ConstraintSystemFailure);
        }

        Ok(self)
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> Evaluated<F, CS> {
    pub(in crate::plonk) fn queries(
        &self,
        x: F,
    ) -> impl Iterator<Item = VerifierQuery<F, CS>> + Clone + '_ {
        iter::empty()
            .chain(
                self.h_commitments
                    .iter()
                    .zip(self.h_evals.iter())
                    .map(move |(&c, e)| VerifierQuery::new(x, c, *e)),
            )
            .chain(Some(VerifierQuery::new(
                x,
                self.random_poly_commitment,
                self.random_eval,
            )))
    }
}
