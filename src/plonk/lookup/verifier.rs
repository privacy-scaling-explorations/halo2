use std::iter;

use super::super::circuit::Expression;
use super::Argument;
use crate::poly::commitment::PolynomialCommitmentScheme;
use crate::transcript::{Hashable, Transcript};
use crate::{
    plonk::{Error, VerifyingKey},
    poly::{Rotation, VerifierQuery},
};
use ff::{PrimeField, WithSmallOrderMulGroup};
use halo2curves::serde::SerdeObject;

pub struct PermutationCommitments<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    permuted_input_commitment: CS::Commitment,
    permuted_table_commitment: CS::Commitment,
}

pub struct Committed<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    permuted: PermutationCommitments<F, CS>,
    product_commitment: CS::Commitment,
}

pub struct Evaluated<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    committed: Committed<F, CS>,
    product_eval: F,
    product_next_eval: F,
    permuted_input_eval: F,
    permuted_input_inv_eval: F,
    permuted_table_eval: F,
}

impl<F: PrimeField> Argument<F> {
    pub(in crate::plonk) fn read_permuted_commitments<
        CS: PolynomialCommitmentScheme<F>,
        T: Transcript,
    >(
        &self,
        transcript: &mut T,
    ) -> Result<PermutationCommitments<F, CS>, Error>
    where
        CS::Commitment: Hashable<T::Hash>,
    {
        let permuted_input_commitment = transcript.read()?;
        let permuted_table_commitment = transcript.read()?;

        Ok(PermutationCommitments {
            permuted_input_commitment,
            permuted_table_commitment,
        })
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> PermutationCommitments<F, CS> {
    pub(in crate::plonk) fn read_product_commitment<T: Transcript>(
        self,
        transcript: &mut T,
    ) -> Result<Committed<F, CS>, Error>
    where
        CS::Commitment: Hashable<T::Hash> + SerdeObject,
    {
        let product_commitment = transcript.read()?;

        Ok(Committed {
            permuted: self,
            product_commitment,
        })
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> Committed<F, CS> {
    pub(crate) fn evaluate<T: Transcript>(
        self,
        transcript: &mut T,
    ) -> Result<Evaluated<F, CS>, Error>
    where
        F: Hashable<T::Hash> + SerdeObject,
    {
        let product_eval = transcript.read()?;
        let product_next_eval = transcript.read()?;
        let permuted_input_eval = transcript.read()?;
        let permuted_input_inv_eval = transcript.read()?;
        let permuted_table_eval = transcript.read()?;

        Ok(Evaluated {
            committed: self,
            product_eval,
            product_next_eval,
            permuted_input_eval,
            permuted_input_inv_eval,
            permuted_table_eval,
        })
    }
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> Evaluated<F, CS> {
    #[allow(clippy::too_many_arguments)]
    pub(in crate::plonk) fn expressions<'a>(
        &'a self,
        l_0: F,
        l_last: F,
        l_blind: F,
        argument: &'a Argument<F>,
        theta: F,
        beta: F,
        gamma: F,
        advice_evals: &[F],
        fixed_evals: &[F],
        instance_evals: &[F],
        challenges: &[F],
    ) -> impl Iterator<Item = F> + 'a {
        let active_rows = F::ONE - (l_last + l_blind);

        let product_expression = || {
            // z(\omega X) (a'(X) + \beta) (s'(X) + \gamma)
            // - z(X) (\theta^{m-1} a_0(X) + ... + a_{m-1}(X) + \beta) (\theta^{m-1} s_0(X) + ... + s_{m-1}(X) + \gamma)
            let left = self.product_next_eval
                * &(self.permuted_input_eval + &beta)
                * &(self.permuted_table_eval + &gamma);

            let compress_expressions = |expressions: &[Expression<F>]| {
                expressions
                    .iter()
                    .map(|expression| {
                        expression.evaluate(
                            &|scalar| scalar,
                            &|_| panic!("virtual selectors are removed during optimization"),
                            &|query| fixed_evals[query.index.unwrap()],
                            &|query| advice_evals[query.index.unwrap()],
                            &|query| instance_evals[query.index.unwrap()],
                            &|challenge| challenges[challenge.index()],
                            &|a| -a,
                            &|a, b| a + &b,
                            &|a, b| a * &b,
                            &|a, scalar| a * &scalar,
                        )
                    })
                    .fold(F::ZERO, |acc, eval| acc * &theta + &eval)
            };
            let right = self.product_eval
                * &(compress_expressions(&argument.input_expressions) + &beta)
                * &(compress_expressions(&argument.table_expressions) + &gamma);

            (left - &right) * &active_rows
        };

        std::iter::empty()
            .chain(
                // l_0(X) * (1 - z(X)) = 0
                Some(l_0 * &(F::ONE - &self.product_eval)),
            )
            .chain(
                // l_last(X) * (z(X)^2 - z(X)) = 0
                Some(l_last * &(self.product_eval.square() - &self.product_eval)),
            )
            .chain(
                // (1 - (l_last(X) + l_blind(X))) * (
                //   z(\omega X) (a'(X) + \beta) (s'(X) + \gamma)
                //   - z(X) (\theta^{m-1} a_0(X) + ... + a_{m-1}(X) + \beta) (\theta^{m-1} s_0(X) + ... + s_{m-1}(X) + \gamma)
                // ) = 0
                Some(product_expression()),
            )
            .chain(Some(
                // l_0(X) * (a'(X) - s'(X)) = 0
                l_0 * &(self.permuted_input_eval - &self.permuted_table_eval),
            ))
            .chain(Some(
                // (1 - (l_last(X) + l_blind(X))) * (a′(X) − s′(X))⋅(a′(X) − a′(\omega^{-1} X)) = 0
                (self.permuted_input_eval - &self.permuted_table_eval)
                    * &(self.permuted_input_eval - &self.permuted_input_inv_eval)
                    * &active_rows,
            ))
    }

    // todo: Removing trick from MSMs here
    pub(in crate::plonk) fn queries(
        &self,
        vk: &VerifyingKey<F, CS>,
        x: F,
    ) -> impl Iterator<Item = VerifierQuery<F, CS>> + Clone {
        let x_inv = vk.domain.rotate_omega(x, Rotation::prev());
        let x_next = vk.domain.rotate_omega(x, Rotation::next());

        iter::empty()
            // Open lookup product commitment at x
            .chain(Some(VerifierQuery::new(
                x,
                self.committed.product_commitment,
                self.product_eval,
            )))
            // Open lookup input commitments at x
            .chain(Some(VerifierQuery::new(
                x,
                self.committed.permuted.permuted_input_commitment,
                self.permuted_input_eval,
            )))
            // Open lookup table commitments at x
            .chain(Some(VerifierQuery::new(
                x,
                self.committed.permuted.permuted_table_commitment,
                self.permuted_table_eval,
            )))
            // Open lookup input commitments at \omega^{-1} x
            .chain(Some(VerifierQuery::new(
                x_inv,
                self.committed.permuted.permuted_input_commitment,
                self.permuted_input_inv_eval,
            )))
            // Open lookup product commitment at \omega x
            .chain(Some(VerifierQuery::new(
                x_next,
                self.committed.product_commitment,
                self.product_next_eval,
            )))
    }
}
