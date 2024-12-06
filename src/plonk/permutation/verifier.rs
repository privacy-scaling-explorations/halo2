use ff::PrimeField;
use halo2curves::serde::SerdeObject;
use std::iter;

use super::super::circuit::Any;
use super::{Argument, VerifyingKey};
use crate::poly::commitment::PolynomialCommitmentScheme;
use crate::transcript::{Hashable, Transcript};
use crate::{
    plonk::{self, Error},
    poly::{Rotation, VerifierQuery},
};

pub struct Committed<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    permutation_product_commitments: Vec<CS::Commitment>,
}

pub struct EvaluatedSet<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    permutation_product_commitment: CS::Commitment,
    permutation_product_eval: F,
    permutation_product_next_eval: F,
    permutation_product_last_eval: Option<F>,
}

pub struct CommonEvaluated<F: PrimeField> {
    permutation_evals: Vec<F>,
}

pub struct Evaluated<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    sets: Vec<EvaluatedSet<F, CS>>,
}

impl Argument {
    pub(crate) fn read_product_commitments<
        F: PrimeField,
        CS: PolynomialCommitmentScheme<F>,
        T: Transcript,
    >(
        &self,
        vk: &plonk::VerifyingKey<F, CS>,
        transcript: &mut T,
    ) -> Result<Committed<F, CS>, Error>
    where
        CS::Commitment: Hashable<T::Hash> + SerdeObject,
    {
        let chunk_len = vk.cs_degree - 2;

        let permutation_product_commitments = self
            .columns
            .chunks(chunk_len)
            .map(|_| transcript.read())
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Committed {
            permutation_product_commitments,
        })
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> VerifyingKey<F, CS> {
    pub(in crate::plonk) fn evaluate<T: Transcript>(
        &self,
        transcript: &mut T,
    ) -> Result<CommonEvaluated<F>, Error>
    where
        F: Hashable<T::Hash> + SerdeObject,
    {
        let permutation_evals = self
            .commitments
            .iter()
            .map(|_| transcript.read())
            .collect::<Result<Vec<_>, _>>()?;

        Ok(CommonEvaluated { permutation_evals })
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> Committed<F, CS> {
    pub(crate) fn evaluate<T: Transcript>(
        self,
        transcript: &mut T,
    ) -> Result<Evaluated<F, CS>, Error>
    where
        CS::Commitment: Hashable<T::Hash> + SerdeObject,
        F: Hashable<T::Hash> + SerdeObject,
    {
        let mut sets = vec![];

        let mut iter = self.permutation_product_commitments.into_iter();

        while let Some(permutation_product_commitment) = iter.next() {
            let permutation_product_eval = transcript.read()?;
            let permutation_product_next_eval = transcript.read()?;
            let permutation_product_last_eval = if iter.len() > 0 {
                Some(transcript.read()?)
            } else {
                None
            };

            sets.push(EvaluatedSet {
                permutation_product_commitment,
                permutation_product_eval,
                permutation_product_next_eval,
                permutation_product_last_eval,
            });
        }

        Ok(Evaluated { sets })
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> Evaluated<F, CS> {
    #[allow(clippy::too_many_arguments)]
    pub(in crate::plonk) fn expressions<'a>(
        &'a self,
        vk: &'a plonk::VerifyingKey<F, CS>,
        p: &'a Argument,
        common: &'a CommonEvaluated<F>,
        advice_evals: &'a [F],
        fixed_evals: &'a [F],
        instance_evals: &'a [F],
        l_0: F,
        l_last: F,
        l_blind: F,
        beta: F,
        gamma: F,
        x: F,
    ) -> impl Iterator<Item = F> + 'a {
        let chunk_len = vk.cs_degree - 2;
        iter::empty()
            // Enforce only for the first set.
            // l_0(X) * (1 - z_0(X)) = 0
            .chain(
                self.sets
                    .first()
                    .map(|first_set| l_0 * &(F::ONE - &first_set.permutation_product_eval)),
            )
            // Enforce only for the last set.
            // l_last(X) * (z_l(X)^2 - z_l(X)) = 0
            .chain(self.sets.last().map(|last_set| {
                (last_set.permutation_product_eval.square() - &last_set.permutation_product_eval)
                    * &l_last
            }))
            // Except for the first set, enforce.
            // l_0(X) * (z_i(X) - z_{i-1}(\omega^(last) X)) = 0
            .chain(
                self.sets
                    .iter()
                    .skip(1)
                    .zip(self.sets.iter())
                    .map(|(set, last_set)| {
                        (
                            set.permutation_product_eval,
                            last_set.permutation_product_last_eval.unwrap(),
                        )
                    })
                    .map(move |(set, prev_last)| (set - &prev_last) * &l_0),
            )
            // And for all the sets we enforce:
            // (1 - (l_last(X) + l_blind(X))) * (
            //   z_i(\omega X) \prod (p(X) + \beta s_i(X) + \gamma)
            // - z_i(X) \prod (p(X) + \delta^i \beta X + \gamma)
            // )
            .chain(
                self.sets
                    .iter()
                    .zip(p.columns.chunks(chunk_len))
                    .zip(common.permutation_evals.chunks(chunk_len))
                    .enumerate()
                    .map(move |(chunk_index, ((set, columns), permutation_evals))| {
                        let mut left = set.permutation_product_next_eval;
                        for (eval, permutation_eval) in columns
                            .iter()
                            .map(|&column| match column.column_type() {
                                Any::Advice(_) => {
                                    advice_evals[vk.cs.get_any_query_index(column, Rotation::cur())]
                                }
                                Any::Fixed => {
                                    fixed_evals[vk.cs.get_any_query_index(column, Rotation::cur())]
                                }
                                Any::Instance => {
                                    instance_evals
                                        [vk.cs.get_any_query_index(column, Rotation::cur())]
                                }
                            })
                            .zip(permutation_evals.iter())
                        {
                            left *= &(eval + &(beta * permutation_eval) + &gamma);
                        }

                        let mut right = set.permutation_product_eval;
                        let mut current_delta = (beta * &x)
                            * &(<F as PrimeField>::DELTA
                                .pow_vartime([(chunk_index * chunk_len) as u64]));
                        for eval in columns.iter().map(|&column| match column.column_type() {
                            Any::Advice(_) => {
                                advice_evals[vk.cs.get_any_query_index(column, Rotation::cur())]
                            }
                            Any::Fixed => {
                                fixed_evals[vk.cs.get_any_query_index(column, Rotation::cur())]
                            }
                            Any::Instance => {
                                instance_evals[vk.cs.get_any_query_index(column, Rotation::cur())]
                            }
                        }) {
                            right *= &(eval + &current_delta + &gamma);
                            current_delta *= &F::DELTA;
                        }

                        (left - &right) * (F::ONE - &(l_last + &l_blind))
                    }),
            )
    }

    // todo: Removing the MSM tricks here. Bring them back
    pub(in crate::plonk) fn queries<'r>(
        &'r self,
        vk: &'r plonk::VerifyingKey<F, CS>,
        x: F,
    ) -> impl Iterator<Item = VerifierQuery<F, CS>> + Clone + 'r {
        let blinding_factors = vk.cs.blinding_factors();
        let x_next = vk.domain.rotate_omega(x, Rotation::next());
        let x_last = vk
            .domain
            .rotate_omega(x, Rotation(-((blinding_factors + 1) as i32)));

        iter::empty()
            .chain(self.sets.iter().flat_map(move |set| {
                iter::empty()
                    // Open permutation product commitments at x and \omega^{-1} x
                    // Open permutation product commitments at x and \omega x
                    .chain(Some(VerifierQuery::new(
                        x,
                        set.permutation_product_commitment,
                        set.permutation_product_eval,
                    )))
                    .chain(Some(VerifierQuery::new(
                        x_next,
                        set.permutation_product_commitment,
                        set.permutation_product_next_eval,
                    )))
            }))
            // Open it at \omega^{last} x for all but the last set
            .chain(self.sets.iter().rev().skip(1).flat_map(move |set| {
                Some(VerifierQuery::new(
                    x_last,
                    set.permutation_product_commitment,
                    set.permutation_product_last_eval.unwrap(),
                ))
            }))
    }
}

impl<F: PrimeField> CommonEvaluated<F> {
    // todo: MSM trick here
    pub(in crate::plonk) fn queries<'r, CS: PolynomialCommitmentScheme<F>>(
        &'r self,
        vkey: &'r VerifyingKey<F, CS>,
        x: F,
    ) -> impl Iterator<Item = VerifierQuery<F, CS>> + Clone + 'r {
        // Open permutation commitments for each permutation argument at x
        vkey.commitments
            .iter()
            .zip(self.permutation_evals.iter())
            .map(move |(&commitment, &eval)| VerifierQuery::new(x, commitment, eval))
    }
}
