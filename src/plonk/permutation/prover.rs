use ff::{PrimeField, WithSmallOrderMulGroup};
use group::ff::BatchInvert;
use halo2curves::serde::SerdeObject;
use rand_core::RngCore;
use std::iter::{self, ExactSizeIterator};

use super::super::circuit::Any;
use super::{Argument, ProvingKey};
use crate::poly::commitment::{Params, PolynomialCommitmentScheme};
use crate::transcript::{Hashable, Transcript};
use crate::{
    arithmetic::{eval_polynomial, parallelize},
    plonk::{self, Error},
    poly::{Coeff, LagrangeCoeff, Polynomial, ProverQuery, Rotation},
};

pub(crate) struct CommittedSet<F: PrimeField> {
    pub(crate) permutation_product_poly: Polynomial<F, Coeff>,
}

pub(crate) struct Committed<F: PrimeField> {
    pub(crate) sets: Vec<CommittedSet<F>>,
}

pub(crate) struct Evaluated<F: PrimeField> {
    constructed: Committed<F>,
}

impl Argument {
    #[allow(clippy::too_many_arguments)]
    pub(in crate::plonk) fn commit<
        F: WithSmallOrderMulGroup<3>,
        CS: PolynomialCommitmentScheme<F>,
        R: RngCore,
        T: Transcript,
    >(
        &self,
        params: &CS::Parameters,
        pk: &plonk::ProvingKey<F, CS>,
        pkey: &ProvingKey<F>,
        advice: &[Polynomial<F, LagrangeCoeff>],
        fixed: &[Polynomial<F, LagrangeCoeff>],
        instance: &[Polynomial<F, LagrangeCoeff>],
        beta: F,
        gamma: F,
        mut rng: R,
        transcript: &mut T,
    ) -> Result<Committed<F>, Error>
    where
        CS::Commitment: Hashable<T::Hash>,
    {
        let domain = &pk.vk.domain;

        // How many columns can be included in a single permutation polynomial?
        // We need to multiply by z(X) and (1 - (l_last(X) + l_blind(X))). This
        // will never underflow because of the requirement of at least a degree
        // 3 circuit for the permutation argument.
        assert!(pk.vk.cs_degree >= 3);
        let chunk_len = pk.vk.cs_degree - 2;
        let blinding_factors = pk.vk.cs.blinding_factors();

        // Each column gets its own delta power.
        let mut deltaomega = F::ONE;

        // Track the "last" value from the previous column set
        let mut last_z = F::ONE;

        let mut sets = vec![];

        for (columns, permutations) in self
            .columns
            .chunks(chunk_len)
            .zip(pkey.permutations.chunks(chunk_len))
        {
            // Goal is to compute the products of fractions
            //
            // (p_j(\omega^i) + \delta^j \omega^i \beta + \gamma) /
            // (p_j(\omega^i) + \beta s_j(\omega^i) + \gamma)
            //
            // where p_j(X) is the jth column in this permutation,
            // and i is the ith row of the column.

            let mut modified_values = vec![F::ONE; params.n() as usize];

            // Iterate over each column of the permutation
            for (&column, permuted_column_values) in columns.iter().zip(permutations.iter()) {
                let values = match column.column_type() {
                    Any::Advice(_) => advice,
                    Any::Fixed => fixed,
                    Any::Instance => instance,
                };
                parallelize(&mut modified_values, |modified_values, start| {
                    for ((modified_values, value), permuted_value) in modified_values
                        .iter_mut()
                        .zip(values[column.index()][start..].iter())
                        .zip(permuted_column_values[start..].iter())
                    {
                        *modified_values *= &(beta * permuted_value + &gamma + value);
                    }
                });
            }

            // Invert to obtain the denominator for the permutation product polynomial
            modified_values.batch_invert();

            // Iterate over each column again, this time finishing the computation
            // of the entire fraction by computing the numerators
            for &column in columns.iter() {
                let omega = domain.get_omega();
                let values = match column.column_type() {
                    Any::Advice(_) => advice,
                    Any::Fixed => fixed,
                    Any::Instance => instance,
                };
                parallelize(&mut modified_values, |modified_values, start| {
                    let mut deltaomega = deltaomega * &omega.pow_vartime([start as u64, 0, 0, 0]);
                    for (modified_values, value) in modified_values
                        .iter_mut()
                        .zip(values[column.index()][start..].iter())
                    {
                        // Multiply by p_j(\omega^i) + \delta^j \omega^i \beta
                        *modified_values *= &(deltaomega * &beta + &gamma + value);
                        deltaomega *= &omega;
                    }
                });
                deltaomega *= &F::DELTA;
            }

            // The modified_values vector is a vector of products of fractions
            // of the form
            //
            // (p_j(\omega^i) + \delta^j \omega^i \beta + \gamma) /
            // (p_j(\omega^i) + \beta s_j(\omega^i) + \gamma)
            //
            // where i is the index into modified_values, for the jth column in
            // the permutation

            // Compute the evaluations of the permutation product polynomial
            // over our domain, starting with z[0] = 1
            let mut z = vec![last_z];
            for row in 1..(params.n() as usize) {
                let mut tmp = z[row - 1];

                tmp *= &modified_values[row - 1];
                z.push(tmp);
            }
            let mut z = domain.lagrange_from_vec(z);
            // Set blinding factors
            for z in &mut z[params.n() as usize - blinding_factors..] {
                *z = F::random(&mut rng);
            }
            // Set new last_z
            last_z = z[params.n() as usize - (blinding_factors + 1)];

            let permutation_product_commitment = params.commit_lagrange(&z);
            let permutation_product_poly = domain.lagrange_to_coeff(z);

            // Hash the permutation product commitment
            transcript.write(&permutation_product_commitment)?;

            sets.push(CommittedSet {
                permutation_product_poly,
            });
        }

        Ok(Committed { sets })
    }
}

impl<F: PrimeField> super::ProvingKey<F> {
    pub(in crate::plonk) fn open(&self, x: F) -> impl Iterator<Item = ProverQuery<'_, F>> + Clone {
        self.polys
            .iter()
            .map(move |poly| ProverQuery { point: x, poly })
    }

    pub(in crate::plonk) fn evaluate<T: Transcript>(
        &self,
        x: F,
        transcript: &mut T,
    ) -> Result<(), Error>
    where
        F: Hashable<T::Hash> + SerdeObject,
    {
        // Hash permutation evals
        for eval in self.polys.iter().map(|poly| eval_polynomial(poly, x)) {
            transcript.write(&eval)?;
        }

        Ok(())
    }
}

impl<F: WithSmallOrderMulGroup<3>> Committed<F> {
    // TODO: I don't quite like the PCS in the function
    pub(in crate::plonk) fn evaluate<T: Transcript, CS: PolynomialCommitmentScheme<F>>(
        self,
        pk: &plonk::ProvingKey<F, CS>,
        x: F,
        transcript: &mut T,
    ) -> Result<Evaluated<F>, Error>
    where
        F: Hashable<T::Hash> + SerdeObject,
    {
        let domain = &pk.vk.domain;
        let blinding_factors = pk.vk.cs.blinding_factors();

        {
            let mut sets = self.sets.iter();

            while let Some(set) = sets.next() {
                let permutation_product_eval = eval_polynomial(&set.permutation_product_poly, x);

                let permutation_product_next_eval = eval_polynomial(
                    &set.permutation_product_poly,
                    domain.rotate_omega(x, Rotation::next()),
                );

                // Hash permutation product evals
                for eval in iter::empty()
                    .chain(Some(&permutation_product_eval))
                    .chain(Some(&permutation_product_next_eval))
                {
                    transcript.write(eval)?;
                }

                // If we have any remaining sets to process, evaluate this set at omega^u
                // so we can constrain the last value of its running product to equal the
                // first value of the next set's running product, chaining them together.
                if sets.len() > 0 {
                    let permutation_product_last_eval = eval_polynomial(
                        &set.permutation_product_poly,
                        domain.rotate_omega(x, Rotation(-((blinding_factors + 1) as i32))),
                    );

                    transcript.write(&permutation_product_last_eval)?;
                }
            }
        }

        Ok(Evaluated { constructed: self })
    }
}

impl<F: WithSmallOrderMulGroup<3>> Evaluated<F> {
    // todo: ditto - I don't like the PCS here
    pub(in crate::plonk) fn open<'a, CS: PolynomialCommitmentScheme<F>>(
        &'a self,
        pk: &'a plonk::ProvingKey<F, CS>,
        x: F,
    ) -> impl Iterator<Item = ProverQuery<'a, F>> + Clone {
        let blinding_factors = pk.vk.cs.blinding_factors();
        let x_next = pk.vk.domain.rotate_omega(x, Rotation::next());
        let x_last = pk
            .vk
            .domain
            .rotate_omega(x, Rotation(-((blinding_factors + 1) as i32)));

        iter::empty()
            .chain(self.constructed.sets.iter().flat_map(move |set| {
                iter::empty()
                    // Open permutation product commitments at x and \omega x
                    .chain(Some(ProverQuery {
                        point: x,
                        poly: &set.permutation_product_poly,
                    }))
                    .chain(Some(ProverQuery {
                        point: x_next,
                        poly: &set.permutation_product_poly,
                    }))
            }))
            // Open it at \omega^{last} x for all but the last set. This rotation is only
            // sensical for the first row, but we only use this rotation in a constraint
            // that is gated on l_0.
            .chain(
                self.constructed
                    .sets
                    .iter()
                    .rev()
                    .skip(1)
                    .flat_map(move |set| {
                        Some(ProverQuery {
                            point: x_last,
                            poly: &set.permutation_product_poly,
                        })
                    }),
            )
    }
}
