use ff::WithSmallOrderMulGroup;
use halo2curves::serde::SerdeObject;
use std::iter;

use super::{vanishing, Error, VerifyingKey};
use crate::utils::arithmetic::compute_inner_product;
use crate::poly::commitment::{Params, PolynomialCommitmentScheme};
use crate::poly::VerifierQuery;
use crate::transcript::{read_n, Hashable, Sampleable, Transcript};

/// Returns a boolean indicating whether or not the proof is valid
pub fn verify_proof<
    F: WithSmallOrderMulGroup<3> + Hashable<T::Hash> + Sampleable<T::Hash> + SerdeObject,
    CS: PolynomialCommitmentScheme<F>,
    T: Transcript,
>(
    params: &CS::VerifierParameters,
    vk: &VerifyingKey<F, CS>,
    instances: &[&[&[F]]],
    transcript: &mut T,
) -> Result<(), Error>
where
    CS::Commitment: Hashable<T::Hash> + SerdeObject,
{
    // Check that instances matches the expected number of instance columns
    for instances in instances.iter() {
        if instances.len() != vk.cs.num_instance_columns {
            return Err(Error::InvalidInstances);
        }
    }

    let num_proofs = instances.len();

    // Hash verification key into transcript
    vk.hash_into(transcript)?;

    for instance in instances.iter() {
        for instance in instance.iter() {
            for value in instance.iter() {
                transcript.common(value)?;
            }
        }
    }

    // Hash the prover's advice commitments into the transcript and squeeze challenges
    let (advice_commitments, challenges) = {
        let mut advice_commitments =
            vec![vec![CS::Commitment::default(); vk.cs.num_advice_columns]; num_proofs];
        let mut challenges = vec![F::ZERO; vk.cs.num_challenges];

        for current_phase in vk.cs.phases() {
            for advice_commitments in advice_commitments.iter_mut() {
                for (phase, commitment) in vk
                    .cs
                    .advice_column_phase
                    .iter()
                    .zip(advice_commitments.iter_mut())
                {
                    if current_phase == *phase {
                        *commitment = transcript.read()?;
                    }
                }
            }
            for (phase, challenge) in vk.cs.challenge_phase.iter().zip(challenges.iter_mut()) {
                if current_phase == *phase {
                    *challenge = transcript.squeeze_challenge();
                }
            }
        }

        (advice_commitments, challenges)
    };

    // Sample theta challenge for keeping lookup columns linearly independent
    let theta: F = transcript.squeeze_challenge();

    let lookups_permuted = (0..num_proofs)
        .map(|_| -> Result<Vec<_>, _> {
            // Hash each lookup permuted commitment
            vk.cs
                .lookups
                .iter()
                .map(|argument| argument.read_permuted_commitments(transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Sample beta challenge
    let beta: F = transcript.squeeze_challenge();

    // Sample gamma challenge
    let gamma: F = transcript.squeeze_challenge();

    let permutations_committed = (0..num_proofs)
        .map(|_| {
            // Hash each permutation product commitment
            vk.cs.permutation.read_product_commitments(vk, transcript)
        })
        .collect::<Result<Vec<_>, _>>()?;

    let lookups_committed = lookups_permuted
        .into_iter()
        .map(|lookups| {
            // Hash each lookup product commitment
            lookups
                .into_iter()
                .map(|lookup| lookup.read_product_commitment(transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    let vanishing = vanishing::Argument::read_commitments_before_y(transcript)?;

    // Sample y challenge, which keeps the gates linearly independent.
    let y: F = transcript.squeeze_challenge();

    let vanishing = vanishing.read_commitments_after_y(vk, transcript)?;

    // Sample x challenge, which is used to ensure the circuit is
    // satisfied with high probability.
    let x: F = transcript.squeeze_challenge();
    let instance_evals = {
        let xn = x.pow([params.n()]);
        let (min_rotation, max_rotation) =
            vk.cs
                .instance_queries
                .iter()
                .fold((0, 0), |(min, max), (_, rotation)| {
                    if rotation.0 < min {
                        (rotation.0, max)
                    } else if rotation.0 > max {
                        (min, rotation.0)
                    } else {
                        (min, max)
                    }
                });
        let max_instance_len = instances
            .iter()
            .flat_map(|instance| instance.iter().map(|instance| instance.len()))
            .max_by(Ord::cmp)
            .unwrap_or_default();
        let l_i_s = &vk.domain.l_i_range(
            x,
            xn,
            -max_rotation..max_instance_len as i32 + min_rotation.abs(),
        );
        instances
            .iter()
            .map(|instances| {
                vk.cs
                    .instance_queries
                    .iter()
                    .map(|(column, rotation)| {
                        let instances = instances[column.index()];
                        let offset = (max_rotation - rotation.0) as usize;
                        compute_inner_product(instances, &l_i_s[offset..offset + instances.len()])
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    };

    let advice_evals = (0..num_proofs)
        .map(|_| -> Result<Vec<_>, _> { read_n(transcript, vk.cs.advice_queries.len()) })
        .collect::<Result<Vec<_>, _>>()?;

    let fixed_evals = read_n(transcript, vk.cs.fixed_queries.len())?;

    let vanishing = vanishing.evaluate_after_x(vk, transcript)?;

    let permutations_common = vk.permutation.evaluate(transcript)?;

    let permutations_evaluated = permutations_committed
        .into_iter()
        .map(|permutation| permutation.evaluate(transcript))
        .collect::<Result<Vec<_>, _>>()?;

    let lookups_evaluated = lookups_committed
        .into_iter()
        .map(|lookups| -> Result<Vec<_>, _> {
            lookups
                .into_iter()
                .map(|lookup| lookup.evaluate(transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    // This check ensures the circuit is satisfied so long as the polynomial
    // commitments open to the correct values.
    let vanishing = {
        // x^n
        let xn = x.pow([params.n()]);

        let blinding_factors = vk.cs.blinding_factors();
        let l_evals = vk
            .domain
            .l_i_range(x, xn, (-((blinding_factors + 1) as i32))..=0);
        assert_eq!(l_evals.len(), 2 + blinding_factors);
        let l_last = l_evals[0];
        let l_blind: F = l_evals[1..(1 + blinding_factors)]
            .iter()
            .fold(F::ZERO, |acc, eval| acc + eval);
        let l_0 = l_evals[1 + blinding_factors];

        // Compute the expected value of h(x)
        let expressions = advice_evals
            .iter()
            .zip(instance_evals.iter())
            .zip(permutations_evaluated.iter())
            .zip(lookups_evaluated.iter())
            .flat_map(|(((advice_evals, instance_evals), permutation), lookups)| {
                let challenges = &challenges;
                let fixed_evals = &fixed_evals;
                std::iter::empty()
                    // Evaluate the circuit using the custom gates provided
                    .chain(vk.cs.gates.iter().flat_map(move |gate| {
                        gate.polynomials().iter().map(move |poly| {
                            poly.evaluate(
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
                    }))
                    .chain(permutation.expressions(
                        vk,
                        &vk.cs.permutation,
                        &permutations_common,
                        advice_evals,
                        fixed_evals,
                        instance_evals,
                        l_0,
                        l_last,
                        l_blind,
                        beta,
                        gamma,
                        x,
                    ))
                    .chain(lookups.iter().zip(vk.cs.lookups.iter()).flat_map(
                        move |(p, argument)| {
                            p.expressions(
                                l_0,
                                l_last,
                                l_blind,
                                argument,
                                theta,
                                beta,
                                gamma,
                                advice_evals,
                                fixed_evals,
                                instance_evals,
                                challenges,
                            )
                        },
                    ))
            });

        vanishing.verify(expressions, y, xn)?
    };

    let queries = advice_commitments
        .iter()
        .zip(advice_evals.iter())
        .zip(permutations_evaluated.iter())
        .zip(lookups_evaluated.iter())
        .flat_map(
            |(((advice_commitments, advice_evals), permutation), lookups)| {
                iter::empty()
                    .chain(vk.cs.advice_queries.iter().enumerate().map(
                        move |(query_index, &(column, at))| {
                            VerifierQuery::new(
                                vk.domain.rotate_omega(x, at),
                                advice_commitments[column.index()],
                                advice_evals[query_index],
                            )
                        },
                    ))
                    .chain(permutation.queries(vk, x))
                    .chain(lookups.iter().flat_map(move |p| p.queries(vk, x)))
            },
        )
        .chain(
            vk.cs
                .fixed_queries
                .iter()
                .enumerate()
                .map(|(query_index, &(column, at))| {
                    VerifierQuery::new(
                        vk.domain.rotate_omega(x, at),
                        vk.fixed_commitments[column.index()],
                        fixed_evals[query_index],
                    )
                }),
        )
        .chain(permutations_common.queries(&vk.permutation, x))
        .chain(vanishing.queries(x));

    // We are now convinced the circuit is satisfied so long as the
    // polynomial commitments open to the correct values.
    CS::verify(params, queries, transcript).map_err(|_| Error::Opening)
}
