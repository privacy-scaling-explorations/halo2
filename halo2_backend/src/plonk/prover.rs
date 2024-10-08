//! Generate a proof

use group::prime::PrimeCurveAffine;
use group::Curve;
use rand_core::RngCore;
use std::collections::{BTreeSet, HashSet};
use std::{collections::HashMap, iter};

use crate::arithmetic::{eval_polynomial, CurveAffine};
use crate::plonk::{
    lookup, lookup::prover::lookup_commit_permuted, permutation,
    permutation::prover::permutation_commit, shuffle, shuffle::prover::shuffle_commit_product,
    vanishing, ChallengeBeta, ChallengeGamma, ChallengeTheta, ChallengeX, ChallengeY, Error,
    ProvingKey,
};
use crate::poly::{
    commitment::{self, Blind, CommitmentScheme, Params},
    Basis, Coeff, LagrangeCoeff, Polynomial, ProverQuery,
};
use crate::transcript::{EncodedChallenge, TranscriptWrite};
use halo2_middleware::ff::{Field, FromUniformBytes, WithSmallOrderMulGroup};
use halo2_middleware::zal::{
    impls::{H2cEngine, PlonkEngine, PlonkEngineConfig},
    traits::MsmAccel,
};

/// Collection of instance data used during proving for a single circuit proof.
#[derive(Debug)]
struct InstanceSingle<C: CurveAffine> {
    pub instance_values: Vec<Polynomial<C::Scalar, LagrangeCoeff>>,
    pub instance_polys: Vec<Polynomial<C::Scalar, Coeff>>,
}

/// Collection of advice data used during proving for a single circuit proof.
#[derive(Debug, Clone)]
struct AdviceSingle<C: CurveAffine, B: Basis> {
    pub advice_polys: Vec<Polynomial<C::Scalar, B>>,
    pub advice_blinds: Vec<Blind<C::Scalar>>,
}

/// The prover object used to create proofs interactively by passing the witnesses to commit at
/// each phase.  This works for a single proof.  This is a wrapper over ProverMulti.
#[derive(Debug)]
pub struct Prover<
    'a,
    'params,
    Scheme: CommitmentScheme,
    P: commitment::Prover<'params, Scheme>,
    E: EncodedChallenge<Scheme::Curve>,
    R: RngCore,
    T: TranscriptWrite<Scheme::Curve, E>,
    M: MsmAccel<Scheme::Curve>,
>(ProverMulti<'a, 'params, Scheme, P, E, R, T, M>);

impl<
        'a,
        'params,
        Scheme: CommitmentScheme,
        P: commitment::Prover<'params, Scheme>,
        E: EncodedChallenge<Scheme::Curve>,
        R: RngCore,
        T: TranscriptWrite<Scheme::Curve, E>,
        M: MsmAccel<Scheme::Curve>,
    > Prover<'a, 'params, Scheme, P, E, R, T, M>
{
    /// Create a new ProverMulti object
    pub fn new_with_engine(
        engine: PlonkEngine<Scheme::Curve, M>,
        params: &'params Scheme::ParamsProver,
        pk: &'a ProvingKey<Scheme::Curve>,
        instance: Vec<Vec<Scheme::Scalar>>,
        rng: R,
        transcript: &'a mut T,
    ) -> Result<Self, Error>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        Ok(Self(ProverMulti::new_with_engine(
            engine,
            params,
            pk,
            &[instance],
            rng,
            transcript,
        )?))
    }

    pub fn new(
        params: &'params Scheme::ParamsProver,
        pk: &'a ProvingKey<Scheme::Curve>,
        instance: Vec<Vec<Scheme::Scalar>>,
        rng: R,
        transcript: &'a mut T,
    ) -> Result<Prover<'a, 'params, Scheme, P, E, R, T, H2cEngine>, Error>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        let engine = PlonkEngineConfig::build_default();
        Prover::new_with_engine(engine, params, pk, instance, rng, transcript)
    }

    /// Commit the `witness` at `phase` and return the challenges after `phase`.
    pub fn commit_phase(
        &mut self,
        phase: u8,
        witness: Vec<Option<Vec<Scheme::Scalar>>>,
    ) -> Result<HashMap<usize, Scheme::Scalar>, Error>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        self.0.commit_phase(phase, vec![witness])
    }

    /// Finalizes the proof creation.
    pub fn create_proof(self) -> Result<(), Error>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        self.0.create_proof()
    }
}

/// The prover object used to create proofs interactively by passing the witnesses to commit at
/// each phase.  This supports batch proving.
#[derive(Debug)]
pub struct ProverMulti<
    'a,
    'params,
    Scheme: CommitmentScheme,
    P: commitment::Prover<'params, Scheme>,
    E: EncodedChallenge<Scheme::Curve>,
    R: RngCore,
    T: TranscriptWrite<Scheme::Curve, E>,
    M: MsmAccel<Scheme::Curve>,
> {
    engine: PlonkEngine<Scheme::Curve, M>,
    // Circuit and setup fields
    params: &'params Scheme::ParamsProver,
    // Plonk proving key
    pk: &'a ProvingKey<Scheme::Curve>,
    // Phases
    phases: Vec<u8>,
    // Polynomials (Lagrange and Coeff) for all circuits instances
    instances: Vec<InstanceSingle<Scheme::Curve>>,
    // Advice polynomials with its blindings
    advices: Vec<AdviceSingle<Scheme::Curve, LagrangeCoeff>>,
    // The phase challenges by challenge index
    challenges: HashMap<usize, Scheme::Scalar>,
    // The next phase to be committed
    next_phase_index: usize,
    // Transcript to be updated
    transcript: &'a mut T,
    // Randomness
    rng: R,
    _marker: std::marker::PhantomData<(P, E)>,
}

impl<
        'a,
        'params,
        Scheme: CommitmentScheme,
        P: commitment::Prover<'params, Scheme>,
        E: EncodedChallenge<Scheme::Curve>,
        R: RngCore,
        T: TranscriptWrite<Scheme::Curve, E>,
        M: MsmAccel<Scheme::Curve>,
    > ProverMulti<'a, 'params, Scheme, P, E, R, T, M>
{
    /// Create a new prover object
    pub fn new_with_engine(
        engine: PlonkEngine<Scheme::Curve, M>,
        params: &'params Scheme::ParamsProver,
        pk: &'a ProvingKey<Scheme::Curve>,
        circuits_instances: &[Vec<Vec<Scheme::Scalar>>],
        rng: R,
        transcript: &'a mut T,
    ) -> Result<Self, Error>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        for instance in circuits_instances.iter() {
            if instance.len() != pk.vk.cs.num_instance_columns {
                return Err(Error::InvalidInstances);
            }
        }

        // Hash verification key into transcript [TRANSCRIPT-1]
        pk.vk.hash_into(transcript)?;

        let meta = &pk.vk.cs;
        let phases = meta.phases().collect();

        let domain = &pk.vk.domain;

        // commit_instance_fn is a helper function to return the polynomials (and its commitments) of
        // instance columns while updating the transcript.
        let mut commit_instance_fn =
            |instance: &[Vec<Scheme::Scalar>]| -> Result<InstanceSingle<Scheme::Curve>, Error> {
                // Create a lagrange polynomial for each instance column

                let instance_values = instance
                    .iter()
                    .map(|values| {
                        let mut poly = domain.empty_lagrange();
                        assert_eq!(poly.len(), params.n() as usize);
                        if values.len() > (poly.len() - (meta.blinding_factors() + 1)) {
                            return Err(Error::InstanceTooLarge);
                        }
                        for (poly, value) in poly.iter_mut().zip(values.iter()) {
                            if !P::QUERY_INSTANCE {
                                // Add to the transcript the instance polynomials lagrange value.
                                transcript.common_scalar(*value)?;
                            }
                            *poly = *value;
                        }
                        Ok(poly)
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                if P::QUERY_INSTANCE {
                    // Add to the transcript the commitments of the instance lagrange polynomials

                    let instance_commitments_projective: Vec<_> = instance_values
                        .iter()
                        .map(|poly| {
                            params.commit_lagrange(&engine.msm_backend, poly, Blind::default())
                        })
                        .collect();
                    let mut instance_commitments =
                        vec![Scheme::Curve::identity(); instance_commitments_projective.len()];
                    <Scheme::Curve as CurveAffine>::CurveExt::batch_normalize(
                        &instance_commitments_projective,
                        &mut instance_commitments,
                    );
                    let instance_commitments = instance_commitments;
                    drop(instance_commitments_projective);

                    for commitment in &instance_commitments {
                        transcript.common_point(*commitment)?;
                    }
                }

                // Convert from evaluation to coefficient form.

                let instance_polys: Vec<_> = instance_values
                    .iter()
                    .map(|poly| {
                        let lagrange_vec = domain.lagrange_from_vec(poly.to_vec());
                        domain.lagrange_to_coeff(lagrange_vec)
                    })
                    .collect();

                Ok(InstanceSingle {
                    instance_values,
                    instance_polys,
                })
            };

        // Commit the polynomials of all circuits instances
        // [TRANSCRIPT-2]

        let instances: Vec<InstanceSingle<Scheme::Curve>> = circuits_instances
            .iter()
            .map(|instance| commit_instance_fn(instance))
            .collect::<Result<Vec<_>, _>>()?;

        // Create an structure to hold the advice polynomials and its blinds, it will be filled later in the
        // [`commit_phase`].

        let advices = vec![
            AdviceSingle::<Scheme::Curve, LagrangeCoeff> {
                // Create vectors with empty polynomials to free space while they are not being used
                advice_polys: vec![
                    Polynomial::new_empty(0, Scheme::Scalar::ZERO);
                    meta.num_advice_columns
                ],
                advice_blinds: vec![Blind::default(); meta.num_advice_columns],
            };
            circuits_instances.len()
        ];

        // Challenges will be also filled later in the [`commit_phase`].

        let challenges = HashMap::<usize, Scheme::Scalar>::with_capacity(meta.num_challenges);

        Ok(ProverMulti {
            engine,
            params,
            pk,
            phases,
            instances,
            rng,
            transcript,
            advices,
            challenges,
            next_phase_index: 0,
            _marker: std::marker::PhantomData {},
        })
    }

    /// Commit the `witness` at `phase` and return the challenges after `phase`.
    #[allow(clippy::type_complexity)]
    pub fn commit_phase(
        &mut self,
        phase: u8,
        witness: Vec<Vec<Option<Vec<Scheme::Scalar>>>>,
    ) -> Result<HashMap<usize, Scheme::Scalar>, Error>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        // Check if the phase is valid.

        let current_phase = match self.phases.get(self.next_phase_index) {
            Some(phase) => phase,
            None => {
                return Err(Error::Other("All phases already committed".to_string()));
            }
        };
        if phase != *current_phase {
            return Err(Error::Other(format!(
                "Committing invalid phase.  Expected {current_phase}, got {phase}",
            )));
        }

        let params = self.params;
        let meta = &self.pk.vk.cs;

        let mut rng = &mut self.rng;

        let advices = &mut self.advices;
        let challenges = &mut self.challenges;

        // Get the indices of the advice columns that are in the current phase.

        let column_indices = meta
            .advice_column_phase
            .iter()
            .enumerate()
            .filter_map(|(column_index, phase)| {
                if current_phase == phase {
                    Some(column_index)
                } else {
                    None
                }
            })
            .collect::<BTreeSet<_>>();

        if witness.len() != advices.len() {
            return Err(Error::Other("witness.len() != advice.len()".to_string()));
        }

        // Check all witness are consistent with the current phase.

        for witness_circuit in &witness {
            // Check contains all columns.
            if witness_circuit.len() != meta.num_advice_columns {
                return Err(Error::Other(format!(
                    "unexpected length in witness_circuitk.  Got {}, expected {}",
                    witness_circuit.len(),
                    meta.num_advice_columns,
                )));
            }
            // Check that all current_phase advice columns are Some, and their length is correct
            for (column_index, advice_column) in witness_circuit.iter().enumerate() {
                if column_indices.contains(&column_index) {
                    match advice_column {
                        None => {
                            return Err(Error::Other(format!(
                                "expected advice column with index {column_index} at phase {current_phase}",
                            )))
                        }
                        Some(advice_column) => {
                            if advice_column.len() != params.n() as usize {
                                return Err(Error::Other(format!(
                                    "expected advice column with index {} to have length {}",
                                    column_index,
                                    params.n(),
                                )));
                            }
                        }
                    }
                } else if advice_column.is_some() {
                    return Err(Error::Other(format!(
                        "expected no advice column with index {column_index} at phase {current_phase}",
                    )));
                };
            }
        }

        // commit_phase_fn fills advice columns (no defined as unblinded) with binding factors,
        // adding to the transcript its blinded affine commitments.
        // Also sets advice_polys with the (blinding) updated advice columns and advice_blinds with
        // the blinding factor used for each advice column.

        let mut commit_phase_fn = |advice: &mut AdviceSingle<Scheme::Curve, LagrangeCoeff>,
                                   witness: Vec<
            Option<Polynomial<Scheme::Scalar, LagrangeCoeff>>,
        >|
         -> Result<(), Error> {
            let unusable_rows_start = params.n() as usize - (meta.blinding_factors() + 1);
            let mut advice_values: Vec<_> = witness.into_iter().flatten().collect();
            let unblinded_advice: HashSet<usize> =
                HashSet::from_iter(meta.unblinded_advice_columns.clone());

            // Add blinding factors to advice columns.
            for (column_index, advice_values) in column_indices.iter().zip(&mut advice_values) {
                if !unblinded_advice.contains(column_index) {
                    for cell in &mut advice_values[unusable_rows_start..] {
                        *cell = Scheme::Scalar::random(&mut rng);
                    }
                } else {
                    #[cfg(feature = "sanity-checks")]
                    for cell in &advice_values[unusable_rows_start..] {
                        assert_eq!(*cell, Scheme::Scalar::ZERO);
                    }
                }
            }

            // Compute commitments to advice column polynomials
            let blinds: Vec<_> = column_indices
                .iter()
                .map(|i| {
                    if unblinded_advice.contains(i) {
                        Blind::default()
                    } else {
                        Blind(Scheme::Scalar::random(&mut rng))
                    }
                })
                .collect();
            let advice_commitments_projective: Vec<_> = advice_values
                .iter()
                .zip(blinds.iter())
                .map(|(poly, blind)| params.commit_lagrange(&self.engine.msm_backend, poly, *blind))
                .collect();
            let mut advice_commitments_affine =
                vec![Scheme::Curve::identity(); advice_commitments_projective.len()];
            <Scheme::Curve as CurveAffine>::CurveExt::batch_normalize(
                &advice_commitments_projective,
                &mut advice_commitments_affine,
            );
            let advice_commitments_affine = advice_commitments_affine;
            drop(advice_commitments_projective);

            // Update transcript.
            // [TRANSCRIPT-3]
            for commitment in &advice_commitments_affine {
                self.transcript.write_point(*commitment)?;
            }

            // Set advice_polys & advice_blinds
            for ((column_index, advice_values), blind) in
                column_indices.iter().zip(advice_values).zip(blinds)
            {
                advice.advice_polys[*column_index] = advice_values;
                advice.advice_blinds[*column_index] = blind;
            }
            Ok(())
        };

        // Update blindings for each advice column
        // [TRANSCRIPT-3]

        for (witness, advice) in witness.into_iter().zip(advices.iter_mut()) {
            commit_phase_fn(
                advice,
                witness
                    .into_iter()
                    .map(|v| v.map(Polynomial::new_lagrange_from_vec))
                    .collect(),
            )?;
        }

        // Squeeze the current transcript and get an new fresh challenge from the current phase.
        // [TRANSCRIPT-4]

        for (index, phase) in meta.challenge_phase.iter().enumerate() {
            if current_phase == phase {
                let existing =
                    challenges.insert(index, *self.transcript.squeeze_challenge_scalar::<()>());
                assert!(existing.is_none());
            }
        }

        // Move on

        self.next_phase_index += 1;
        Ok(challenges.clone())
    }

    /// Finalizes the proof creation.
    /// The following steps are performed:
    /// - 1. Generate committed lookup polys
    /// - 2. Generate committed permutation polys
    /// - 3. Generate committed lookup polys
    /// - 4. Generate committed shuffle polys
    /// - 5. Commit to the vanishing argument's random polynomial
    /// - 6. Generate the advice polys
    /// - 7. Evaluate the h(X) polynomial
    /// - 8. Construct the vanishing argument's h(X) commitments
    /// - 9. Compute x
    /// - 10. Compute and hash instance evals for the circuit instance
    /// - 11. Compute and hash fixed evals
    /// - 12. Evaluate permutation, lookups and shuffles at x
    /// - 13. Generate all queries ([`ProverQuery`])
    /// - 14. Send the queries to the [`Prover`]
    pub fn create_proof(mut self) -> Result<(), Error>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        let cs = &self.pk.vk.cs;
        assert_eq!(self.challenges.len(), cs.num_challenges);
        let challenges = (0..cs.num_challenges)
            .map(|index| self.challenges.remove(&index).unwrap())
            .collect::<Vec<_>>();

        // 1. Generate committed ( added to transcript ) lookup polys  ---------------------------------------

        // Sample theta challenge for keeping lookup columns linearly independent
        // [TRANSCRIPT-5]
        let theta: ChallengeTheta<_> = self.transcript.squeeze_challenge_scalar();

        // 2. Get permuted lookup polys
        // [TRANSCRIPT-6]
        let permuted_lookups = self.gen_permuted_lookups(theta, &challenges)?;

        // Sample beta challenge
        // [TRANSCRIPT-7]
        let beta: ChallengeBeta<_> = self.transcript.squeeze_challenge_scalar();

        // Sample gamma challenge
        // [TRANSCRIPT-8]
        let gamma: ChallengeGamma<_> = self.transcript.squeeze_challenge_scalar();

        // 2. Generate committed permutation polys  -----------------------------------------
        // [TRANSCRIPT-9]
        let permutations_committed = self.gen_committed_permutation_polys(beta, gamma)?;

        // 3. Generate committed lookup polys ----------------------------------------------------------
        // [TRANSCRIPT-10]
        let lookups_committed = self.gen_committed_lookups_polys(permuted_lookups, beta, gamma)?;

        // 4. Generate commited shuffle polys  -------------------------------------------------------
        // [TRANSCRIPT-11]
        let shuffles_committed = self.gen_committed_shuffles(theta, gamma, &challenges)?;

        // 5. Commit to the vanishing argument's random polynomial for blinding h(x_3) -------------------
        // [TRANSCRIPT-12]
        let vanishing_committed = self.gen_committed_vanishing()?;

        // 6. Generate the advice polys ------------------------------------------------------------------
        let advice = self.gen_advice_polys();

        // 7. Evaluate the h(X) polynomial -----------------------------------------------------------

        // Obtain challenge for keeping all separate gates linearly independent
        // [TRANSCRIPT-13]
        let y: ChallengeY<_> = self.transcript.squeeze_challenge_scalar();

        let h_poly = self.pk.ev.evaluate_h(
            self.pk,
            &advice
                .iter()
                .map(|a| a.advice_polys.as_slice())
                .collect::<Vec<_>>(),
            &self
                .instances
                .iter()
                .map(|i| i.instance_polys.as_slice())
                .collect::<Vec<_>>(),
            &challenges,
            *y,
            *beta,
            *gamma,
            *theta,
            &lookups_committed,
            &shuffles_committed,
            &permutations_committed,
        );

        // 8. Construct the vanishing argument's h(X) commitments --------------------------------------
        // [TRANSCRIPT-14]
        let vanishing = self.gen_constructed_vanishing(vanishing_committed, h_poly)?;

        // 9. Compute x  --------------------------------------------------------------------------------
        // [TRANSCRIPT-15]
        let x: ChallengeX<_> = self.transcript.squeeze_challenge_scalar();

        let x_pow_n = x.pow([self.params.n()]);

        // [TRANSCRIPT-16]
        self.write_instance_evals(x)?;

        // 10. Compute and hash advice evals for the circuit instance ------------------------------------
        // [TRANSCRIPT-17]
        self.write_advice_evals(x, &advice)?;

        // 11. Compute and hash fixed evals -----------------------------------------------------------

        // Hash each fixed column evaluation
        // [TRANSCRIPT-18]
        self.write_fixed_evals(x)?;

        // [TRANSCRIPT-19]
        let vanishing = vanishing.evaluate(x, x_pow_n, &self.pk.vk.domain, self.transcript)?;

        // 12. Evaluate permutation, lookups and shuffles at x -----------------------------------

        // Evaluate common permutation data
        // [TRANSCRIPT-20]
        self.pk.permutation.evaluate(x, self.transcript)?;

        // Evaluate the permutations, if any, at omega^i x.
        // [TRANSCRIPT-21]
        let permutations_evaluated = self.evaluate_permutations(x, permutations_committed)?;

        // Evaluate the lookups, if any, at omega^i x.
        // [TRANSCRIPT-22]
        let lookups_evaluated = self.evaluate_lookups(x, lookups_committed)?;

        // Evaluate the shuffles, if any, at omega^i x.
        // [TRANSCRIPT-23]
        let shuffles_evaluated = self.evaluate_shuffles(x, shuffles_committed)?;

        // 13. Generate all queries ([`ProverQuery`]) that needs to be sent to prover  --------------------
        let instances = std::mem::take(&mut self.instances);
        let queries = instances
            // group the instance, advice, permutation, lookups and shuffles
            .iter()
            .zip(advice.iter())
            .zip(permutations_evaluated.iter())
            .zip(lookups_evaluated.iter())
            .zip(shuffles_evaluated.iter())
            .flat_map(|((((instance, advice), permutation), lookups), shuffles)| {
                // Build a (an iterator) over a set of ProverQueries for each instance, advice, permutatiom, lookup and shuffle
                iter::empty()
                    // Instances
                    .chain(
                        P::QUERY_INSTANCE
                            .then_some(self.pk.vk.cs.instance_queries.iter().map(
                                move |&(column, at)| ProverQuery {
                                    point: self.pk.vk.domain.rotate_omega(*x, at),
                                    poly: &instance.instance_polys[column.index],
                                    blind: Blind::default(),
                                },
                            ))
                            .into_iter()
                            .flatten(),
                    )
                    // Advices
                    .chain(
                        self.pk
                            .vk
                            .cs
                            .advice_queries
                            .iter()
                            .map(move |&(column, at)| ProverQuery {
                                point: self.pk.vk.domain.rotate_omega(*x, at),
                                poly: &advice.advice_polys[column.index],
                                blind: advice.advice_blinds[column.index],
                            }),
                    )
                    // Permutations
                    .chain(permutation.open(self.pk, x))
                    // Lookups
                    .chain(lookups.iter().flat_map(move |p| p.open(self.pk, x)))
                    // Shuffles
                    .chain(shuffles.iter().flat_map(move |p| p.open(self.pk, x)))
            })
            // Queries to fixed columns
            .chain(
                self.pk
                    .vk
                    .cs
                    .fixed_queries
                    .iter()
                    .map(|&(column, at)| ProverQuery {
                        point: self.pk.vk.domain.rotate_omega(*x, at),
                        poly: &self.pk.fixed_polys[column.index],
                        blind: Blind::default(),
                    }),
            )
            // Copy constraints
            .chain(self.pk.permutation.open(x))
            // We query the h(X) polynomial at x
            .chain(vanishing.open(x));

        // 14. Send the queries to the [`Prover`]  ------------------------------------------------

        let prover = P::new(self.params);
        prover
            .create_proof_with_engine(&self.engine.msm_backend, self.rng, self.transcript, queries)
            .map_err(|_| Error::ConstraintSystemFailure)?;

        Ok(())
    }

    fn gen_permuted_lookups(
        &mut self,
        theta: ChallengeTheta<Scheme::Curve>,
        challenges: &[<Scheme as CommitmentScheme>::Scalar],
    ) -> Result<Vec<Vec<lookup::prover::Permuted<Scheme::Curve>>>, Error>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        let mut lookups_fn =
            |instance: &InstanceSingle<Scheme::Curve>,
             advice: &AdviceSingle<Scheme::Curve, LagrangeCoeff>|
             -> Result<Vec<lookup::prover::Permuted<Scheme::Curve>>, Error> {
                self.pk
                    .vk
                    .cs
                    .lookups
                    .iter()
                    .map(|lookup| {
                        lookup_commit_permuted(
                            &self.engine,
                            lookup,
                            self.pk,
                            self.params,
                            &self.pk.vk.domain,
                            theta,
                            &advice.advice_polys,
                            &self.pk.fixed_values,
                            &instance.instance_values,
                            challenges,
                            &mut self.rng,
                            self.transcript,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()
            };
        let permuted_lookups: Vec<Vec<lookup::prover::Permuted<Scheme::Curve>>> = self
            .instances
            .iter()
            .zip(self.advices.iter())
            .map(|(instance, advice)| -> Result<Vec<_>, Error> {
                // Construct and commit to permuted values for each lookup
                lookups_fn(instance, advice)
            })
            .collect::<Result<Vec<_>, _>>()?;

        Ok(permuted_lookups)
    }

    fn gen_committed_permutation_polys(
        &mut self,
        beta: ChallengeBeta<Scheme::Curve>,
        gamma: ChallengeGamma<Scheme::Curve>,
    ) -> Result<Vec<permutation::prover::Committed<Scheme::Curve>>, Error>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        let permutations_committed = self
            .instances
            .iter()
            .zip(self.advices.iter())
            .map(|(instance, advice)| {
                permutation_commit(
                    &self.engine,
                    &self.pk.vk.cs.permutation,
                    self.params,
                    self.pk,
                    &self.pk.permutation,
                    &advice.advice_polys,
                    &self.pk.fixed_values,
                    &instance.instance_values,
                    beta,
                    gamma,
                    &mut self.rng,
                    self.transcript,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(permutations_committed)
    }

    fn gen_committed_lookups_polys(
        &mut self,
        permuted_lookups: Vec<Vec<lookup::prover::Permuted<Scheme::Curve>>>,
        beta: ChallengeBeta<Scheme::Curve>,
        gamma: ChallengeGamma<Scheme::Curve>,
    ) -> Result<Vec<Vec<lookup::prover::Committed<Scheme::Curve>>>, Error>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        let lookups_committed: Vec<Vec<lookup::prover::Committed<Scheme::Curve>>> =
            permuted_lookups
                .into_iter()
                .map(|lookups| -> Result<Vec<_>, _> {
                    // Construct and commit to products for each lookup
                    lookups
                        .into_iter()
                        .map(|lookup| {
                            lookup.commit_product(
                                &self.engine,
                                self.pk,
                                self.params,
                                beta,
                                gamma,
                                &mut self.rng,
                                self.transcript,
                            )
                        })
                        .collect::<Result<Vec<_>, _>>()
                })
                .collect::<Result<Vec<_>, _>>()?;
        Ok(lookups_committed)
    }

    fn gen_committed_shuffles(
        &mut self,
        theta: ChallengeTheta<Scheme::Curve>,
        gamma: ChallengeGamma<Scheme::Curve>,
        challenges: &[<Scheme as CommitmentScheme>::Scalar],
    ) -> Result<Vec<Vec<shuffle::prover::Committed<Scheme::Curve>>>, Error>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        let shuffles_committed: Vec<Vec<shuffle::prover::Committed<Scheme::Curve>>> = self
            .instances
            .iter()
            .zip(self.advices.iter())
            .map(|(instance, advice)| -> Result<Vec<_>, _> {
                // Compress expressions for each shuffle
                self.pk
                    .vk
                    .cs
                    .shuffles
                    .iter()
                    .map(|shuffle| {
                        shuffle_commit_product(
                            &self.engine,
                            shuffle,
                            self.pk,
                            self.params,
                            &self.pk.vk.domain,
                            theta,
                            gamma,
                            &advice.advice_polys,
                            &self.pk.fixed_values,
                            &instance.instance_values,
                            challenges,
                            &mut self.rng,
                            self.transcript,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(shuffles_committed)
    }

    fn gen_committed_vanishing(
        &mut self,
    ) -> Result<vanishing::prover::Committed<Scheme::Curve>, Error> {
        let committed_vanishing = vanishing::Argument::commit(
            &self.engine.msm_backend,
            self.params,
            &self.pk.vk.domain,
            &mut self.rng,
            self.transcript,
        )?;
        Ok(committed_vanishing)
    }

    fn gen_advice_polys(&mut self) -> Vec<AdviceSingle<Scheme::Curve, Coeff>>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        let advices = std::mem::take(&mut self.advices);
        advices
            .into_iter()
            .map(
                |AdviceSingle {
                     advice_polys,
                     advice_blinds,
                 }| {
                    AdviceSingle {
                        advice_polys: advice_polys
                            .into_iter()
                            .map(|poly| self.pk.vk.domain.lagrange_to_coeff(poly))
                            .collect::<Vec<_>>(),
                        advice_blinds,
                    }
                },
            )
            .collect()
    }

    fn gen_constructed_vanishing(
        &mut self,
        vanishing: vanishing::prover::Committed<Scheme::Curve>,
        h_poly: Polynomial<
            <<Scheme as CommitmentScheme>::Curve as CurveAffine>::ScalarExt,
            crate::poly::ExtendedLagrangeCoeff,
        >,
    ) -> Result<vanishing::prover::Constructed<Scheme::Curve>, Error>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        let vanishing = vanishing.construct(
            &self.engine,
            self.params,
            &self.pk.vk.domain,
            h_poly,
            &mut self.rng,
            self.transcript,
        )?;
        Ok(vanishing)
    }

    fn write_instance_evals(&mut self, x: ChallengeX<Scheme::Curve>) -> Result<(), Error>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        if P::QUERY_INSTANCE {
            // Compute and hash instance evals for the circuit instance
            for instance in self.instances.iter() {
                // Evaluate polynomials at omega^i x
                let instance_evals: Vec<_> = self
                    .pk
                    .vk
                    .cs
                    .instance_queries
                    .iter()
                    .map(|&(column, at)| {
                        eval_polynomial(
                            &instance.instance_polys[column.index],
                            self.pk.vk.domain.rotate_omega(*x, at),
                        )
                    })
                    .collect();

                // Hash each instance column evaluation
                for eval in instance_evals.iter() {
                    self.transcript.write_scalar(*eval)?;
                }
            }
        }
        Ok(())
    }

    fn write_advice_evals(
        &mut self,
        x: ChallengeX<Scheme::Curve>,
        advice: &[AdviceSingle<Scheme::Curve, Coeff>],
    ) -> Result<(), Error>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        for advice in advice.iter() {
            // Evaluate polynomials at omega^i x
            let advice_evals: Vec<_> = self
                .pk
                .vk
                .cs
                .advice_queries
                .iter()
                .map(|&(column, at)| {
                    eval_polynomial(
                        &advice.advice_polys[column.index],
                        self.pk.vk.domain.rotate_omega(*x, at),
                    )
                })
                .collect();

            // Hash each advice column evaluation
            for eval in advice_evals.iter() {
                self.transcript.write_scalar(*eval)?;
            }
        }
        Ok(())
    }

    fn write_fixed_evals(&mut self, x: ChallengeX<Scheme::Curve>) -> Result<(), Error>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        let fixed_evals: Vec<_> = self
            .pk
            .vk
            .cs
            .fixed_queries
            .iter()
            .map(|&(column, at)| {
                eval_polynomial(
                    &self.pk.fixed_polys[column.index],
                    self.pk.vk.domain.rotate_omega(*x, at),
                )
            })
            .collect();

        // Hash each fixed column evaluation
        // [TRANSCRIPT-18]
        for eval in fixed_evals.iter() {
            self.transcript.write_scalar(*eval)?;
        }

        Ok(())
    }

    fn evaluate_permutations(
        &mut self,
        x: ChallengeX<Scheme::Curve>,
        permutations_committed: Vec<permutation::prover::Committed<Scheme::Curve>>,
    ) -> Result<Vec<permutation::prover::Evaluated<Scheme::Curve>>, Error>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        let permutations_evaluated: Vec<permutation::prover::Evaluated<Scheme::Curve>> =
            permutations_committed
                .into_iter()
                .map(|permutation| -> Result<_, _> {
                    permutation.evaluate(self.pk, x, self.transcript)
                })
                .collect::<Result<Vec<_>, _>>()?;
        Ok(permutations_evaluated)
    }

    fn evaluate_lookups(
        &mut self,
        x: ChallengeX<Scheme::Curve>,
        lookups_committed: Vec<Vec<lookup::prover::Committed<Scheme::Curve>>>,
    ) -> Result<Vec<Vec<lookup::prover::Evaluated<Scheme::Curve>>>, Error>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        let lookups_evaluated: Vec<Vec<lookup::prover::Evaluated<Scheme::Curve>>> =
            lookups_committed
                .into_iter()
                .map(|lookups| -> Result<Vec<_>, _> {
                    lookups
                        .into_iter()
                        .map(|p| p.evaluate(self.pk, x, self.transcript))
                        .collect::<Result<Vec<_>, _>>()
                })
                .collect::<Result<Vec<_>, _>>()?;

        Ok(lookups_evaluated)
    }

    fn evaluate_shuffles(
        &mut self,
        x: ChallengeX<Scheme::Curve>,
        shuffles_committed: Vec<Vec<shuffle::prover::Committed<Scheme::Curve>>>,
    ) -> Result<Vec<Vec<shuffle::prover::Evaluated<Scheme::Curve>>>, Error>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        let shuffles_evaluated: Vec<Vec<shuffle::prover::Evaluated<Scheme::Curve>>> =
            shuffles_committed
                .into_iter()
                .map(|shuffles| -> Result<Vec<_>, _> {
                    shuffles
                        .into_iter()
                        .map(|p| p.evaluate(self.pk, x, self.transcript))
                        .collect::<Result<Vec<_>, _>>()
                })
                .collect::<Result<Vec<_>, _>>()?;
        Ok(shuffles_evaluated)
    }

    /// Returns the phases of the circuit
    pub fn phases(&self) -> &[u8] {
        self.phases.as_slice()
    }

    /// Create a new prover object
    pub fn new(
        params: &'params Scheme::ParamsProver,
        pk: &'a ProvingKey<Scheme::Curve>,
        circuits_instances: &[Vec<Vec<Scheme::Scalar>>],
        rng: R,
        transcript: &'a mut T,
    ) -> Result<ProverMulti<'a, 'params, Scheme, P, E, R, T, H2cEngine>, Error>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    {
        let engine = PlonkEngineConfig::build_default();
        ProverMulti::new_with_engine(engine, params, pk, circuits_instances, rng, transcript)
    }
}
