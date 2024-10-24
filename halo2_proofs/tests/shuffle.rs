use ff::{BatchInvert, FromUniformBytes};
use halo2_debug::test_rng;
use halo2_proofs::{
    arithmetic::Field,
    circuit::{floor_planner::V1, Layouter, Value},
    dev::{metadata, FailureLocation, MockProver, VerifyFailure},
    plonk::*,
    poly::kzg::{
        commitment::{KZGCommitmentScheme, ParamsKZG},
        multiopen::{ProverSHPLONK, VerifierSHPLONK},
        strategy::SingleStrategy,
    },
    transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
    },
};
use halo2curves::bn256::{Bn256, Fr, G1Affine};
use rand_core::RngCore;
use std::iter;

fn rand_2d_array<F: Field, R: RngCore, const W: usize, const H: usize>(rng: &mut R) -> [[F; H]; W] {
    [(); W].map(|_| [(); H].map(|_| F::random(&mut *rng)))
}

fn shuffled<F: Field, R: RngCore, const W: usize, const H: usize>(
    original: [[F; H]; W],
    rng: &mut R,
) -> [[F; H]; W] {
    let mut shuffled = original;

    for row in (1..H).rev() {
        let rand_row = (rng.next_u32() as usize) % row;
        for column in shuffled.iter_mut() {
            column.swap(row, rand_row);
        }
    }

    shuffled
}

#[derive(Clone)]
struct MyConfig<const W: usize> {
    q_shuffle: Selector,
    q_first: Selector,
    q_last: Selector,
    original: [Column<Advice>; W],
    shuffled: [Column<Advice>; W],
    theta: Challenge,
    gamma: Challenge,
    z: Column<Advice>,
}

impl<const W: usize> MyConfig<W> {
    fn configure<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        let [q_shuffle, q_first, q_last] = [(); 3].map(|_| meta.selector());
        // First phase
        let original = [(); W].map(|_| meta.advice_column_in(FirstPhase));
        let shuffled = [(); W].map(|_| meta.advice_column_in(FirstPhase));
        let [theta, gamma] = [(); 2].map(|_| meta.challenge_usable_after(FirstPhase));
        // Second phase
        let z = meta.advice_column_in(SecondPhase);

        meta.create_gate("z should start with 1", |_| {
            let one = Expression::Constant(F::ONE);

            vec![q_first.expr() * (one - z.cur())]
        });

        meta.create_gate("z should end with 1", |_| {
            let one = Expression::Constant(F::ONE);

            vec![q_last.expr() * (one - z.cur())]
        });

        meta.create_gate("z should have valid transition", |_| {
            let q_shuffle = q_shuffle.expr();
            let original = original.map(|advice| advice.cur());
            let shuffled = shuffled.map(|advice| advice.cur());
            let [theta, gamma] = [theta, gamma].map(|challenge| challenge.expr());

            // Compress
            let original = original
                .iter()
                .cloned()
                .reduce(|acc, a| acc * theta.clone() + a)
                .unwrap();
            let shuffled = shuffled
                .iter()
                .cloned()
                .reduce(|acc, a| acc * theta.clone() + a)
                .unwrap();

            vec![q_shuffle * (z.cur() * (original + gamma.clone()) - z.next() * (shuffled + gamma))]
        });

        Self {
            q_shuffle,
            q_first,
            q_last,
            original,
            shuffled,
            theta,
            gamma,
            z,
        }
    }
}

#[derive(Clone, Default)]
struct MyCircuit<F: Field, const W: usize, const H: usize> {
    original: Value<[[F; H]; W]>,
    shuffled: Value<[[F; H]; W]>,
}

impl<F: Field, const W: usize, const H: usize> MyCircuit<F, W, H> {
    fn rand<R: RngCore>(rng: &mut R) -> Self {
        let original = rand_2d_array::<F, _, W, H>(rng);
        let shuffled = shuffled(original, rng);

        Self {
            original: Value::known(original),
            shuffled: Value::known(shuffled),
        }
    }
}

impl<F: Field, const W: usize, const H: usize> Circuit<F> for MyCircuit<F, W, H> {
    type Config = MyConfig<W>;
    type FloorPlanner = V1;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        MyConfig::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), ErrorFront> {
        let theta = layouter.get_challenge(config.theta);
        let gamma = layouter.get_challenge(config.gamma);

        layouter.assign_region(
            || "Shuffle original into shuffled",
            |mut region| {
                // Keygen
                config.q_first.enable(&mut region, 0)?;
                config.q_last.enable(&mut region, H)?;
                for offset in 0..H {
                    config.q_shuffle.enable(&mut region, offset)?;
                }

                // First phase
                for (idx, (&column, values)) in config
                    .original
                    .iter()
                    .zip(self.original.transpose_array().iter())
                    .enumerate()
                {
                    for (offset, &value) in values.transpose_array().iter().enumerate() {
                        region.assign_advice(
                            || format!("original[{idx}][{offset}]"),
                            column,
                            offset,
                            || value,
                        )?;
                    }
                }
                for (idx, (&column, values)) in config
                    .shuffled
                    .iter()
                    .zip(self.shuffled.transpose_array().iter())
                    .enumerate()
                {
                    for (offset, &value) in values.transpose_array().iter().enumerate() {
                        region.assign_advice(
                            || format!("shuffled[{idx}][{offset}]"),
                            column,
                            offset,
                            || value,
                        )?;
                    }
                }

                // Second phase
                let z = self.original.zip(self.shuffled).zip(theta).zip(gamma).map(
                    |(((original, shuffled), theta), gamma)| {
                        let mut product = vec![F::ZERO; H];
                        for (idx, product) in product.iter_mut().enumerate() {
                            let mut compressed = F::ZERO;
                            for value in shuffled.iter() {
                                compressed *= theta;
                                compressed += value[idx];
                            }

                            *product = compressed + gamma
                        }

                        product.iter_mut().batch_invert();

                        for (idx, product) in product.iter_mut().enumerate() {
                            let mut compressed = F::ZERO;
                            for value in original.iter() {
                                compressed *= theta;
                                compressed += value[idx];
                            }

                            *product *= compressed + gamma
                        }

                        #[allow(clippy::let_and_return)]
                        let z = iter::once(F::ONE)
                            .chain(product)
                            .scan(F::ONE, |state, cur| {
                                *state *= &cur;
                                Some(*state)
                            })
                            .collect::<Vec<_>>();

                        #[cfg(feature = "sanity-checks")]
                        assert_eq!(F::ONE, *z.last().unwrap());

                        z
                    },
                );
                for (offset, value) in z.transpose_vec(H + 1).into_iter().enumerate() {
                    region.assign_advice(|| format!("z[{offset}]"), config.z, offset, || value)?;
                }

                Ok(())
            },
        )
    }
}

fn test_mock_prover<F: Ord + FromUniformBytes<64>, const W: usize, const H: usize>(
    k: u32,
    circuit: MyCircuit<F, W, H>,
    expected: Result<(), Vec<(metadata::Constraint, FailureLocation)>>,
) {
    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    match (prover.verify(), expected) {
        (Ok(_), Ok(_)) => {}
        (Err(err), Err(expected)) => {
            assert_eq!(
                err.into_iter()
                    .map(|failure| match failure {
                        VerifyFailure::ConstraintNotSatisfied {
                            constraint,
                            location,
                            ..
                        } => (constraint, location),
                        _ => panic!("MockProver::verify has result unmatching expected"),
                    })
                    .collect::<Vec<_>>(),
                expected
            )
        }
        (_, _) => panic!("MockProver::verify has result unmatching expected"),
    };
}

fn test_prover<const W: usize, const H: usize>(
    k: u32,
    circuit: MyCircuit<Fr, W, H>,
    expected: bool,
) -> Vec<u8> {
    let instances = vec![vec![]];

    // Setup
    let mut rng = test_rng();
    let params = ParamsKZG::<Bn256>::setup(k, &mut rng);
    let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk.clone(), &circuit).expect("keygen_pk should not fail");

    let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);
    create_proof::<KZGCommitmentScheme<Bn256>, ProverSHPLONK<'_, Bn256>, _, _, _, _>(
        &params,
        &pk,
        &[circuit],
        &instances,
        &mut rng,
        &mut transcript,
    )
    .expect("proof generation should not fail");
    let proof = transcript.finalize();

    // Verify
    let mut verifier_transcript =
        Blake2bRead::<_, G1Affine, Challenge255<_>>::init(proof.as_slice());
    let verifier_params = params.verifier_params();

    let accepted = verify_proof_multi::<
        KZGCommitmentScheme<Bn256>,
        VerifierSHPLONK<Bn256>,
        _,
        _,
        SingleStrategy<_>,
    >(
        &verifier_params,
        &vk,
        instances.as_slice(),
        &mut verifier_transcript,
    );

    assert_eq!(accepted, expected);

    proof
}

#[test]
fn test_shuffle() {
    const W: usize = 4;
    const H: usize = 32;
    const K: u32 = 8;

    let circuit = &MyCircuit::<_, W, H>::rand(&mut test_rng());

    test_mock_prover(K, circuit.clone(), Ok(()));

    halo2_debug::test_result(
        || test_prover::<W, H>(K, circuit.clone(), true),
        "2a91b131950f5c9d9bf8d6486caf3870edcdb772d0021bead607076497762fac",
    );

    #[cfg(not(feature = "sanity-checks"))]
    {
        use std::ops::IndexMut;

        let mut circuit = circuit.clone();
        circuit.shuffled = circuit.shuffled.map(|mut shuffled| {
            shuffled.index_mut(0).swap(0, 1);
            shuffled
        });

        test_mock_prover(
            K,
            circuit.clone(),
            Err(vec![(
                ((1, "z should end with 1").into(), 0, "").into(),
                FailureLocation::InRegion {
                    region: (0, "Shuffle original into shuffled").into(),
                    offset: 32,
                },
            )]),
        );
        halo2_debug::test_result(
            || test_prover::<W, H>(K, circuit.clone(), false),
            "e3702897ecf9e9ea052887184fae88e499ed34669e8861c5b2e53c2f1d54e055",
        );
    }
}
