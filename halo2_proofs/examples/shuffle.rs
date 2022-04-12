use ff::BatchInvert;
use halo2_proofs::{
    arithmetic::{FieldExt, MultiMillerLoop},
    circuit::{Layouter, SimpleFloorPlanner},
    dev::{MockProver, VerifyFailure},
    plonk::*,
    poly::{
        commitment::{Params, ParamsVerifier},
        Rotation,
    },
    transcript::{Blake2bRead, Blake2bWrite, Challenge255},
};
use pairing::bn256::Bn256;
use rand::{rngs::StdRng, Rng, SeedableRng};
use rand_core::OsRng;
use std::{iter, marker::PhantomData};

fn rand_2d_array<F: FieldExt, R: Rng, const W: usize, const H: usize>(rng: &mut R) -> [[F; H]; W] {
    [(); W].map(|_| [(); H].map(|_| F::random(&mut *rng)))
}

fn shuffled<F: FieldExt, R: Rng, const W: usize, const H: usize>(
    original: [[F; H]; W],
    rng: &mut R,
) -> [[F; H]; W] {
    let mut shuffled = original;

    for row in (1..H).rev() {
        let rand_row = rng.gen_range(0..=row);
        for column in shuffled.iter_mut() {
            column.swap(row, rand_row);
        }
    }

    shuffled
}

#[derive(Clone)]
struct MyConfig<F, const W: usize> {
    q_shuffle: Selector,
    q_first: Selector,
    q_last: Selector,
    original: [Column<Advice>; W],
    shuffled: [Column<Advice>; W],
    theta: Challenge,
    gamma: Challenge,
    z: Column<Advice>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const W: usize> MyConfig<F, W> {
    fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        // Round 0
        let [q_shuffle, q_first, q_last] = [(); 3].map(|_| meta.selector());
        // Round 1
        let original = [(); W].map(|_| meta.advice_column());
        let shuffled = [(); W].map(|_| meta.advice_column());
        let [theta, gamma] = [(); 2].map(|_| meta.challenge());
        // Round 2
        let z = meta.advice_column();

        meta.create_gate("z should start with 1", |meta| {
            let q_first = meta.query_selector(q_first);
            let z = meta.query_advice(z, Rotation::cur());
            let one = Expression::Constant(F::one());

            vec![q_first * (one - z)]
        });

        meta.create_gate("z should end with 1", |meta| {
            let q_last = meta.query_selector(q_last);
            let z = meta.query_advice(z, Rotation::cur());
            let one = Expression::Constant(F::one());

            vec![q_last * (one - z)]
        });

        meta.create_gate("z should have valid transition", |meta| {
            let q_shuffle = meta.query_selector(q_shuffle);
            let original = original.map(|advice| meta.query_advice(advice, Rotation::cur()));
            let shuffled = shuffled.map(|advice| meta.query_advice(advice, Rotation::cur()));
            let [theta, gamma] = [theta, gamma].map(|challenge| meta.query_challenge(challenge));
            let [z, z_w] =
                [Rotation::cur(), Rotation::next()].map(|rotation| meta.query_advice(z, rotation));

            // compress
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

            vec![q_shuffle * (z * (original + gamma.clone()) - z_w * (shuffled + gamma))]
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
            _marker: PhantomData,
        }
    }
}

#[derive(Clone, Default)]
struct MyCircuit<F: FieldExt, const W: usize, const H: usize> {
    original: Option<[[F; H]; W]>,
    shuffled: Option<[[F; H]; W]>,
}

impl<F: FieldExt, const W: usize, const H: usize> MyCircuit<F, W, H> {
    fn rand<R: Rng>(rng: &mut R) -> Self {
        let original = rand_2d_array::<F, _, W, H>(rng);
        let shuffled = shuffled(original, rng);

        Self {
            original: Some(original),
            shuffled: Some(shuffled),
        }
    }
}

impl<F: FieldExt, const W: usize, const H: usize> Circuit<F> for MyCircuit<F, W, H> {
    type Config = MyConfig<F, W>;
    type FloorPlanner = SimpleFloorPlanner;

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
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "Shuffle original into shuffled",
            |mut region| {
                // Keygen (Round 0)
                config.q_first.enable(&mut region, 0)?;
                config.q_last.enable(&mut region, H)?;
                for offset in 0..H {
                    config.q_shuffle.enable(&mut region, offset)?;
                }

                // Round 1
                if let (Some(original), Some(shuffled)) = (&self.original, &self.shuffled) {
                    for (idx, (&column, value)) in
                        config.original.iter().zip(original.iter()).enumerate()
                    {
                        for (offset, &value) in value.iter().enumerate() {
                            region.assign_advice(
                                || format!("original[{}]", idx),
                                column,
                                offset,
                                || Ok(value),
                            )?;
                        }
                    }
                    for (idx, (&column, value)) in
                        config.shuffled.iter().zip(shuffled.iter()).enumerate()
                    {
                        for (offset, &value) in value.iter().enumerate() {
                            region.assign_advice(
                                || format!("shuffled[{}]", idx),
                                column,
                                offset,
                                || Ok(value),
                            )?;
                        }
                    }
                }

                // Round 2
                if let (Some(theta), Some(gamma), Some(original), Some(shuffled)) = (
                    region.query_challenge(config.theta)?,
                    region.query_challenge(config.gamma)?,
                    &self.original,
                    &self.shuffled,
                ) {
                    let mut product = vec![F::zero(); H];
                    for (idx, product) in product.iter_mut().enumerate() {
                        let mut compressed = F::zero();
                        for value in shuffled.iter() {
                            compressed *= theta;
                            compressed += value[idx];
                        }

                        *product = compressed + gamma
                    }

                    product.iter_mut().batch_invert();

                    for (idx, product) in product.iter_mut().enumerate() {
                        let mut compressed = F::zero();
                        for value in original.iter() {
                            compressed *= theta;
                            compressed += value[idx];
                        }

                        *product *= compressed + gamma
                    }

                    let z = iter::once(F::one())
                        .chain(product)
                        .scan(F::one(), |state, cur| {
                            *state *= &cur;
                            Some(*state)
                        })
                        .take(H + 1)
                        .collect::<Vec<_>>();

                    #[cfg(feature = "sanity-checks")]
                    assert_eq!(F::one(), *z.last().unwrap());

                    for (offset, &value) in z.iter().enumerate() {
                        region.assign_advice(|| "Grand product", config.z, offset, || Ok(value))?;
                    }
                }

                Ok(())
            },
        )
    }
}

fn test_mock_prover<F: FieldExt, const W: usize, const H: usize>(
    k: u32,
    circuit: MyCircuit<F, W, H>,
    expected: Result<(), Vec<VerifyFailure>>,
) {
    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    assert_eq!(prover.verify(), expected);
}

fn test_prover<C: MultiMillerLoop, const W: usize, const H: usize>(
    k: u32,
    circuit: MyCircuit<C::Scalar, W, H>,
    expected: bool,
) {
    let params: Params<C::G1Affine> = Params::<C::G1Affine>::unsafe_setup::<C>(k);
    let params_verifier: ParamsVerifier<C> = params.verifier(0).unwrap();

    let vk = keygen_vk(&params, &MyCircuit::<C::Scalar, W, H>::default()).unwrap();
    let pk = keygen_pk(&params, vk, &MyCircuit::<C::Scalar, W, H>::default()).unwrap();

    let proof = {
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

        create_proof(&params, &pk, &[circuit], &[&[]], OsRng, &mut transcript)
            .expect("proof generation should not fail");

        transcript.finalize()
    };

    let accepted = {
        let strategy = SingleVerifier::new(&params_verifier);
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);

        verify_proof(
            &params_verifier,
            pk.get_vk(),
            strategy,
            &[&[]],
            &mut transcript,
        )
        .is_ok()
    };

    assert_eq!(accepted, expected);
}

fn main() {
    const W: usize = 4;
    const H: usize = 32;
    const K: u32 = 8;

    let mut rng = StdRng::from_seed([
        5, 77, 48, 115, 120, 129, 86, 16, 166, 157, 124, 134, 199, 233, 248, 174, //
        105, 136, 137, 241, 61, 39, 252, 57, 31, 208, 170, 133, 166, 169, 184, 11,
    ]);
    let circuit = &MyCircuit::<_, W, H>::rand(&mut rng);

    {
        test_mock_prover(K, circuit.clone(), Ok(()));
        test_prover::<Bn256, W, H>(K, circuit.clone(), true);
    }

    #[cfg(not(feature = "sanity-checks"))]
    {
        use halo2_proofs::dev::FailureLocation;
        use std::ops::IndexMut;

        let mut circuit = circuit.clone();
        circuit.shuffled.as_mut().unwrap().index_mut(0).swap(0, 1);

        test_mock_prover(
            K,
            circuit.clone(),
            Err(vec![VerifyFailure::ConstraintNotSatisfied {
                constraint: ((1, "z should end with 1").into(), 0, "").into(),
                location: FailureLocation::InRegion {
                    region: (0, "Shuffle original into shuffled").into(),
                    offset: 32,
                },
                cell_values: vec![(
                    ((Any::Advice, 8).into(), 0).into(),
                    "0x608d5ce5ebdeff516eb21e242ed4926777f1675c883438a84a94d859fb93907".to_string(),
                )],
            }]),
        );
        test_prover::<Bn256, W, H>(K, circuit, false);
    }
}
