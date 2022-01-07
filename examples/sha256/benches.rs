use halo2::{
    circuit::{Layouter, SimpleFloorPlanner},
    plonk::{
        create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, ConstraintSystem, Error,
        VerifyingKey,
    },
    poly::commitment::{Params, ParamsVerifier, Setup},
    transcript::{Blake2bRead, Blake2bWrite, Challenge255},
};
use rand::rngs::OsRng;

use pairing::bn256::Fr as Fp;
use pairing::bn256::{Bn256, G1Affine};
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;

use std::{
    fs::File,
    io::{prelude::*, BufReader},
    path::Path,
};

use criterion::{criterion_group, criterion_main, Criterion};

use crate::{BlockWord, Sha256, Table16Chip, Table16Config, BLOCK_SIZE};

#[allow(dead_code)]
fn bench(name: &str, k: u32, c: &mut Criterion) {
    #[derive(Default)]
    struct MyCircuit {}

    impl Circuit<Fp> for MyCircuit {
        type Config = Table16Config;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
            Table16Chip::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fp>,
        ) -> Result<(), Error> {
            Table16Chip::load(config.clone(), &mut layouter)?;
            let table16_chip = Table16Chip::construct(config);

            // Test vector: "abc"
            let test_input = [
                BlockWord(Some(0b01100001011000100110001110000000)),
                BlockWord(Some(0b00000000000000000000000000000000)),
                BlockWord(Some(0b00000000000000000000000000000000)),
                BlockWord(Some(0b00000000000000000000000000000000)),
                BlockWord(Some(0b00000000000000000000000000000000)),
                BlockWord(Some(0b00000000000000000000000000000000)),
                BlockWord(Some(0b00000000000000000000000000000000)),
                BlockWord(Some(0b00000000000000000000000000000000)),
                BlockWord(Some(0b00000000000000000000000000000000)),
                BlockWord(Some(0b00000000000000000000000000000000)),
                BlockWord(Some(0b00000000000000000000000000000000)),
                BlockWord(Some(0b00000000000000000000000000000000)),
                BlockWord(Some(0b00000000000000000000000000000000)),
                BlockWord(Some(0b00000000000000000000000000000000)),
                BlockWord(Some(0b00000000000000000000000000000000)),
                BlockWord(Some(0b00000000000000000000000000011000)),
            ];

            // Create a message of length 31 blocks
            let mut input = Vec::with_capacity(31 * BLOCK_SIZE);
            for _ in 0..31 {
                input.extend_from_slice(&test_input);
            }

            Sha256::digest(table16_chip, layouter.namespace(|| "'abc' * 2"), &input)?;

            Ok(())
        }
    }

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    // Initialize the polynomial commitment parameters
    let params_path = Path::new("./benches/sha256_assets/sha256_params");
    if File::open(&params_path).is_err() {
        let params = Setup::<Bn256>::new(k, &mut rng);

        let mut buf = Vec::new();

        params.write(&mut buf).expect("Failed to write params");
        let mut file = File::create(&params_path).expect("Failed to create sha256_params");

        file.write_all(&buf[..])
            .expect("Failed to write params to file");
    }

    let params_fs = File::open(&params_path).expect("couldn't load sha256_params");
    let params: Params<G1Affine> =
        Params::read::<_>(&mut BufReader::new(params_fs)).expect("Failed to read params");

    let params_verifier_path = Path::new("./benches/sha256_assets/sha256_verifier_params");
    if File::open(&params_verifier_path).is_err() {
        let params_verifier = Setup::<Bn256>::verifier_params(&params, 0).unwrap();

        let mut buf = Vec::new();

        params_verifier
            .write(&mut buf)
            .expect("Failed to write params");
        let mut file = File::create(&params_verifier_path).expect("Failed to create sha256_params");

        file.write_all(&buf[..])
            .expect("Failed to write params to file");
    }

    let params_fs = File::open(&params_verifier_path).expect("couldn't load sha256_params");
    let params_verifier: ParamsVerifier<Bn256> =
        ParamsVerifier::read::<_>(&mut BufReader::new(params_fs)).expect("Failed to read params");

    let empty_circuit: MyCircuit = MyCircuit {};

    // Initialize the proving key
    let vk_path = Path::new("./benches/sha256_assets/sha256_vk");
    if File::open(&vk_path).is_err() {
        let vk = keygen_vk(&params, &empty_circuit).expect("keygen_vk should not fail");
        let mut buf = Vec::new();

        vk.write(&mut buf).expect("Failed to write vk");
        let mut file = File::create(&vk_path).expect("Failed to create sha256_vk");

        file.write_all(&buf[..])
            .expect("Failed to write vk to file");
    }

    let vk_fs = File::open(&vk_path).expect("couldn't load sha256_vk");
    let vk: VerifyingKey<G1Affine> =
        VerifyingKey::<G1Affine>::read::<_, MyCircuit>(&mut BufReader::new(vk_fs), &params)
            .expect("Failed to read vk");

    let pk = keygen_pk(&params, vk, &empty_circuit).expect("keygen_pk should not fail");

    let circuit: MyCircuit = MyCircuit {};

    // let prover_name = name.to_string() + "-prover";
    let verifier_name = name.to_string() + "-verifier";

    // /// Benchmark proof creation
    // c.bench_function(&prover_name, |b| {
    //     b.iter(|| {
    //         let mut transcript = Blake2bWrite::init(Fq::one());
    //         create_proof(&params, &pk, &circuit, &[], &mut transcript)
    //             .expect("proof generation should not fail");
    //         let proof: Vec<u8> = transcript.finalize();
    //     });
    // });

    // Create a proof
    let proof_path = Path::new("./benches/sha256_assets/sha256_proof");
    if File::open(&proof_path).is_err() {
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof(&params, &pk, &[circuit], &[], OsRng, &mut transcript)
            .expect("proof generation should not fail");
        let proof: Vec<u8> = transcript.finalize();
        let mut file = File::create(&proof_path).expect("Failed to create sha256_proof");
        file.write_all(&proof[..]).expect("Failed to write proof");
    }

    let mut proof_fs = File::open(&proof_path).expect("couldn't load sha256_proof");
    let mut proof = Vec::<u8>::new();
    proof_fs
        .read_to_end(&mut proof)
        .expect("Couldn't read proof");

    c.bench_function(&verifier_name, |b| {
        b.iter(|| {
            let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
            assert!(bool::from(
                verify_proof(&params_verifier, pk.get_vk(), &[], &mut transcript).unwrap()
            ));
        });
    });
}

#[allow(dead_code)]
fn criterion_benchmark(c: &mut Criterion) {
    bench("sha256", 17, c);
    // bench("sha256", 20, c);
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
