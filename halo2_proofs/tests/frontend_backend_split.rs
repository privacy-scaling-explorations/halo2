#![allow(clippy::many_single_char_names)]
#![allow(clippy::op_ref)]

#[cfg(feature = "heap-profiling")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

// Import the utility module from utils.rs
#[path = "utils.rs"]
mod utils;
use utils::{MyCircuit, OneNg};

use halo2_backend::{
    plonk::{
        keygen::{keygen_pk, keygen_vk},
        prover::ProverSingle,
        verifier::{verify_proof, verify_proof_single},
    },
    transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
    },
};
use halo2_frontend::{
    circuit::{
        compile_circuit, 
        WitnessCalculator,
    },
    dev::MockProver,
};
use halo2_proofs::poly::commitment::ParamsProver;
use std::collections::HashMap;


use halo2_proofs::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
use halo2_proofs::poly::kzg::multiopen::{ProverSHPLONK, VerifierSHPLONK};
use halo2_proofs::poly::kzg::strategy::SingleStrategy;
use halo2curves::bn256::{Bn256, Fr, G1Affine};
use rand_core::block::BlockRng;

#[test]
fn test_mycircuit_mock() {
    let k = 6;
    const WIDTH_FACTOR: usize = 2;
    let circuit: MyCircuit<Fr, WIDTH_FACTOR> = MyCircuit::new(k, 42);
    let instances = circuit.instances();
    let prover = MockProver::run(k, &circuit, instances).unwrap();
    prover.assert_satisfied();
}

use std::time::Instant;

const K: u32 = 6;
const WIDTH_FACTOR: usize = 1;

#[test]
fn test_mycircuit_full_legacy() {
    #[cfg(feature = "heap-profiling")]
    let _profiler = dhat::Profiler::new_heap();

    use halo2_proofs::plonk::{
        create_proof, keygen_pk as keygen_pk_legacy, keygen_vk as keygen_vk_legacy,
    };

    let k = K;
    let circuit: MyCircuit<Fr, WIDTH_FACTOR> = MyCircuit::new(k, 42);

    // Setup
    let mut rng = BlockRng::new(OneNg {});
    let params = ParamsKZG::<Bn256>::setup(k, &mut rng);
    let verifier_params = params.verifier_params();
    let start = Instant::now();
    let vk = keygen_vk_legacy(&params, &circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk_legacy(&params, vk.clone(), &circuit).expect("keygen_pk should not fail");
    println!("Keygen: {:?}", start.elapsed());

    // Proving
    let instances = circuit.instances();
    let instances_slice: &[&[Fr]] = &(instances
        .iter()
        .map(|instance| instance.as_slice())
        .collect::<Vec<_>>());

    let start = Instant::now();
    let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);
    create_proof::<KZGCommitmentScheme<Bn256>, ProverSHPLONK<'_, Bn256>, _, _, _, _>(
        &params,
        &pk,
        &[circuit],
        &[instances_slice],
        &mut rng,
        &mut transcript,
    )
    .expect("proof generation should not fail");
    let proof = transcript.finalize();
    println!("Prove: {:?}", start.elapsed());

    // Verify
    let start = Instant::now();
    let mut verifier_transcript =
        Blake2bRead::<_, G1Affine, Challenge255<_>>::init(proof.as_slice());
    let strategy = SingleStrategy::new(verifier_params);

    verify_proof::<KZGCommitmentScheme<Bn256>, VerifierSHPLONK<'_, Bn256>, _, _, _>(
        &params,
        &vk,
        strategy,
        &[instances_slice],
        &mut verifier_transcript,
    )
    .expect("verify succeeds");
    println!("Verify: {:?}", start.elapsed());
}

#[test]
fn test_mycircuit_full_split() {
    use halo2_middleware::zal::impls::{H2cEngine, PlonkEngineConfig};

    #[cfg(feature = "heap-profiling")]
    let _profiler = dhat::Profiler::new_heap();

    let engine = PlonkEngineConfig::new()
        .set_curve::<G1Affine>()
        .set_msm(H2cEngine::new())
        .build();
    let k = K;
    let circuit: MyCircuit<Fr, WIDTH_FACTOR> = MyCircuit::new(k, 42);
    let (compiled_circuit, config, cs) = compile_circuit(k, &circuit, false).unwrap();

    // Setup
    let mut rng = BlockRng::new(OneNg {});
    let params = ParamsKZG::<Bn256>::setup(k, &mut rng);
    let verifier_params = params.verifier_params();
    let start = Instant::now();
    let vk = keygen_vk(&params, &compiled_circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk.clone(), &compiled_circuit).expect("keygen_pk should not fail");
    println!("Keygen: {:?}", start.elapsed());
    drop(compiled_circuit);

    // Proving
    println!("Proving...");
    let instances = circuit.instances();
    let instances_slice: &[&[Fr]] = &(instances
        .iter()
        .map(|instance| instance.as_slice())
        .collect::<Vec<_>>());

    let start = Instant::now();
    let mut witness_calc = WitnessCalculator::new(k, &circuit, &config, &cs, instances_slice);
    let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);
    let mut prover = ProverSingle::<
        KZGCommitmentScheme<Bn256>,
        ProverSHPLONK<'_, Bn256>,
        _,
        _,
        _,
        _,
    >::new_with_engine(
        engine,
        &params,
        &pk,
        instances_slice,
        &mut rng,
        &mut transcript,
    )
    .unwrap();
    let mut challenges = HashMap::new();
    for phase in 0..cs.phases().count() {
        println!("phase {phase}");
        let witness = witness_calc.calc(phase as u8, &challenges).unwrap();
        challenges = prover.commit_phase(phase as u8, witness).unwrap();
    }
    prover.create_proof().unwrap();
    let proof = transcript.finalize();
    println!("Prove: {:?}", start.elapsed());

    // Verify
    let start = Instant::now();
    println!("Verifying...");
    let mut verifier_transcript =
        Blake2bRead::<_, G1Affine, Challenge255<_>>::init(proof.as_slice());
    let strategy = SingleStrategy::new(verifier_params);

    verify_proof_single::<KZGCommitmentScheme<Bn256>, VerifierSHPLONK<'_, Bn256>, _, _, _>(
        &params,
        &vk,
        strategy,
        instances_slice,
        &mut verifier_transcript,
    )
    .expect("verify succeeds");
    println!("Verify: {:?}", start.elapsed());
}
