// Import the utility module from utils.rs
#[path = "utils.rs"]
mod utils;
use utils::{MyCircuit, OneNg};

use halo2_backend::transcript::{
    Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
};
use halo2_middleware::zal::impls::{H2cEngine, PlonkEngineConfig};
use halo2_proofs::plonk::{
    create_proof_custom_with_engine, keygen_pk_custom, keygen_vk_custom, verify_proof, Error,
};
use halo2_proofs::poly::commitment::ParamsProver;
use halo2_proofs::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
use halo2_proofs::poly::kzg::multiopen::{ProverSHPLONK, VerifierSHPLONK};
use halo2_proofs::poly::kzg::strategy::SingleStrategy;
use halo2curves::bn256::{Bn256, Fr, G1Affine};
use rand_core::block::BlockRng;

const K: u32 = 6;
const WIDTH_FACTOR: usize = 1;

fn test_mycircuit(
    vk_keygen_compress_selectors: bool,
    pk_keygen_compress_selectors: bool,
    proofgen_compress_selectors: bool,
) -> Result<(), Error> {
    let engine = PlonkEngineConfig::new()
        .set_curve::<G1Affine>()
        .set_msm(H2cEngine::new())
        .build();
    let k = K;
    let circuit: MyCircuit<Fr, WIDTH_FACTOR> = MyCircuit::new(k, 42);

    // Setup
    let mut rng = BlockRng::new(OneNg {});
    let params = ParamsKZG::<Bn256>::setup(k, &mut rng);
    let verifier_params = params.verifier_params();
    let vk = keygen_vk_custom(&params, &circuit, vk_keygen_compress_selectors)
        .expect("keygen_vk should not fail");
    let pk = keygen_pk_custom(&params, vk.clone(), &circuit, pk_keygen_compress_selectors)
        .expect("keygen_pk should not fail");

    // Proving
    let instances = circuit.instances();
    let instances_slice: &[&[Fr]] = &(instances
        .iter()
        .map(|instance| instance.as_slice())
        .collect::<Vec<_>>());

    let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);
    create_proof_custom_with_engine::<
        KZGCommitmentScheme<Bn256>,
        ProverSHPLONK<'_, Bn256>,
        _,
        _,
        _,
        _,
        _,
    >(
        engine,
        &params,
        &pk,
        proofgen_compress_selectors,
        &[circuit],
        &[instances_slice],
        &mut rng,
        &mut transcript,
    )?;
    let proof = transcript.finalize();

    // Verify
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
    .map_err(|e| Error::Backend(e))
}

#[test]
fn test_mycircuit_compress_selectors() {
    match test_mycircuit(true, true, true) {
        Ok(_) => println!("Success!"),
        Err(_) => panic!("Should succeed!"),
    }
    match test_mycircuit(false, false, false) {
        Ok(_) => println!("Success!"),
        Err(_) => panic!("Should succeed!"),
    }

    match test_mycircuit(false, true, true) {
        Ok(_) => panic!("Should fail!"),
        Err(_) => println!("Success!"),
    }
    match test_mycircuit(true, false, true) {
        Ok(_) => panic!("Should fail!"),
        Err(_) => println!("Success!"),
    }

    match test_mycircuit(false, false, true) {
        Ok(_) => panic!("Should fail!"),
        Err(_) => println!("Success!"),
    }
    match test_mycircuit(true, true, false) {
        Ok(_) => panic!("Should fail!"),
        Err(_) => println!("Success!"),
    }
}
