use crate::transcript::{
    Hashable, Sampleable, TranscriptHash, BLAKE2B_PREFIX_CHALLENGE, BLAKE2B_PREFIX_COMMON,
};
use blake2b_simd::{Params, State as Blake2bState};
use ff::FromUniformBytes;
use group::GroupEncoding;
use halo2curves::bn256::{Fr, G1Affine};

impl TranscriptHash for Blake2bState {
    type Input = Vec<u8>;
    type Output = Vec<u8>;

    fn init() -> Self {
        Params::new()
            .hash_length(64)
            .key(b"Domain separator for transcript")
            .to_state()
    }

    fn absorb(&mut self, input: &Self::Input) -> &mut Self {
        self.update(&[BLAKE2B_PREFIX_COMMON]);
        self.update(input)
    }

    fn squeeze(&mut self) -> Self::Output {
        self.update(&[BLAKE2B_PREFIX_CHALLENGE]);
        self.finalize().as_bytes().to_vec()
    }
}

///////////////////////////////////////////////////
/// Implementation of Hashable for BN with Blake //
///////////////////////////////////////////////////

impl Hashable<Blake2bState> for G1Affine {
    fn to_input(&self) -> Vec<u8> {
        self.to_bytes().as_ref().to_vec()
    }
}

impl Hashable<Blake2bState> for Fr {
    fn to_input(&self) -> Vec<u8> {
        self.to_bytes().to_vec()
    }
}

impl Sampleable<Blake2bState> for Fr {
    fn sample(out: Vec<u8>) -> Self {
        assert!(out.len() <= 64);
        let mut bytes = [0u8; 64];
        bytes[..out.len()].copy_from_slice(&out);
        Fr::from_uniform_bytes(&bytes)
    }
}
