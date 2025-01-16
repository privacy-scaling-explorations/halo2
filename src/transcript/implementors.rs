use crate::transcript::{
    Hashable, Sampleable, TranscriptHash, BLAKE2B_PREFIX_CHALLENGE, BLAKE2B_PREFIX_COMMON,
};
use blake2b_simd::{Params, State as Blake2bState};
use ff::{FromUniformBytes, PrimeField};
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
    /// Converts it to compressed form in bytes
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
    fn sample(hash_output: Vec<u8>) -> Self {
        assert!(hash_output.len() <= 64);
        let mut bytes = [0u8; 64];
        bytes[..hash_output.len()].copy_from_slice(&hash_output);
        Fr::from_uniform_bytes(&bytes)
    }
}

//////////////////////////////////////////////////////////
/// Implementation of Hashable for BLS12-381 with Blake //
//////////////////////////////////////////////////////////

impl Hashable<Blake2bState> for blstrs::G1Affine {
    /// Converts it to compressed form in bytes
    fn to_input(&self) -> Vec<u8> {
        self.to_bytes().as_ref().to_vec()
    }
}

impl Hashable<Blake2bState> for blstrs::Scalar {
    fn to_input(&self) -> Vec<u8> {
        self.to_repr().to_vec()
    }
}

impl Sampleable<Blake2bState> for blstrs::Scalar {
    fn sample(hash_output: Vec<u8>) -> Self {
        assert!(hash_output.len() <= 64);
        assert!(hash_output.len() >= (blstrs::Scalar::NUM_BITS as usize / 8) + 12);
        let mut bytes = [0u8; 64];
        bytes[..hash_output.len()].copy_from_slice(&hash_output);
        blstrs::Scalar::from_uniform_bytes(&bytes)
    }
}

impl Hashable<Blake2bState> for halo2curves::bls12381::G1Affine {
    /// Converts it to compressed form in bytes
    fn to_input(&self) -> Vec<u8> {
        self.to_bytes().as_ref().to_vec()
    }
}

impl Hashable<Blake2bState> for halo2curves::bls12381::Fr {
    fn to_input(&self) -> Vec<u8> {
        self.to_repr().as_ref().to_vec()
    }
}

impl Sampleable<Blake2bState> for halo2curves::bls12381::Fr {
    fn sample(hash_output: Vec<u8>) -> Self {
        assert!(hash_output.len() <= 64);
        let mut bytes = [0u8; 64];
        bytes[..hash_output.len()].copy_from_slice(&hash_output);
        halo2curves::bls12381::Fr::from_uniform_bytes(&bytes)
    }
}
