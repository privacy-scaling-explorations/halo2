//! This module contains utilities and traits for dealing with Fiat-Shamir
//! transcripts.
use blake2b_simd::{Params, State as Blake2bState};

use ff::FromUniformBytes;
use group::GroupEncoding;
use halo2curves::bn256::{Fr, G1Affine};
use halo2curves::serde::SerdeObject;
use std::io::{self, Cursor};

/// Prefix to a prover's message soliciting a challenge
const BLAKE2B_PREFIX_CHALLENGE: u8 = 0;

// TODO: BEFORE WE HAD DIFFERENT PREFIXES FOR DIFFERENT TYPES
/// Prefix to a prover's message
const BLAKE2B_PREFIX_COMMON: u8 = 1;

/*
/// NOTE /////
Why do we need the below three traits? The reason is that we cannot implement
Into<Transcript::HashInput> for an arbitrary type due to the orphan rule. This
means that we need to have a trait for something that is hashable.
 */

/// Hash function that can be used for transcript
pub trait TranscriptHash {
    /// Input type of the hash function
    type Input;
    /// Output type of the hash function
    type Output;

    /// Initialise the hasher
    fn init() -> Self;
    /// Absorb an element
    fn absorb(&mut self, input: &Self::Input) -> &mut Self;
    /// Squeeze an output
    fn squeeze(&mut self) -> Self::Output;
}

/// Traits to represent values that can be hashed with a `TranscriptHash`
pub trait Hashable<H: TranscriptHash> {
    /// Converts the hashable type to a format that can be hashed with `H`
    fn to_input(&self) -> H::Input;
}

/// Trait to represent values that can be sampled from a `TranscriptHash`
pub trait Sampleable<H: TranscriptHash> {
    /// Converts `H`'s output to Self
    fn sample(out: H::Output) -> Self;
}

/// Generic transcript view
pub trait Transcript {
    /// Hash function
    type Hash: TranscriptHash;

    /// Initialises the transcript
    fn init() -> Self;

    /// Parses an existing transcript
    fn init_from_bytes(bytes: &[u8]) -> Self;

    /// Squeeze a challenge of type `T`, which only needs to be `Sampleable` with
    /// the corresponding hash function.
    fn squeeze_challenge<T: Sampleable<Self::Hash>>(&mut self) -> T;

    /// Writing a hashable element `T` to the transcript without writing it to the proof,
    /// treating it as a common commitment.
    fn common<T: Hashable<Self::Hash>>(&mut self, input: &T) -> io::Result<()>;

    /// Read a hashable element `T` from the prover.
    fn read<T: Hashable<Self::Hash> + SerdeObject>(&mut self) -> io::Result<T>;

    /// Write a hashable element `T` to the proof and the transcript.
    fn write<T: Hashable<Self::Hash> + SerdeObject>(&mut self, input: &T) -> io::Result<()>;

    /// Returns the buffer with the proof
    fn finalize(self) -> Vec<u8>;
}

#[derive(Debug)]
/// Transcript used in proofs, parametrised by its hash function.
pub struct CircuitTranscript<H: TranscriptHash> {
    state: H,
    buffer: Cursor<Vec<u8>>,
}

impl<H: TranscriptHash> Transcript for CircuitTranscript<H> {
    type Hash = H;

    fn init() -> Self {
        Self {
            state: H::init(),
            buffer: Cursor::new(vec![]),
        }
    }

    fn init_from_bytes(bytes: &[u8]) -> Self {
        Self {
            state: H::init(),
            buffer: Cursor::new(bytes.to_vec()),
        }
    }

    fn squeeze_challenge<T: Sampleable<H>>(&mut self) -> T {
        T::sample(self.state.squeeze())
    }

    fn common<T: Hashable<H>>(&mut self, input: &T) -> io::Result<()> {
        self.state.absorb(&input.to_input());

        Ok(())
    }

    fn read<T: Hashable<H> + SerdeObject>(&mut self) -> io::Result<T> {
        let val = T::read_raw(&mut self.buffer)?;
        self.common(&val)?;

        Ok(val)
    }

    fn write<T: Hashable<H> + SerdeObject>(&mut self, input: &T) -> io::Result<()> {
        self.common(input)?;
        input.write_raw(&mut self.buffer)
    }

    fn finalize(self) -> Vec<u8> {
        self.buffer.into_inner()
    }
}

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

pub(crate) fn read_n<C, T>(transcript: &mut T, n: usize) -> io::Result<Vec<C>>
where
    T: Transcript,
    C: Hashable<T::Hash> + SerdeObject,
{
    (0..n).map(|_| transcript.read()).collect()
}
