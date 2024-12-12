//! This module provides an implementation of a variant of (Turbo)[PLONK][plonk]
//! that is designed specifically for the polynomial commitment scheme described
//! in the [Halo][halo] paper.
//!
//! [halo]: https://eprint.iacr.org/2019/1021
//! [plonk]: https://eprint.iacr.org/2019/953

use blake2b_simd::Params as Blake2bParams;
use group::ff::FromUniformBytes;

use crate::helpers::{
    byte_length, polynomial_slice_byte_length, read_polynomial_vec, write_polynomial_slice,
    SerdePrimeField,
};
use crate::poly::{
    Coeff, EvaluationDomain, ExtendedLagrangeCoeff, LagrangeCoeff, PinnedEvaluationDomain,
    Polynomial,
};
use crate::transcript::{Hashable, Transcript};
use crate::SerdeFormat;

mod circuit;
mod error;
mod evaluation;
mod keygen;
mod lookup;
pub mod permutation;
mod vanishing;

mod prover;
mod verifier;

pub use circuit::*;
pub use error::*;
pub use keygen::*;
pub use prover::*;
pub use verifier::*;

use crate::poly::commitment::PolynomialCommitmentScheme;
use evaluation::Evaluator;
use ff::{PrimeField, WithSmallOrderMulGroup};
use halo2curves::serde::SerdeObject;
use std::io;

/// This is a verifying key which allows for the verification of proofs for a
/// particular circuit.
#[derive(Clone, Debug)]
pub struct VerifyingKey<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    domain: EvaluationDomain<F>,
    fixed_commitments: Vec<CS::Commitment>,
    permutation: permutation::VerifyingKey<F, CS>,
    cs: ConstraintSystem<F>,
    /// Cached maximum degree of `cs` (which doesn't change after construction).
    cs_degree: usize,
    /// The representative of this `VerifyingKey` in transcripts.
    transcript_repr: F,
    selectors: Vec<Vec<bool>>,
}

// Current version of the VK
const VERSION: u8 = 0x03;

impl<F, CS> VerifyingKey<F, CS>
where
    F: WithSmallOrderMulGroup<3> + SerdePrimeField + FromUniformBytes<64> + SerdeObject,
    CS: PolynomialCommitmentScheme<F>,
    CS::Commitment: SerdeObject,
{
    /// Writes a verifying key to a buffer.
    ///
    /// Writes a curve element according to `format`:
    /// - `Processed`: Writes a compressed curve element with coordinates in standard form.
    /// Writes a field element in standard form, with endianness specified by the
    /// `PrimeField` implementation.
    /// - Otherwise: Writes an uncompressed curve element with coordinates in Montgomery form
    /// Writes a field element into raw bytes in its internal Montgomery representation,
    /// WITHOUT performing the expensive Montgomery reduction.
    pub fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()> {
        // Version byte that will be checked on read.
        writer.write_all(&[VERSION])?;
        let k = &self.domain.k();
        assert!(*k <= F::S);
        // k value fits in 1 byte
        writer.write_all(&[*k as u8])?;
        writer.write_all(&(self.fixed_commitments.len() as u32).to_le_bytes())?;
        for commitment in &self.fixed_commitments {
            // TODO: writting raw here - do we maybe want a wrapper like we had?
            commitment.write_raw(writer)?;
        }
        self.permutation.write(writer, format)?;

        // write self.selectors
        for selector in &self.selectors {
            // since `selector` is filled with `bool`, we pack them 8 at a time into bytes and then write
            for bits in selector.chunks(8) {
                writer.write_all(&[crate::helpers::pack(bits)])?;
            }
        }
        Ok(())
    }

    /// Reads a verification key from a buffer.
    ///
    /// Reads a curve element from the buffer and parses it according to the `format`:
    /// - `Processed`: Reads a compressed curve element and decompresses it.
    /// Reads a field element in standard form, with endianness specified by the
    /// `PrimeField` implementation, and checks that the element is less than the modulus.
    /// - `RawBytes`: Reads an uncompressed curve element with coordinates in Montgomery form.
    /// Checks that field elements are less than modulus, and then checks that the point is on the curve.
    /// - `RawBytesUnchecked`: Reads an uncompressed curve element with coordinates in Montgomery form;
    /// does not perform any checks
    pub fn read<R: io::Read, ConcreteCircuit: Circuit<F>>(
        reader: &mut R,
        format: SerdeFormat,
        #[cfg(feature = "circuit-params")] params: ConcreteCircuit::Params,
    ) -> io::Result<Self> {
        let mut version_byte = [0u8; 1];
        reader.read_exact(&mut version_byte)?;
        if VERSION != version_byte[0] {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "unexpected version byte",
            ));
        }

        let mut k = [0u8; 1];
        reader.read_exact(&mut k)?;
        let k = u8::from_le_bytes(k);
        if k as u32 > F::S {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("circuit size value (k): {} exceeds maxium: {}", k, F::S),
            ));
        }

        let (domain, cs, _) = keygen::create_domain::<F, ConcreteCircuit>(
            k as u32,
            #[cfg(feature = "circuit-params")]
            params,
        );
        let mut num_fixed_columns = [0u8; 4];
        reader.read_exact(&mut num_fixed_columns)?;
        let num_fixed_columns = u32::from_le_bytes(num_fixed_columns);

        let fixed_commitments: Vec<_> = (0..num_fixed_columns)
            // TODO: Fix FORMAT - wrapper like before?
            .map(|_| CS::Commitment::read_raw(reader))
            .collect::<Result<_, _>>()?;

        let permutation = permutation::VerifyingKey::read(reader, &cs.permutation, format)?;

        let selectors = vec![];
        // we still need to replace selectors with fixed Expressions in `cs`
        let fake_selectors = vec![vec![]; cs.num_selectors];
        let (cs, _) = cs.directly_convert_selectors_to_fixed(fake_selectors);

        Ok(Self::from_parts(
            domain,
            fixed_commitments,
            permutation,
            cs,
            selectors,
        ))
    }

    /// Writes a verifying key to a vector of bytes using [`Self::write`].
    pub fn to_bytes(&self, format: SerdeFormat) -> Vec<u8> {
        let mut bytes = Vec::<u8>::with_capacity(self.bytes_length(format));
        Self::write(self, &mut bytes, format).expect("Writing to vector should not fail");
        bytes
    }

    /// Reads a verification key from a slice of bytes using [`Self::read`].
    pub fn from_bytes<ConcreteCircuit: Circuit<F>>(
        mut bytes: &[u8],
        format: SerdeFormat,
        #[cfg(feature = "circuit-params")] params: ConcreteCircuit::Params,
    ) -> io::Result<Self> {
        Self::read::<_, ConcreteCircuit>(
            &mut bytes,
            format,
            #[cfg(feature = "circuit-params")]
            params,
        )
    }
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> VerifyingKey<F, CS> {
    fn bytes_length(&self, format: SerdeFormat) -> usize {
        10 + (self.fixed_commitments.len() * byte_length::<CS::Commitment>(format))
            + self.permutation.bytes_length(format)
            + self.selectors.len()
                * (self
                    .selectors
                    .first()
                    .map(|selector| (selector.len() + 7) / 8)
                    .unwrap_or(0))
    }

    fn from_parts(
        domain: EvaluationDomain<F>,
        fixed_commitments: Vec<CS::Commitment>,
        permutation: permutation::VerifyingKey<F, CS>,
        cs: ConstraintSystem<F>,
        selectors: Vec<Vec<bool>>,
    ) -> Self
    where
        F: FromUniformBytes<64>,
    {
        // Compute cached values.
        let cs_degree = cs.degree();

        let mut vk = Self {
            domain,
            fixed_commitments,
            permutation,
            cs,
            cs_degree,
            // Temporary, this is not pinned.
            transcript_repr: F::ZERO,
            selectors,
        };

        let mut hasher = Blake2bParams::new()
            .hash_length(64)
            .personal(b"Halo2-Verify-Key")
            .to_state();

        let s = format!("{:?}", vk.pinned());

        hasher.update(&(s.len() as u64).to_le_bytes());
        hasher.update(s.as_bytes());

        // Hash in final Blake2bState
        vk.transcript_repr = F::from_uniform_bytes(hasher.finalize().as_array());

        vk
    }

    /// Hashes a verification key into a transcript.
    pub fn hash_into<T: Transcript>(&self, transcript: &mut T) -> io::Result<()>
    where
        F: Hashable<T::Hash>,
    {
        transcript.common(&self.transcript_repr)?;

        Ok(())
    }

    /// Obtains a pinned representation of this verification key that contains
    /// the minimal information necessary to reconstruct the verification key.
    pub fn pinned(&self) -> PinnedVerificationKey<'_, F, CS> {
        PinnedVerificationKey {
            domain: self.domain.pinned(),
            fixed_commitments: &self.fixed_commitments,
            permutation: &self.permutation,
            cs: self.cs.pinned(),
        }
    }

    /// Returns commitments of fixed polynomials
    pub fn fixed_commitments(&self) -> &Vec<CS::Commitment> {
        &self.fixed_commitments
    }

    /// Returns `VerifyingKey` of permutation
    pub fn permutation(&self) -> &permutation::VerifyingKey<F, CS> {
        &self.permutation
    }

    /// Returns `ConstraintSystem`
    pub fn cs(&self) -> &ConstraintSystem<F> {
        &self.cs
    }

    /// Returns representative of this `VerifyingKey` in transcripts
    pub fn transcript_repr(&self) -> F {
        self.transcript_repr
    }
}

/// Minimal representation of a verification key that can be used to identify
/// its active contents.
#[allow(dead_code)]
#[derive(Debug)]
pub struct PinnedVerificationKey<'a, F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    domain: PinnedEvaluationDomain<'a, F>,
    cs: PinnedConstraintSystem<'a, F>,
    fixed_commitments: &'a Vec<CS::Commitment>,
    permutation: &'a permutation::VerifyingKey<F, CS>,
}
/// This is a proving key which allows for the creation of proofs for a
/// particular circuit.
#[derive(Clone, Debug)]
pub struct ProvingKey<F: PrimeField, CS: PolynomialCommitmentScheme<F>> {
    vk: VerifyingKey<F, CS>,
    l0: Polynomial<F, ExtendedLagrangeCoeff>,
    l_last: Polynomial<F, ExtendedLagrangeCoeff>,
    l_active_row: Polynomial<F, ExtendedLagrangeCoeff>,
    fixed_values: Vec<Polynomial<F, LagrangeCoeff>>,
    fixed_polys: Vec<Polynomial<F, Coeff>>,
    fixed_cosets: Vec<Polynomial<F, ExtendedLagrangeCoeff>>,
    permutation: permutation::ProvingKey<F>,
    ev: Evaluator<F>,
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> ProvingKey<F, CS>
where
    F: FromUniformBytes<64>,
{
    /// Get the underlying [`VerifyingKey`].
    pub fn get_vk(&self) -> &VerifyingKey<F, CS> {
        &self.vk
    }

    /// Gets the total number of bytes in the serialization of `self`
    fn bytes_length(&self, format: SerdeFormat) -> usize {
        let scalar_len = F::default().to_repr().as_ref().len();
        self.vk.bytes_length(format)
            + 12 // bytes used for encoding the length(u32) of "l0", "l_last" & "l_active_row" polys
            + scalar_len * (self.l0.len() + self.l_last.len() + self.l_active_row.len())
            + polynomial_slice_byte_length(&self.fixed_values)
            + polynomial_slice_byte_length(&self.fixed_polys)
            + polynomial_slice_byte_length(&self.fixed_cosets)
            + self.permutation.bytes_length()
    }
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> ProvingKey<F, CS>
where
    F: SerdePrimeField + FromUniformBytes<64>,
{
    /// Writes a proving key to a buffer.
    ///
    /// Writes a curve element according to `format`:
    /// - `Processed`: Writes a compressed curve element with coordinates in standard form.
    /// Writes a field element in standard form, with endianness specified by the
    /// `PrimeField` implementation.
    /// - Otherwise: Writes an uncompressed curve element with coordinates in Montgomery form
    /// Writes a field element into raw bytes in its internal Montgomery representation,
    /// WITHOUT performing the expensive Montgomery reduction.
    /// Does so by first writing the verifying key and then serializing the rest of the data (in the form of field polynomials)
    pub fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()> {
        self.vk.write(writer, format)?;
        self.l0.write(writer, format)?;
        self.l_last.write(writer, format)?;
        self.l_active_row.write(writer, format)?;
        write_polynomial_slice(&self.fixed_values, writer, format)?;
        write_polynomial_slice(&self.fixed_polys, writer, format)?;
        write_polynomial_slice(&self.fixed_cosets, writer, format)?;
        self.permutation.write(writer, format)?;
        Ok(())
    }

    /// Reads a proving key from a buffer.
    /// Does so by reading verification key first, and then deserializing the rest of the file into the remaining proving key data.
    ///
    /// Reads a curve element from the buffer and parses it according to the `format`:
    /// - `Processed`: Reads a compressed curve element and decompresses it.
    /// Reads a field element in standard form, with endianness specified by the
    /// `PrimeField` implementation, and checks that the element is less than the modulus.
    /// - `RawBytes`: Reads an uncompressed curve element with coordinates in Montgomery form.
    /// Checks that field elements are less than modulus, and then checks that the point is on the curve.
    /// - `RawBytesUnchecked`: Reads an uncompressed curve element with coordinates in Montgomery form;
    /// does not perform any checks
    pub fn read<R: io::Read, ConcreteCircuit: Circuit<F>>(
        reader: &mut R,
        format: SerdeFormat,
        #[cfg(feature = "circuit-params")] params: ConcreteCircuit::Params,
    ) -> io::Result<Self> {
        let vk = VerifyingKey::<F, CS>::read::<R, ConcreteCircuit>(
            reader,
            format,
            #[cfg(feature = "circuit-params")]
            params,
        )?;
        let l0 = Polynomial::read(reader, format)?;
        let l_last = Polynomial::read(reader, format)?;
        let l_active_row = Polynomial::read(reader, format)?;
        let fixed_values = read_polynomial_vec(reader, format)?;
        let fixed_polys = read_polynomial_vec(reader, format)?;
        let fixed_cosets = read_polynomial_vec(reader, format)?;
        let permutation = permutation::ProvingKey::read(reader, format)?;
        let ev = Evaluator::new(vk.cs());
        Ok(Self {
            vk,
            l0,
            l_last,
            l_active_row,
            fixed_values,
            fixed_polys,
            fixed_cosets,
            permutation,
            ev,
        })
    }

    /// Writes a proving key to a vector of bytes using [`Self::write`].
    pub fn to_bytes(&self, format: SerdeFormat) -> Vec<u8> {
        let mut bytes = Vec::<u8>::with_capacity(self.bytes_length(format));
        Self::write(self, &mut bytes, format).expect("Writing to vector should not fail");
        bytes
    }

    /// Reads a proving key from a slice of bytes using [`Self::read`].
    pub fn from_bytes<ConcreteCircuit: Circuit<F>>(
        mut bytes: &[u8],
        format: SerdeFormat,
        #[cfg(feature = "circuit-params")] params: ConcreteCircuit::Params,
    ) -> io::Result<Self> {
        Self::read::<_, ConcreteCircuit>(
            &mut bytes,
            format,
            #[cfg(feature = "circuit-params")]
            params,
        )
    }
}

impl<F: PrimeField, CS: PolynomialCommitmentScheme<F>> VerifyingKey<F, CS> {
    /// Get the underlying [`EvaluationDomain`].
    pub fn get_domain(&self) -> &EvaluationDomain<F> {
        &self.domain
    }
}
