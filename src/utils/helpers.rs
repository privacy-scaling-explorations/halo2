//! HELPER FUNCTIONS

use crate::poly::Polynomial;
use ff::PrimeField;
use group::prime::PrimeCurveAffine;
use group::GroupEncoding;
use halo2curves::serde::SerdeObject;
use std::io;

/// This enum specifies how various types are serialized and deserialized.
#[derive(Clone, Copy, Debug)]
pub enum SerdeFormat {
    /// Curve elements are serialized in compressed form.
    /// Field elements are serialized in standard form, with endianness specified by the
    /// `PrimeField` implementation.
    Processed,
    /// Curve elements are serialized in uncompressed form. Field elements are serialized
    /// in their internal Montgomery representation.
    /// When deserializing, checks are performed to ensure curve elements indeed lie on the curve and field elements
    /// are less than modulus.
    RawBytes,
    /// Serialization is the same as `RawBytes`, but no checks are performed.
    RawBytesUnchecked,
}

/// Interface for Serde objects that can be represented in compressed form.
pub trait ProcessedSerdeObject: SerdeObject + Default {
    /// Reads an element from the buffer and parses it according to the `format`:
    /// - `Processed`: Reads a compressed element and decompress it
    /// - `RawBytes`: Reads an uncompressed element and checks its correctness
    /// - `RawBytesUnchecked`: Reads an uncompressed element without performing any checks
    fn read<R: io::Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self>;

    /// Writes an element according to `format`:
    /// - `Processed`: Writes a compressed element
    /// - Otherwise: Writes an uncompressed element
    fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()>;
}

/// Byte length of an affine curve element according to `format`.
pub fn byte_length<T: ProcessedSerdeObject + Default>(format: SerdeFormat) -> usize {
    match format {
        SerdeFormat::Processed => T::default().to_raw_bytes().len(),
        _ => T::default().to_raw_bytes().len() * 2,
    }
}

/// Helper function to read a field element with a serde format. There is no way to compress field
/// elements, so `Processed` and `RawBytes` act equivalently.
pub(crate) fn read_f<F: PrimeField + SerdeObject, R: io::Read>(
    reader: &mut R,
    format: SerdeFormat,
) -> io::Result<F> {
    match format {
        SerdeFormat::Processed => <F as SerdeObject>::read_raw(reader),
        SerdeFormat::RawBytes => <F as SerdeObject>::read_raw(reader),
        SerdeFormat::RawBytesUnchecked => Ok(<F as SerdeObject>::read_raw_unchecked(reader)),
    }
}

/// Trait for serialising SerdeObjects
impl<C: PrimeCurveAffine + SerdeObject + Default> ProcessedSerdeObject for C {
    /// Reads an element from the buffer and parses it according to the `format`:
    /// - `Processed`: Reads a compressed curve element and decompress it
    /// - `RawBytes`: Reads an uncompressed curve element with coordinates in Montgomery form.
    ///   Checks that field elements are less than modulus, and then checks that the point is on the curve.
    /// - `RawBytesUnchecked`: Reads an uncompressed curve element with coordinates in Montgomery form;
    ///   does not perform any checks
    fn read<R: io::Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self> {
        match format {
            SerdeFormat::Processed => {
                let mut compressed = <Self as GroupEncoding>::Repr::default();
                reader.read_exact(compressed.as_mut())?;
                Option::from(Self::from_bytes(&compressed)).ok_or_else(|| {
                    io::Error::new(io::ErrorKind::Other, "Invalid point encoding in proof")
                })
            }
            SerdeFormat::RawBytes => <Self as SerdeObject>::read_raw(reader),
            SerdeFormat::RawBytesUnchecked => Ok(<Self as SerdeObject>::read_raw_unchecked(reader)),
        }
    }
    /// Writes a curve element according to `format`:
    /// - `Processed`: Writes a compressed curve element
    /// - Otherwise: Writes an uncompressed curve element with coordinates in Montgomery form
    fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()> {
        match format {
            SerdeFormat::Processed => writer.write_all(self.to_bytes().as_ref()),
            _ => self.write_raw(writer),
        }
    }
}

/// Convert a slice of `bool` into a `u8`.
///
/// Panics if the slice has length greater than 8.
pub fn pack(bits: &[bool]) -> u8 {
    let mut value = 0u8;
    assert!(bits.len() <= 8);
    for (bit_index, bit) in bits.iter().enumerate() {
        value |= (*bit as u8) << bit_index;
    }
    value
}

/// Writes the first `bits.len()` bits of a `u8` into `bits`.
pub fn unpack(byte: u8, bits: &mut [bool]) {
    for (bit_index, bit) in bits.iter_mut().enumerate() {
        *bit = (byte >> bit_index) & 1 == 1;
    }
}

/// Reads a vector of polynomials from buffer
pub(crate) fn read_polynomial_vec<R: io::Read, F: PrimeField + SerdeObject, B>(
    reader: &mut R,
    format: SerdeFormat,
) -> io::Result<Vec<Polynomial<F, B>>> {
    let mut len = [0u8; 4];
    reader.read_exact(&mut len)?;
    let len = u32::from_be_bytes(len);

    (0..len)
        .map(|_| Polynomial::<F, B>::read(reader, format))
        .collect::<io::Result<Vec<_>>>()
}

/// Writes a slice of polynomials to buffer
pub(crate) fn write_polynomial_slice<W: io::Write, F: PrimeField + SerdeObject, B>(
    slice: &[Polynomial<F, B>],
    writer: &mut W,
) -> io::Result<()> {
    writer.write_all(&(slice.len() as u32).to_be_bytes())?;
    for poly in slice.iter() {
        poly.write(writer)?;
    }
    Ok(())
}

/// Gets the total number of bytes of a slice of polynomials, assuming all polynomials are the same length
pub(crate) fn polynomial_slice_byte_length<F: PrimeField, B>(slice: &[Polynomial<F, B>]) -> usize {
    let field_len = F::default().to_repr().as_ref().len();
    4 + slice.len() * (4 + field_len * slice.first().map(|poly| poly.len()).unwrap_or(0))
}
