use halo2_middleware::ff::FromUniformBytes;
use halo2curves::CurveAffine;

#[derive(Debug)]
struct BatchItem<C: CurveAffine> {
    instances: Vec<Vec<Vec<C::ScalarExt>>>,
    proof: Vec<u8>,
}

/// A verifier that checks multiple proofs in a batch. **This requires the
/// `batch` crate feature to be enabled.**
#[derive(Debug, Default)]
pub struct BatchVerifier<C: CurveAffine> {
    items: Vec<BatchItem<C>>,
}

impl<C: CurveAffine> BatchVerifier<C>
where
    C::Scalar: FromUniformBytes<64>,
{
    /// Constructs a new batch verifier.
    pub fn new() -> Self {
        Self { items: vec![] }
    }

    /// Adds a proof to the batch.
    pub fn add_proof(&mut self, instances: Vec<Vec<Vec<C::Scalar>>>, proof: Vec<u8>) {
        self.items.push(BatchItem { instances, proof })
    }
}
