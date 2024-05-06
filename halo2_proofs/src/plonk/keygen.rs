use crate::plonk::Error;
use halo2_backend::plonk::{
    keygen::{keygen_pk as backend_keygen_pk, keygen_vk as backend_keygen_vk},
    ProvingKey, VerifyingKey,
};
use halo2_backend::{arithmetic::CurveAffine, poly::commitment::Params};
use halo2_frontend::circuit::compile_circuit;
use halo2_frontend::plonk::Circuit;
use halo2_middleware::ff::FromUniformBytes;

/// Generate a `VerifyingKey` from an instance of `Circuit`.
/// By default, selector compression is turned **ON**.
///
/// **NOTE**: This `keygen_vk` is legacy one, assuming that `compress_selector: true`.  
/// Hence, it is HIGHLY recommended to pair this util with `keygen_pk`.  
/// In addition, when using this for key generation, user MUST use `compress_selectors: true`.
pub fn keygen_vk<'params, C, P, ConcreteCircuit>(
    params: &P,
    circuit: &ConcreteCircuit,
) -> Result<VerifyingKey<C>, Error>
where
    C: CurveAffine,
    P: Params<'params, C>,
    ConcreteCircuit: Circuit<C::Scalar>,
    C::Scalar: FromUniformBytes<64>,
{
    let (compiled_circuit, _, _) = compile_circuit(params.k(), circuit)?;
    Ok(backend_keygen_vk(params, &compiled_circuit)?)
}

/// Generate a `ProvingKey` from a `VerifyingKey` and an instance of `Circuit`.
/// By default, selector compression is turned **ON**.
///
/// **NOTE**: This `keygen_pk` is legacy one, assuming that `compress_selector: true`.  
/// Hence, it is HIGHLY recommended to pair this util with `keygen_vk`.  
/// In addition, when using this for key generation, user MUST use `compress_selectors: true`.
pub fn keygen_pk<'params, C, P, ConcreteCircuit>(
    params: &P,
    vk: VerifyingKey<C>,
    circuit: &ConcreteCircuit,
) -> Result<ProvingKey<C>, Error>
where
    C: CurveAffine,
    P: Params<'params, C>,
    ConcreteCircuit: Circuit<C::Scalar>,
{
    let (compiled_circuit, _, _) = compile_circuit(params.k(), circuit)?;
    Ok(backend_keygen_pk(params, vk, &compiled_circuit)?)
}
