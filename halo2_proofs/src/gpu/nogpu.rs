use super::error::{GPUError, GPUResult};
use crate::pairing::ff::{PrimeField, ScalarEngine};
use crate::pairing::CurveAffine;
use crate::worker::Worker;
use std::marker::PhantomData;
use std::sync::Arc;

// This module is compiled instead of `fft.rs` and `multiexp.rs` if `gpu` feature is disabled.

pub struct MultiFFTKernel<E>(PhantomData<E>)
where
    E: ScalarEngine;

impl<E> MultiFFTKernel<E>
where
    E: ScalarEngine,
{
    pub fn create(_: bool) -> GPUResult<MultiFFTKernel<E>> {
        return Err(GPUError::GPUDisabled);
    }

    pub fn radix_fft(&mut self, _: &mut [E::Fr], _: &E::Fr, _: u32) -> GPUResult<()> {
        return Err(GPUError::GPUDisabled);
    }
}

pub struct MultiexpKernel<E>(PhantomData<E>)
where
    E: ScalarEngine;

impl<E> MultiexpKernel<E>
where
    E: ScalarEngine,
{
    pub fn create(_: bool) -> GPUResult<MultiexpKernel<E>> {
        return Err(GPUError::GPUDisabled);
    }

    pub fn multiexp<G>(
        &mut self,
        _: &Worker,
        _: Arc<Vec<G>>,
        _: Arc<Vec<<<G::Engine as ScalarEngine>::Fr as PrimeField>::Repr>>,
        _: usize,
        _: usize,
    ) -> GPUResult<<G as CurveAffine>::Projective>
    where
        G: CurveAffine,
    {
        return Err(GPUError::GPUDisabled);
    }

    pub fn dense_multiexp<G: CurveAffine>(
        &mut self,
        _: &Worker,
        _: Arc<Vec<G>>,
        _: Arc<Vec<<<G::Engine as ScalarEngine>::Fr as PrimeField>::Repr>>,
        _: usize,
    ) -> GPUResult<<G as CurveAffine>::Projective>
    where
        G::Engine: crate::pairing::Engine,
    {
        return Err(GPUError::GPUDisabled);
    }
}

use crate::pairing::Engine;

macro_rules! locked_kernel {
    ($class:ident) => {
        pub struct $class<E>(PhantomData<E>);

        impl<E> $class<E>
        where
            E: Engine,
        {
            pub fn new(_: usize, _: bool) -> $class<E> {
                $class::<E>(PhantomData)
            }

            pub fn with<F, R, K>(&mut self, _: F) -> GPUResult<R>
            where
                F: FnMut(&mut K) -> GPUResult<R>,
            {
                return Err(GPUError::GPUDisabled);
            }
        }
    };
}

locked_kernel!(LockedMultiFFTKernel);
locked_kernel!(LockedMultiexpKernel);
