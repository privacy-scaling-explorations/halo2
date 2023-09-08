#[macro_use]
extern crate criterion;

use crate::arithmetic::{best_multiexp, CurveAffine};
// use crate::halo2curves::pasta::{EqAffine, Fp};
use crate::halo2curves::bn256::{G1Affine, Fr};
use ff::PrimeField;
use halo2_proofs::*;

use halo2_proofs::poly::{commitment::ParamsProver, ipa::commitment::ParamsIPA};

use criterion::{black_box, BenchmarkId, Criterion};
use rand_core::OsRng;

pub fn generate_msm_inputs<C, F>(size: usize) -> (Vec<C>, Vec<F>)
where
    F: PrimeField,
    C: CurveAffine<ScalarExt=F>,
{
    let rng = OsRng;
    let vec_len = 1 << size;
    let scalar_vec = (0..vec_len)
        .map(|_| F::random(rng))
        .collect();
    let params: ParamsIPA<C> = ParamsIPA::new(size as u32);
    let point_vec = params.get_g().to_vec();
    (
        point_vec,
        scalar_vec,
    )
}

fn criterion_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("msm");
    for size in 8..10 {
        let (point_vec, scalar_vec) = generate_msm_inputs::<G1Affine, Fr>(size);
        let point_vec = black_box(point_vec);
        let scalar_vec = black_box(scalar_vec);
        group.bench_with_input(BenchmarkId::new("Baseline", size), &size, |b, _size| {
            b.iter(|| {
                let _ = best_multiexp(&scalar_vec[..], &point_vec[..]);
            })
        });
        // add optimized function here
        // group.bench_with_input(BenchmarId::new("Optimized, size) ....
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
