#[macro_use]
extern crate criterion;

use criterion::{BenchmarkId, Criterion};
use ff::Field;
use group::{Curve, Group};
use halo2curves::bn256::{Bn256, Fr};
use halo2curves::pairing::Engine;

use halo2_proofs::arithmetic::best_multiexp;
use rand_core::OsRng;

fn criterion_benchmark(c: &mut Criterion) {
    const MIN_K: u32 = 16;
    const MAX_K: u32 = 24;

    let rng = OsRng;

    let mut group = c.benchmark_group("msm");
    for k in MIN_K..=MAX_K {
        let n = 1 << k;
        let coeffs = (0..n).map(|_| Fr::random(OsRng)).collect::<Vec<_>>();
        let bases: Vec<_> = (0..n)
            .map(|_| <Bn256 as Engine>::G1::random(rng).to_affine())
            .collect();

        group.bench_function(BenchmarkId::new("k", k), |b| {
            b.iter(|| {
                best_multiexp(&coeffs, &bases);
            });
        });
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
