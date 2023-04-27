#[macro_use]
extern crate criterion;

use crate::arithmetic::best_fft;
use group::ff::Field;
use halo2_proofs::*;
use halo2curves::pasta::Fp;

use criterion::{BenchmarkId, Criterion};
use rand_core::OsRng;

fn criterion_benchmark(c: &mut Criterion) {
    const MIN_K: u32 = 16;
    const MAX_K: u32 = 24;

    let mut group = c.benchmark_group("fft");
    for k in MIN_K..=MAX_K {
        group.bench_function(BenchmarkId::new("k", k), |b| {
            let mut a = (0..(1 << k)).map(|_| Fp::random(OsRng)).collect::<Vec<_>>();
            let omega = Fp::random(OsRng); // would be weird if this mattered
            b.iter(|| {
                best_fft(&mut a, omega, k as u32);
            });
        });
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
