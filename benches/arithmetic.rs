#[macro_use]
extern crate criterion;

extern crate halo2;
use crate::arithmetic::small_multiexp;
use crate::poly::commitment::Setup;
use halo2::*;
use pairing::arithmetic::BaseExt;
use pairing::bn256::{Bn256, Fr as Fp};
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;

use criterion::{black_box, Criterion};

fn criterion_benchmark(c: &mut Criterion) {
    // small multiexp
    {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);
        let params = Setup::<Bn256>::new(5, &mut rng);

        let g = &mut params.get_g();
        let len = g.len() / 2;
        let (g_lo, g_hi) = g.split_at_mut(len);

        let coeff_1 = Fp::rand();
        let coeff_2 = Fp::rand();

        c.bench_function("double-and-add", |b| {
            b.iter(|| {
                for (g_lo, g_hi) in g_lo.iter().zip(g_hi.iter()) {
                    small_multiexp(&[black_box(coeff_1), black_box(coeff_2)], &[*g_lo, *g_hi]);
                }
            })
        });
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
