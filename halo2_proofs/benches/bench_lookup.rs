#[macro_use]
extern crate criterion;

use ff::{Field, PrimeField};
use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::plonk::*;
use halo2_proofs::poly::commitment::ParamsProver;
use halo2_proofs::poly::ipa::commitment::{IPACommitmentScheme, ParamsIPA};
use halo2_proofs::poly::ipa::multiopen::ProverIPA;
use halo2_proofs::poly::Rotation;
use halo2_proofs::transcript::{Blake2bWrite, Challenge255, TranscriptWriterBuffer};
use halo2curves::pasta::{pallas, EqAffine};
use rand_core::OsRng;

use std::marker::PhantomData;

use criterion::{BenchmarkId, Criterion};

fn criterion_benchmark(c: &mut Criterion) {
    #[derive(Clone, Default)]
    struct MyCircuit<F: Field> {
        k: usize,
        _marker: PhantomData<F>,
    }

    #[derive(Clone)]
    struct MyConfig {
        selector: Selector,
        table: TableColumn,
        advice: Column<Advice>,
    }

    impl<F: PrimeField> Circuit<F> for MyCircuit<F> {
        type Config = MyConfig;
        type FloorPlanner = SimpleFloorPlanner;
        #[cfg(feature = "circuit-params")]
        type Params = ();

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> MyConfig {
            let config = MyConfig {
                selector: meta.complex_selector(),
                table: meta.lookup_table_column(),
                advice: meta.advice_column(),
            };

            meta.lookup("lookup", |meta| {
                let selector = meta.query_selector(config.selector);
                let not_selector = Expression::Constant(F::ONE) - selector.clone();
                let advice = meta.query_advice(config.advice, Rotation::cur());
                vec![(selector * advice + not_selector, config.table)]
            });

            config
        }

        fn synthesize(
            &self,
            config: MyConfig,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            layouter.assign_table(
                || "lookup table",
                |mut table| {
                    for row in 0u64..(1 << (self.k - 1)) {
                        table.assign_cell(
                            || format!("row {}", row),
                            config.table,
                            row as usize,
                            || Value::known(F::from(row)),
                        )?;
                    }

                    Ok(())
                },
            )?;

            layouter.assign_region(
                || "assign values",
                |mut region| {
                    for offset in 0u64..(1 << self.k) - 20 {
                        config.selector.enable(&mut region, offset as usize)?;
                        region.assign_advice(
                            || format!("offset {}", offset),
                            config.advice,
                            offset as usize,
                            || Value::known(F::from(offset >> 1)),
                        )?;
                    }

                    Ok(())
                },
            )
        }
    }

    let k_range = 14..=18;

    let mut prover_group = c.benchmark_group("bench-lookup");
    prover_group.sample_size(10);
    for k in k_range {
        let circuit = MyCircuit::<pallas::Base> {
            k: k as usize,
            _marker: PhantomData,
        };
        let params = ParamsIPA::<EqAffine>::new(k);
        let vk = keygen_vk(&params, &circuit).unwrap();
        let pk = keygen_pk(&params, vk, &circuit).unwrap();
        prover_group.bench_with_input(
            BenchmarkId::from_parameter(k),
            &(params, pk),
            |b, (params, pk)| {
                b.iter(|| {
                    let mut transcript = Blake2bWrite::<_, _, Challenge255<EqAffine>>::init(vec![]);
                    let rng = OsRng;
                    create_proof::<IPACommitmentScheme<EqAffine>, ProverIPA<EqAffine>, _, _, _, _>(
                        params,
                        pk,
                        &[circuit.clone()],
                        &[&[]],
                        rng,
                        &mut transcript,
                    )
                    .unwrap();
                    transcript.finalize();
                });
            },
        );
    }
    prover_group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
