use std::{
    fs::File,
    io::{BufReader, BufWriter, Write},
};

use ff::Field;
use halo2_debug::test_rng;
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        keygen_pk_custom, keygen_vk_custom, pk_read, vk_read, Advice, Circuit, Column,
        ConstraintSystem, ErrorFront, Fixed, Instance, ProvingKey, VerifyingKey,
    },
    poly::{kzg::commitment::ParamsKZG, Rotation},
    SerdeFormat,
};
use halo2curves::bn256::{Bn256, Fr, G1Affine};

#[derive(Clone, Copy)]
struct StandardPlonkConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
    q_a: Column<Fixed>,
    q_b: Column<Fixed>,
    q_c: Column<Fixed>,
    q_ab: Column<Fixed>,
    constant: Column<Fixed>,
    #[allow(dead_code)]
    instance: Column<Instance>,
}

impl StandardPlonkConfig {
    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self {
        let [a, b, c] = [(); 3].map(|_| meta.advice_column());
        let [q_a, q_b, q_c, q_ab, constant] = [(); 5].map(|_| meta.fixed_column());
        let instance = meta.instance_column();

        [a, b, c].map(|column| meta.enable_equality(column));

        meta.create_gate(
            "q_a·a + q_b·b + q_c·c + q_ab·a·b + constant + instance = 0",
            |meta| {
                let [a, b, c] = [a, b, c].map(|column| meta.query_advice(column, Rotation::cur()));
                let [q_a, q_b, q_c, q_ab, constant] = [q_a, q_b, q_c, q_ab, constant]
                    .map(|column| meta.query_fixed(column, Rotation::cur()));
                let instance = meta.query_instance(instance, Rotation::cur());
                Some(
                    q_a * a.clone()
                        + q_b * b.clone()
                        + q_c * c
                        + q_ab * a * b
                        + constant
                        + instance,
                )
            },
        );

        StandardPlonkConfig {
            a,
            b,
            c,
            q_a,
            q_b,
            q_c,
            q_ab,
            constant,
            instance,
        }
    }
}

#[derive(Clone, Default)]
struct StandardPlonk(Fr);

impl Circuit<Fr> for StandardPlonk {
    type Config = StandardPlonkConfig;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        StandardPlonkConfig::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), ErrorFront> {
        layouter.assign_region(
            || "",
            |mut region| {
                region.assign_advice(|| "", config.a, 0, || Value::known(self.0))?;
                region.assign_fixed(|| "", config.q_a, 0, || Value::known(-Fr::one()))?;

                region.assign_advice(|| "", config.a, 1, || Value::known(-Fr::from(5u64)))?;
                for (idx, column) in (1..).zip([
                    config.q_a,
                    config.q_b,
                    config.q_c,
                    config.q_ab,
                    config.constant,
                ]) {
                    region.assign_fixed(|| "", column, 1, || Value::known(Fr::from(idx as u64)))?;
                }

                let a = region.assign_advice(|| "", config.a, 2, || Value::known(Fr::one()))?;
                a.copy_advice(|| "", &mut region, config.b, 3)?;
                a.copy_advice(|| "", &mut region, config.c, 4)?;
                Ok(())
            },
        )
    }
}

fn setup(
    k: u32,
    compress_selectors: bool,
) -> (StandardPlonk, VerifyingKey<G1Affine>, ProvingKey<G1Affine>) {
    let mut rng = test_rng();

    let circuit = StandardPlonk(Fr::random(&mut rng));
    let params = ParamsKZG::<Bn256>::setup(k, &mut rng);

    let vk = keygen_vk_custom(&params, &circuit, compress_selectors).expect("vk should not fail");
    let pk = keygen_pk_custom(&params, vk.clone(), &circuit, compress_selectors)
        .expect("pk should not fail");

    (circuit, vk, pk)
}

fn main() {
    let k = 4;
    let compress_selectors = true;

    let (circuit, vk, pk) = setup(k, compress_selectors);

    // choose (de)serialization format
    let format = SerdeFormat::RawBytes;

    // serialization for vk
    let f = File::create("serialization-example.vk").unwrap();
    let mut writer = BufWriter::new(f);
    vk.write(&mut writer, format).unwrap();
    writer.flush().unwrap();

    // deserialization for vk
    let f = File::open("serialization-example.vk").unwrap();
    let mut reader = BufReader::new(f);
    let _vk =
        vk_read::<G1Affine, _, StandardPlonk>(&mut reader, format, k, &circuit, compress_selectors)
            .unwrap();

    // serialization for pk
    let f = File::create("serialization-example.pk").unwrap();
    let mut writer = BufWriter::new(f);
    pk.write(&mut writer, format).unwrap();
    writer.flush().unwrap();

    // deserialization for pk
    let f = File::open("serialization-example.pk").unwrap();
    let mut reader = BufReader::new(f);
    let _pk =
        pk_read::<G1Affine, _, StandardPlonk>(&mut reader, format, k, &circuit, compress_selectors)
            .unwrap();
}
