use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::Field,
    circuit::{AssignedCell, Chip, Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Fixed, Selector},
    poly::Rotation,
};

const EVALADVCOL:usize = 4;

trait PolyEvalInstructions<F: Field>: Chip<F> {
    /// Variable representing a coefficient.
    /// Certainly it could be from another Field/Group,
    /// orther than current one
    type Coeff;

    /// Field element
    type Elem;

    /// Load Element to be used as eval point 
    fn load_element(&self, layouter: impl Layouter<F>, a: Value<F>) -> Result<Self::Elem, Error>;

    /// Evaluation
    fn eval(&self, layouter: impl Layouter<F>, coeffs: Vec<Self::Coeff>, elem: Self::Elem) -> Result<Self::Elem, Error>;

    /// Expose the calculation results as a target whom instance compares with
    fn reveal(&self, layouter: impl Layouter<F>, elem: Self::Elem, row: usize) -> Result<(), Error>;
    
}

/// Chip for poly eval
#[derive(Clone, Debug)]
struct PolyEvalConfig {
    /// cols: | coeff | point | result | accumulative result |
    advice: [Column<Advice>; EVALADVCOL],

    /// This is the public input (instance) column
    instance: Column<Instance>,

    /// | X as kth unit of root |
    point: Column<Fixed>,

    /// A selector controls gate
    e_sel: Selector,
}

struct PolyEvalChip<F: Field> {
    config: PolyEvalConfig,
    _marker: PhantomData<F>,
}

impl<F: Field> PolyEvalChip<F> {
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; EVALADVCOL],
        instance: Column<Instance>,
        point: Column<Fixed>,
    ) -> <Self as Chip<F>>::Config {
        for col in advice.iter() {
            meta.enable_equality(*col);
        }
        meta.enable_equality(instance);
        meta.enable_constant(point);
        // All constraints enforced at once
        let e_sel = meta.selector();

        meta.create_gate("x pow", |meta| {
            let cur_x = meta.query_advice(advice[1], Rotation::cur());
            let next_x = meta.query_advice(advice[1], Rotation::next());
            let x = meta.query_fixed(point, Rotation::cur());
            let pow_s = meta.query_selector(e_sel);

            vec![pow_s * (next_x - cur_x * x)]
        });

        meta.create_gate("addition for res", |meta| {
            let coeff = meta.query_advice(advice[0], Rotation::cur());
            let elem = meta.query_advice(advice[1], Rotation::cur());
            let res = meta.query_advice(advice[2], Rotation::cur());
            let add_s = meta.query_selector(e_sel);

            vec![add_s * (res - coeff * elem)]
        });

        meta.create_gate("acc", |meta| {
            let prev_acc = meta.query_advice(advice[3], Rotation::prev());
            let cur_acc = meta.query_advice(advice[3], Rotation::cur());
            let res = meta.query_advice(advice[2], Rotation::cur());
            let acc_s = meta.query_selector(e_sel);

            vec![acc_s * (cur_acc - (res + prev_acc))]
        });

        PolyEvalConfig {
            advice,
            instance,
            point,
            e_sel,
        }

    }
}

impl<F: Field> Chip<F> for PolyEvalChip<F> {
    type Config = PolyEvalConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

/// A possible implementation
impl<F: Field> PolyEvalInstructions<F> for PolyEvalChip<F> {
    type Coeff = AssignedCell<F,F>;
    type Elem = AssignedCell<F,F>;

    fn load_element(&self, mut layouter: impl Layouter<F>, a: Value<F>) -> Result<Self::Elem, Error> {
        let config = self.config();

        layouter.assign_region(|| "load eval point", |mut region: Region<F>| {
            region.assign_fixed(|| "eval point value", config.point, 0,|| a)
        })
    }

    fn eval(
        &self,
        mut layouter: impl Layouter<F>,
        coeffs: Vec<Self::Coeff>,
        elem: Self::Elem
    ) -> Result<Self::Elem, Error> {
        let config = self.config();

        layouter.assign_region(|| "eval region", |mut region: Region<F>| {
            // Init
            let mut acc = region.assign_advice(
                || "init acc to zero",config.advice[3],
                0, ||Value::known(F::ZERO))?;
            let mut pow_x = Value::known(F::ONE);

            // Assign the advice according to the coeff list
            for (i, coeff) in coeffs.iter().enumerate() {
                // Since our region starts at an aux row which only stores an init acc(F::ZERO)
                let offset = i + 1;
                config.e_sel.enable(&mut region, offset)?;

                // Contrain coeff
                coeff.copy_advice(|| format!("coeff {}", i), &mut region, config.advice[0], offset)?;

                // Assgin x exponentiation
                region.assign_advice(|| format!("x power {}", i), config.advice[1], offset, || pow_x)?;

                // Calculate the current result
                let res = region.assign_advice(
                    || format!("res {}", i),
                    config.advice[2],
                    offset,
                    || coeff.clone().value().copied() * pow_x
                )?;

                // At end of each turn, assign acc and store it
                let prev_acc_value = acc.value().copied();
                acc = region.assign_advice(|| format!("acc {}", i), config.advice[3], offset, || prev_acc_value + res.value())?;

                // Assign fix
                region.assign_fixed(
                    || format!("fixed eval point in {} step", i),
                    config.point,
                    offset,
                    || elem.clone().value().copied()
                )?;

                // Step pow_x with another mul per se
                pow_x = pow_x * elem.clone().value().copied();
            }
            
            // Since we use only one selector on 3 gates, then we have to satisfy gate `pow x`
            // by providing one more row
            region.assign_advice(
                || format!("final row for pow x gate {}",coeffs.len()),
                config.advice[1],
                coeffs.len() + 1,
                || pow_x
            )?;

            Ok(acc)
        })
    }

    fn reveal(&self, mut layouter: impl Layouter<F>, elem: Self::Elem, row: usize) -> Result<(), Error> {
        let config = self.config();

        layouter.constrain_instance(elem.cell(), config.instance, row)
    }
  
} 

/// A way of loading coeffs
impl<F: Field> PolyEvalChip<F> {
    fn load_coeffs(
        &self,
        mut layouter: impl Layouter<F>,
        list: &Vec<Value<F>>,
    ) -> Result<Vec<AssignedCell<F,F>>, Error> {
        let config = self.config();
        let mut coeffs: Vec<AssignedCell<F,F>> = vec![];

        for (i, coeff) in list.iter().enumerate() {
            let cell_coeff = layouter.assign_region(
                || format!("coeff region {}", i),
                |mut region: Region<F>| {
                    region.assign_advice(|| format!("load coeff {}", i), config.advice[0], 0, || *coeff)
                })?;
            coeffs.push(cell_coeff);
        }

        Ok(coeffs)
    }
} 

/// Implement the poly circuit
#[derive(Default)]
struct PolyEvalCircuit<F: Field> {
    coeffs: Vec<Value<F>>,
    point: Value<F>,
}

impl<F:Field> Circuit<F> for PolyEvalCircuit<F> {
    type Config = PolyEvalConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let advice = [meta.advice_column(), meta.advice_column(),
                                           meta.advice_column(), meta.advice_column()];

        let instance = meta.instance_column();

        let point = meta.fixed_column();

        PolyEvalChip::configure(meta, advice, instance, point)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        let chip = PolyEvalChip::<F>::construct(config);

        let coeff_cells = chip.load_coeffs(layouter.namespace(|| "load coeffs in syn"), &self.coeffs)?;

        let point_cell = chip.load_element(layouter.namespace(|| "load eval point in syn"), self.point)?;

        let evaluation = chip.eval(layouter.namespace(|| "eval in syn"), coeff_cells, point_cell)?;

        chip.reveal(layouter.namespace(|| "reveal"), evaluation, 0)

    }
}

fn main() {
    use halo2_proofs::dev::MockProver;
    use halo2curves::pasta::Fp;

    let k = 4;

    let test_list = [1,2,3];
    let test_point = 5;

    let coeffs: Vec<Value<Fp>> = test_list.clone().into_iter().map(|x| {Value::known(Fp::from(x))}).collect();

    let point = Value::known(Fp::from(test_point));

    let circuit = PolyEvalCircuit {
        coeffs: coeffs,
        point: point,
    };

    fn poly_eval(coeffs: Vec<u64>, x :u64) -> u64 {
        let mut acc = 0;
        let mut temp = 1;
        for coeff in coeffs {
            acc += coeff * temp;
            temp *= x;
        }
        acc
    }

    let instance = poly_eval(test_list.to_vec(), test_point);

    let public_inputs = vec![Fp::from(instance)];

     // Given the correct public input, our circuit will verify.
    let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();

    assert_eq!(prover.verify(), Ok(()));
   
}