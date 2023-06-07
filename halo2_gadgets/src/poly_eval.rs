//! A polynomial evaluation scheme
//! Polynomial represents in coeffs, [c0, c1, c2, ...]
//! P[x] = c0 * 1 + c1 * x + c2 * x^2 + ... cn * x^n
//! where x is in a Fp

use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::Field,
    circuit::{AssignedCell, Chip, Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Selector},
    poly::Rotation,
};

/// Global var for advice col layput
const XINDEX: usize = 0;
const COEFFINDEX: usize = 1;
const ACCINDEX: usize = 2;
// As end of the layout
const EVALADVCOL: usize = ACCINDEX + 1;

/// Polynomial represents in coeffs, [c0, c1, c2, ...]
/// P[x] = c0 * 1 + c1 * x + c2 * x^2 + ... cn * x^n
/// where selection of x and coeffs are from same finite field
pub trait PolyEvalInstructions<F: Field>: Chip<F> {
    /// Variable representing a coefficient.
    /// Certainly it could be from another Field/Group,
    /// orther than current one
    type Coeff;

    /// Field element
    type Elem;

    /// Load Element to be used as eval point
    fn load_element(&self, layouter: impl Layouter<F>, a: Value<F>) -> Result<Self::Elem, Error>;

    /// Evaluation
    fn eval(
        &self,
        layouter: impl Layouter<F>,
        coeffs: Vec<Self::Coeff>,
        elem: Self::Elem,
    ) -> Result<Self::Elem, Error>;
}

/// Chip for poly eval
#[derive(Clone, Debug)]
pub struct PolyEvalConfig {
    /// column layput : | eval point | coeff | accumulative result |
    advice: [Column<Advice>; EVALADVCOL],

    /// A selector controls gate
    e_sel: Selector,

    /// A selector indicating a certain cell is zero
    zero_sel: Selector,
}

/// Poly eval chip
#[derive(Clone, Debug)]
pub struct PolyEvalChip<F: Field> {
    config: PolyEvalConfig,
    _marker: PhantomData<F>,
}

impl<F: Field> PolyEvalChip<F> {
    /// Construct a poly eval chip, return a structured config
    pub fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    /// Define the gates that constraint system needs
    /// Polynomial Evaluation -- Horner's rule
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; EVALADVCOL],
    ) -> <Self as Chip<F>>::Config {
        for col in advice.iter() {
            meta.enable_equality(*col);
        }
        // All constraints enforced at once
        let e_sel = meta.selector();
        let zero_sel = meta.selector();

        meta.create_gate("zero test", |meta| {
            // Cells participating in zero test
            let init_acc = meta.query_advice(advice[ACCINDEX], Rotation::cur());
            let zero_s = meta.query_selector(zero_sel);

            // Simply making a cell to zero is not sufficient
            // We have to enforce the relationship between two rows:
            // That is, the next line acc calucation must be dependent on an inital `acc` with zero value
            let init_acc_clone = meta.query_advice(advice[ACCINDEX], Rotation::cur());
            let next_acc = meta.query_advice(advice[ACCINDEX], Rotation::next());
            let next_coeff = meta.query_advice(advice[COEFFINDEX], Rotation::next());
            let next_x = meta.query_advice(advice[XINDEX], Rotation::next());
            let zero_s_clone = meta.query_selector(zero_sel);

            // First, to constrain init acc is zero;
            // Second, to make sure init acc is guaranteed to be used in following calculation
            // Namely acc(i+1) = coeff(i) + x * acc(i) recursion formula
            vec![
                zero_s * init_acc,
                zero_s_clone * (next_coeff + next_x * init_acc_clone - next_acc),
            ]
        });

        // Following lines are enforced acc(i+1) = coeff(i) + x * acc(i) recursion formula
        meta.create_gate("acc", |meta| {
            let prev_acc = meta.query_advice(advice[ACCINDEX], Rotation::prev());
            let cur_acc = meta.query_advice(advice[ACCINDEX], Rotation::cur());
            let x = meta.query_advice(advice[XINDEX], Rotation::cur());
            let coeff = meta.query_advice(advice[COEFFINDEX], Rotation::cur());
            let acc_s = meta.query_selector(e_sel);

            vec![acc_s * (coeff + x * prev_acc - cur_acc)]
        });

        PolyEvalConfig {
            advice,
            e_sel,
            zero_sel,
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

/// Instructions implementation
impl<F: Field> PolyEvalInstructions<F> for PolyEvalChip<F> {
    type Coeff = AssignedCell<F, F>;
    type Elem = AssignedCell<F, F>;

    fn load_element(
        &self,
        mut layouter: impl Layouter<F>,
        a: Value<F>,
    ) -> Result<Self::Elem, Error> {
        let config = self.config();

        layouter.assign_region(
            || "load eval point",
            |mut region: Region<F>| {
                region.assign_advice(|| "eval point value", config.advice[XINDEX], 0, || a)
            },
        )
    }

    fn eval(
        &self,
        mut layouter: impl Layouter<F>,
        coeffs: Vec<Self::Coeff>,
        elem: Self::Elem,
    ) -> Result<Self::Elem, Error> {
        let config = self.config();

        layouter.assign_region(
            || "eval region",
            |mut region: Region<F>| {
                // Init
                let mut acc = region.assign_advice(
                    || "init acc to zero",
                    config.advice[ACCINDEX],
                    0,
                    || Value::known(F::ZERO),
                )?;
                config.zero_sel.enable(&mut region, 0)?;

                // Assign the advice according to the coeff list
                // NOTICE:
                // As input, the coeff list is assigned as natural order c0, c1, c2...
                // while by leveraging Horner's Rule, we order we need is reserved order
                // cn-1, cn-2, ...
                let n = coeffs.len();
                for (i, coeff) in coeffs.iter().rev().enumerate() {
                    // Since our region starts at an aux row which only stores an init acc(F::ZERO)
                    let offset = i + 1;
                    config.e_sel.enable(&mut region, offset)?;

                    // Constraint on a fixed eval point
                    elem.copy_advice(
                        || format!("eval point on {}", i),
                        &mut region,
                        config.advice[XINDEX],
                        offset,
                    )?;

                    // Constrain coeff
                    coeff.copy_advice(
                        || format!("coeff {}", n - 1 - i),
                        &mut region,
                        config.advice[COEFFINDEX],
                        offset,
                    )?;

                    // At end of each turn, assign acc and store it
                    // Again acc(i+1) = coeff(i) + x * acc(i)
                    let prev_acc_value = acc.value().copied();
                    acc = region.assign_advice(
                        || format!("acc {}", i),
                        config.advice[ACCINDEX],
                        offset,
                        || coeff.value().copied() + elem.value().copied() * prev_acc_value,
                    )?;
                }


                Ok(acc)
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::poly_eval::*;
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::{
        arithmetic::Field,
        circuit::{AssignedCell, Chip, Layouter, Region, SimpleFloorPlanner, Value},
        plonk::{Circuit, ConstraintSystem, Error, Instance},
    };
    use halo2curves::pasta::Fp;

    /// An extention Chip which could handle IO
    #[derive(Clone, Debug)]
    struct PolyEvalExtConfig {
        instance: Column<Instance>,

        polyevalconfig: PolyEvalConfig,
    }

    #[derive(Clone, Debug)]
    struct PolyEvalExtChip<F: Field> {
        config: PolyEvalExtConfig,
        _marker: PhantomData<F>,
    }

    impl<F: Field> Chip<F> for PolyEvalExtChip<F> {
        type Config = PolyEvalExtConfig;
        type Loaded = ();

        fn config(&self) -> &Self::Config {
            &self.config
        }

        fn loaded(&self) -> &Self::Loaded {
            &()
        }
    }

    impl<F: Field> PolyEvalInstructions<F> for PolyEvalExtChip<F> {
        type Coeff = AssignedCell<F, F>;
        type Elem = AssignedCell<F, F>;

        fn eval(
            &self,
            layouter: impl Layouter<F>,
            coeffs: Vec<Self::Coeff>,
            elem: Self::Elem,
        ) -> Result<Self::Elem, Error> {
            let config = self.config().polyevalconfig.clone();
            let polyevalchip = PolyEvalChip::<F>::construct(config);
            polyevalchip.eval(layouter, coeffs, elem)
        }

        fn load_element(
            &self,
            layouter: impl Layouter<F>,
            a: Value<F>,
        ) -> Result<Self::Elem, Error> {
            let config = self.config().polyevalconfig.clone();
            let polyevalchip = PolyEvalChip::<F>::construct(config);
            polyevalchip.load_element(layouter, a)
        }
    }

    /// Impl basic construct
    impl<F: Field> PolyEvalExtChip<F> {
        fn construct(
            config: <Self as Chip<F>>::Config,
            _loaded: <Self as Chip<F>>::Loaded,
        ) -> Self {
            Self {
                config,
                _marker: PhantomData,
            }
        }

        fn configure(
            meta: &mut ConstraintSystem<F>,
            advice: [Column<Advice>; EVALADVCOL],
            instance: Column<Instance>,
        ) -> <Self as Chip<F>>::Config {
            let polyevalconfig = PolyEvalChip::configure(meta, advice);
            meta.enable_equality(instance);

            PolyEvalExtConfig {
                instance,
                polyevalconfig,
            }
        }
    }

    /// A way of loading coeffs
    impl<F: Field> PolyEvalExtChip<F> {
        fn load_coeffs(
            &self,
            mut layouter: impl Layouter<F>,
            list: &[Value<F>],
        ) -> Result<Vec<AssignedCell<F, F>>, Error> {
            let config = self.config().polyevalconfig.clone();
            let mut coeffs: Vec<AssignedCell<F, F>> = vec![];

            for (i, coeff) in list.iter().enumerate() {
                let cell_coeff = layouter.assign_region(
                    || format!("coeff region {}", i),
                    |mut region: Region<F>| {
                        region.assign_advice(
                            || format!("load coeff {}", i),
                            config.advice[COEFFINDEX],
                            0,
                            || *coeff,
                        )
                    },
                )?;
                coeffs.push(cell_coeff);
            }

            Ok(coeffs)
        }

        fn reveal(
            &self,
            mut layouter: impl Layouter<F>,
            elem: AssignedCell<F, F>,
            row: usize,
        ) -> Result<(), Error> {
            let config = self.config();

            layouter.constrain_instance(elem.cell(), config.instance, row)
        }
    }

    /// Implement the poly circuit
    #[derive(Default)]
    struct PolyEvalCircuit<F: Field> {
        coeffs: Vec<Value<F>>,
        point: Value<F>,
    }

    impl<F: Field> Circuit<F> for PolyEvalCircuit<F> {
        type Config = PolyEvalExtConfig;
        type FloorPlanner = SimpleFloorPlanner;
        // Optional circuit configuration parameters, which is not in used
        // For compiler compability it is added here
        #[cfg(feature = "circuit-params")]
        type Params = F;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let advice = [
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
            ];

            let instance = meta.instance_column();

            PolyEvalExtChip::configure(meta, advice, instance)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = PolyEvalExtChip::<F>::construct(config, ());

            let coeff_cells = chip
                .load_coeffs(layouter.namespace(|| "load coeffs in syn"), &self.coeffs)
                .unwrap();

            let point_cell = chip
                .load_element(layouter.namespace(|| "load eval point in syn"), self.point)
                .unwrap();

            let evaluation = chip
                .eval(
                    layouter.namespace(|| "eval in syn"),
                    coeff_cells,
                    point_cell,
                )
                .unwrap();

            chip.reveal(layouter.namespace(|| "reveal"), evaluation, 0)
        }
    }

    // Use naive way to implement poly eval, for comparison purpose
    fn poly_eval(coeffs: Vec<u64>, x: u64) -> u64 {
        let mut acc = 0;
        let mut temp = 1;
        for coeff in coeffs {
            acc += coeff * temp;
            temp *= x;
        }
        acc
    }

    fn poly_sanity_check(test_list: Vec<u64>, test_point: u64, k: u32) {
        let coeffs: Vec<Value<Fp>> = test_list
            .clone()
            .into_iter()
            .map(|x| Value::known(Fp::from(x)))
            .collect();

        let point = Value::known(Fp::from(test_point));

        let circuit = PolyEvalCircuit { coeffs, point };

        let instance = poly_eval(test_list.to_vec(), test_point);

        let public_inputs = vec![Fp::from(instance)];

        // Given the correct public input, our circuit will verify.
        let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();

        assert_eq!(prover.verify(), Ok(()))
    }

    #[test]
    fn zero_coeff_check() {
        use rand::Rng;
        let test_list = (1..10).map(|_| 0).collect::<Vec<u64>>();
        let test_point = rand::thread_rng().gen_range(0..100) as u64;
        poly_sanity_check(test_list, test_point, 7)
    }

    #[test]
    fn zero_x_check() {
        use rand::Rng;
        let test_list = (1..10)
            .map(|_| rand::thread_rng().gen_range(0..100))
            .collect::<Vec<u64>>();
        let test_point: u64 = 0;
        poly_sanity_check(test_list, test_point, 7)
    }

    #[test]
    fn simple_check() {
        let test_list = vec![1, 2, 3];
        let test_point = 5;
        poly_sanity_check(test_list, test_point, 4)
    }

    #[test]
    fn random_check() {
        use rand::Rng;
        let test_list = (1..10)
            .map(|_| rand::thread_rng().gen_range(0..100))
            .collect::<Vec<u64>>();
        let test_point = rand::thread_rng().gen_range(0..100) as u64;
        poly_sanity_check(test_list, test_point, 7)
    }
}
