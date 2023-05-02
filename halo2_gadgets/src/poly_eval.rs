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
const URINDEX: usize = 0;
const COEFFINDEX: usize = 1;
const POWXINDEX: usize = 2;
const RESINDEX: usize = 3;
const ACCINDEX: usize = 4;
// As end of the layout
const EVALADVCOL: usize = ACCINDEX + 1;

/// Polynomial represents in coeffs, [c0, c1, c2, ...] 
/// P[x] = c0 * 1 + c1 * x + c2 * x^2 + ... cn * x^n
/// where x is in a Fp, c_i could be chosen another group
/// or field to conduct a Field extension, but not necessarily here
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
    fn eval(&self, layouter: impl Layouter<F>, coeffs: Vec<Self::Coeff>, elem: Self::Elem) -> Result<Self::Elem, Error>;
    
}

/// Chip for poly eval
#[derive(Clone, Debug)]
pub struct PolyEvalConfig {
    /// column layput | eval point | coeff | pow of point | result | accumulative result |
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
            // namely, The starting acc calucation must begin with an inital `acc` with zero value
            let init_acc_clone = meta.query_advice(advice[ACCINDEX], Rotation::cur());
            let next_acc = meta.query_advice(advice[ACCINDEX], Rotation::next());
            let next_res = meta.query_advice(advice[RESINDEX], Rotation::next());
            let zero_s_clone = meta.query_selector(zero_sel);

            // First, to constrain init acc is zero;
            // Second, to make sure init acc is guaranteed to be used in following calculation
            vec![zero_s * init_acc, zero_s_clone * (next_res + init_acc_clone - next_acc)]
        });

        meta.create_gate("x pow", |meta| {
            let unit_of_root = meta.query_advice(advice[URINDEX], Rotation::cur()); 
            let cur_x = meta.query_advice(advice[POWXINDEX], Rotation::cur());
            let next_x = meta.query_advice(advice[POWXINDEX], Rotation::next());
            let pow_s = meta.query_selector(e_sel);

            vec![pow_s * (next_x - cur_x * unit_of_root)]
        });

        meta.create_gate("addition for res", |meta| {
            let coeff = meta.query_advice(advice[COEFFINDEX], Rotation::cur());
            let elem = meta.query_advice(advice[POWXINDEX], Rotation::cur());
            let res = meta.query_advice(advice[RESINDEX], Rotation::cur());
            let add_s = meta.query_selector(e_sel);

            vec![add_s * (res - coeff * elem)]
        });

        meta.create_gate("acc", |meta| {
            let prev_acc = meta.query_advice(advice[ACCINDEX], Rotation::prev());
            let cur_acc = meta.query_advice(advice[ACCINDEX], Rotation::cur());
            let res = meta.query_advice(advice[RESINDEX], Rotation::cur());
            let acc_s = meta.query_selector(e_sel);

            vec![acc_s * (cur_acc - (res + prev_acc))]
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
    type Coeff = AssignedCell<F,F>;
    type Elem = AssignedCell<F,F>;

    fn load_element(&self, mut layouter: impl Layouter<F>, a: Value<F>) -> Result<Self::Elem, Error> {
        let config = self.config();

        layouter.assign_region(|| "load eval point", |mut region: Region<F>| {
            region.assign_advice(|| "eval point value", config.advice[URINDEX], 0,|| a)
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
                || "init acc to zero",config.advice[ACCINDEX],
                0, ||Value::known(F::ZERO))?;
            let mut pow_x = Value::known(F::ONE);
            config.zero_sel.enable(&mut region, 0)?;

            // Assign the advice according to the coeff list
            for (i, coeff) in coeffs.iter().enumerate() {
                // Since our region starts at an aux row which only stores an init acc(F::ZERO)
                let offset = i + 1;
                config.e_sel.enable(&mut region, offset)?;

                // Constraint on a fixed unit of root
                elem.copy_advice(
                    || format!("unit of root on {}", i),
                    &mut region,
                    config.advice[URINDEX],
                    offset,
                )?; 

                // Constrain coeff
                coeff.copy_advice(
                    || format!("coeff {}", i),
                    &mut region,
                    config.advice[COEFFINDEX],
                    offset,
                )?;

                // Assgin x exponentiation
                region.assign_advice(
                    || format!("x power {}", i),
                    config.advice[POWXINDEX],
                    offset,
                    || pow_x
                )?;

                // Calculate the current result
                let res = region.assign_advice(
                    || format!("res {}", i),
                    config.advice[RESINDEX],
                    offset,
                    || coeff.clone().value().copied() * pow_x
                )?;

                // At end of each turn, assign acc and store it
                let prev_acc_value = acc.value().copied();
                acc = region.assign_advice(
                    || format!("acc {}", i),
                    config.advice[ACCINDEX],
                    offset,
                    || prev_acc_value + res.value()
                )?;

                // Step pow_x with another mul per se
                pow_x = pow_x * elem.clone().value().copied();
            }
            
            // Since we use only one selector on 3 gates, then we have to satisfy gate `pow x`
            // by providing one more row
            region.assign_advice(
                || format!("final row for pow x gate {}",coeffs.len()),
                config.advice[POWXINDEX],
                coeffs.len() + 1,
                || pow_x
            )?;

            Ok(acc)
        })
    }

} 

#[cfg(test)]
mod tests {
  use crate::poly_eval::*;
  use halo2_proofs::{
      arithmetic::Field,
      circuit::{AssignedCell, Chip, Layouter, Region, SimpleFloorPlanner, Value},
      plonk::{Circuit, ConstraintSystem, Instance, Error},
  };
  use halo2_proofs::dev::MockProver;
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

    fn eval(&self, layouter: impl Layouter<F>, coeffs: Vec<Self::Coeff>, elem: Self::Elem) -> Result<Self::Elem, Error> {
        let config = self.config().polyevalconfig.clone();
        let polyevalchip = PolyEvalChip::<F>::construct(config);
        polyevalchip.eval(layouter, coeffs, elem)
    }
    
    fn load_element(&self, layouter: impl Layouter<F>, a: Value<F>) -> Result<Self::Elem, Error> {
        let config = self.config().polyevalconfig.clone();
        let polyevalchip = PolyEvalChip::<F>::construct(config);
        polyevalchip.load_element(layouter, a) 
    }
  }

  /// Impl basic construct
  impl<F: Field> PolyEvalExtChip<F> {
    fn construct(config: <Self as Chip<F>>::Config, _loaded: <Self as Chip<F>>::Loaded) -> Self {
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
          list: &Vec<Value<F>>,
      ) -> Result<Vec<AssignedCell<F,F>>, Error> {
          let config = self.config().polyevalconfig.clone();
          let mut coeffs: Vec<AssignedCell<F,F>> = vec![];

          for (i, coeff) in list.iter().enumerate() {
              let cell_coeff = layouter.assign_region(
                  || format!("coeff region {}", i),
                  |mut region: Region<F>| {
                      region.assign_advice(
                        || format!("load coeff {}", i),
                        config.advice[COEFFINDEX],
                        0, 
                        || *coeff
                    )
                  })?;
              coeffs.push(cell_coeff);
          }

          Ok(coeffs)
      }

    fn reveal(&self, mut layouter: impl Layouter<F>, elem: AssignedCell<F, F>, row: usize) -> Result<(), Error> {
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

  impl<F:Field> Circuit<F> for PolyEvalCircuit<F> {
      type Config = PolyEvalExtConfig;
      type FloorPlanner = SimpleFloorPlanner;

      fn without_witnesses(&self) -> Self {
          Self::default()
      }

      fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
          let advice = [meta.advice_column(), meta.advice_column(), meta.advice_column(),
                                             meta.advice_column(), meta.advice_column()];

          let instance = meta.instance_column();

          PolyEvalExtChip::configure(meta, advice, instance)
      }

      fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
          let chip = PolyEvalExtChip::<F>::construct(config, ());

          let coeff_cells = chip.load_coeffs(layouter.namespace(|| "load coeffs in syn"), &self.coeffs).unwrap();

          let point_cell = chip.load_element(layouter.namespace(|| "load eval point in syn"), self.point).unwrap();

          let evaluation = chip.eval(layouter.namespace(|| "eval in syn"), coeff_cells, point_cell).unwrap();

          chip.reveal(layouter.namespace(|| "reveal"), evaluation, 0)

      }
  }

  fn poly_eval(coeffs: Vec<u64>, x :u64) -> u64 {
      let mut acc = 0;
      let mut temp = 1;
      for coeff in coeffs {
          acc += coeff * temp;
          temp *= x;
      }
      acc
  }


  #[test]
  fn poly_sanity_check() {
      let k = 4;

      let test_list = [1,2,3];
      let test_point = 5;

      let coeffs: Vec<Value<Fp>> = test_list.clone().into_iter().map(|x| {Value::known(Fp::from(x))}).collect();

      let point = Value::known(Fp::from(test_point));

      let circuit = PolyEvalCircuit {
          coeffs: coeffs,
          point: point,
      };

      let instance = poly_eval(test_list.to_vec(), test_point);

      let public_inputs = vec![Fp::from(instance)];

       // Given the correct public input, our circuit will verify.
      let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();

      assert_eq!(prover.verify(), Ok(()))
   
  }
}