use crate::circuit::{batch_invert_assigned, Value};
use crate::plonk::{
    sealed::{self, SealedPhase},
    Advice, Assigned, Assignment, Challenge, Circuit, Column, ConstraintSystem, Error, FirstPhase,
    Fixed, FloorPlanner, Instance, SecondPhase, Selector, ThirdPhase,
};
use halo2_middleware::circuit::Any;
use halo2_middleware::ff::Field;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::fmt::Debug;
use std::ops::RangeTo;

struct WitnessCollection<'a, F: Field> {
    k: u32,
    current_phase: sealed::Phase,
    advice_column_phase: &'a Vec<sealed::Phase>,
    advice: Vec<Vec<Assigned<F>>>,
    challenges: &'a HashMap<usize, F>,
    instances: &'a [&'a [F]],
    usable_rows: RangeTo<usize>,
}

impl<'a, F: Field> Assignment<F> for WitnessCollection<'a, F> {
    fn enter_region<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about regions in this context.
    }

    fn exit_region(&mut self) {
        // Do nothing; we don't care about regions in this context.
    }

    fn enable_selector<A, AR>(&mut self, _: A, _: &Selector, _: usize) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // We only care about advice columns here

        Ok(())
    }

    fn annotate_column<A, AR>(&mut self, _annotation: A, _column: Column<Any>)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // Do nothing
    }

    fn query_instance(&self, column: Column<Instance>, row: usize) -> Result<Value<F>, Error> {
        if !self.usable_rows.contains(&row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        self.instances
            .get(column.index())
            .and_then(|column| column.get(row))
            .map(|v| Value::known(*v))
            .ok_or(Error::BoundsFailure)
    }

    fn assign_advice<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<Advice>,
        row: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // Ignore assignment of advice column in different phase than current one.
        let phase = self.advice_column_phase[column.index];
        if self.current_phase != phase {
            return Ok(());
        }

        if !self.usable_rows.contains(&row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        *self
            .advice
            .get_mut(column.index())
            .and_then(|v| v.get_mut(row))
            .ok_or(Error::BoundsFailure)? = to().into_field().assign()?;

        Ok(())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        _: A,
        _: Column<Fixed>,
        _: usize,
        _: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // We only care about advice columns here

        Ok(())
    }

    fn copy(&mut self, _: Column<Any>, _: usize, _: Column<Any>, _: usize) -> Result<(), Error> {
        // We only care about advice columns here

        Ok(())
    }

    fn fill_from_row(
        &mut self,
        _: Column<Fixed>,
        _: usize,
        _: Value<Assigned<F>>,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn get_challenge(&self, challenge: Challenge) -> Value<F> {
        self.challenges
            .get(&challenge.index())
            .cloned()
            .map(Value::known)
            .unwrap_or_else(Value::unknown)
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn pop_namespace(&mut self, _: Option<String>) {
        // Do nothing; we don't care about namespaces in this context.
    }
}

/// Witness calculator.  Frontend function
#[derive(Debug)]
pub struct WitnessCalculator<'a, F: Field, ConcreteCircuit: Circuit<F>> {
    k: u32,
    n: usize,
    unusable_rows_start: usize,
    circuit: &'a ConcreteCircuit,
    config: &'a ConcreteCircuit::Config,
    cs: &'a ConstraintSystem<F>,
    instances: &'a [&'a [F]],
    next_phase: u8,
}

impl<'a, F: Field, ConcreteCircuit: Circuit<F>> WitnessCalculator<'a, F, ConcreteCircuit> {
    /// Create a new WitnessCalculator
    pub fn new(
        k: u32,
        circuit: &'a ConcreteCircuit,
        config: &'a ConcreteCircuit::Config,
        cs: &'a ConstraintSystem<F>,
        instances: &'a [&'a [F]],
    ) -> Self {
        let n = 2usize.pow(k);
        let unusable_rows_start = n - (cs.blinding_factors() + 1);
        Self {
            k,
            n,
            unusable_rows_start,
            circuit,
            config,
            cs,
            instances,
            next_phase: 0,
        }
    }

    /// Calculate witness at phase
    pub fn calc(
        &mut self,
        phase: u8,
        challenges: &HashMap<usize, F>,
    ) -> Result<Vec<Option<Vec<F>>>, Error> {
        if phase != self.next_phase {
            return Err(Error::Other(format!(
                "Expected phase {}, got {}",
                self.next_phase, phase
            )));
        }
        let current_phase = match phase {
            0 => FirstPhase.to_sealed(),
            1 => SecondPhase.to_sealed(),
            2 => ThirdPhase.to_sealed(),
            _ => unreachable!("only phase [0,2] supported"),
        };

        let mut witness = WitnessCollection {
            k: self.k,
            current_phase,
            advice_column_phase: &self.cs.advice_column_phase,
            advice: vec![vec![Assigned::Zero; self.n]; self.cs.num_advice_columns],
            instances: self.instances,
            challenges,
            // The prover will not be allowed to assign values to advice
            // cells that exist within inactive rows, which include some
            // number of blinding factors and an extra row for use in the
            // permutation argument.
            usable_rows: ..self.unusable_rows_start,
        };

        // Synthesize the circuit to obtain the witness and other information.
        ConcreteCircuit::FloorPlanner::synthesize(
            &mut witness,
            self.circuit,
            self.config.clone(),
            self.cs.constants.clone(),
        )
        .expect("todo");

        let column_indices = self
            .cs
            .advice_column_phase
            .iter()
            .enumerate()
            .filter_map(|(column_index, phase)| {
                if current_phase == *phase {
                    Some(column_index)
                } else {
                    None
                }
            })
            .collect::<BTreeSet<_>>();

        self.next_phase += 1;
        let advice_values = batch_invert_assigned(witness.advice);
        Ok(advice_values
            .into_iter()
            .enumerate()
            .map(|(column_index, advice)| {
                if column_indices.contains(&column_index) {
                    Some(advice)
                } else {
                    None
                }
            })
            .collect())
    }
}
