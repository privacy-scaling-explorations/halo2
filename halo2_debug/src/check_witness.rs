use crate::display::FDisp;
use halo2_middleware::circuit::{Any, CompiledCircuit, ExpressionMid, VarMid};
use halo2_middleware::ff::PrimeField;
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;
use std::collections::HashSet;

fn rotate(n: usize, offset: usize, rotation: i32) -> usize {
    let offset = offset as i32 + rotation;
    if offset < 0 {
        (offset + n as i32) as usize
    } else if offset >= n as i32 {
        (offset - n as i32) as usize
    } else {
        offset as usize
    }
}

struct Assignments<'a, F: PrimeField> {
    public: &'a [Vec<F>],
    witness: &'a [Vec<F>],
    fixed: &'a [Vec<F>],
    blinders: &'a [Vec<F>],
    blinded: &'a [bool],
    usable_rows: usize,
    n: usize,
}

impl<'a, F: PrimeField> Assignments<'a, F> {
    // Query a particular Column at an offset
    fn query(&self, column_type: Any, column_index: usize, offset: usize) -> F {
        match column_type {
            Any::Instance => self.public[column_index][offset],
            Any::Advice => {
                if offset >= self.usable_rows && self.blinded[column_index] {
                    self.blinders[column_index][offset - self.usable_rows]
                } else {
                    self.witness[column_index][offset]
                }
            }
            Any::Fixed => self.fixed[column_index][offset],
        }
    }

    // Evaluate an expression using the assignment data
    fn eval(&self, expr: &ExpressionMid<F>, offset: usize) -> F {
        expr.evaluate(
            &|s| s,
            &|v| match v {
                VarMid::Query(q) => {
                    let offset = rotate(self.n, offset, q.rotation.0);
                    self.query(q.column_type, q.column_index, offset)
                }
                VarMid::Challenge(_c) => unimplemented!(),
            },
            &|ne| -ne,
            &|a, b| a + b,
            &|a, b| a * b,
        )
    }

    // Evaluate multiple expressions and return the result as concatenated bytes from the field
    // element representation.
    fn eval_to_buf(&self, f_len: usize, exprs: &[ExpressionMid<F>], offset: usize) -> Vec<u8> {
        let mut eval_buf = Vec::with_capacity(exprs.len() * f_len);
        for eval in exprs.iter().map(|e| self.eval(e, offset)) {
            eval_buf.extend_from_slice(eval.to_repr().as_ref())
        }
        eval_buf
    }
}

/// Check that the wintess passes all the constraints defined by the circuit.  Panics if any
/// constraint is not satisfied.
pub fn check_witness<F: PrimeField>(
    circuit: &CompiledCircuit<F>,
    k: u32,
    blinding_rows: usize,
    witness: &[Vec<F>],
    public: &[Vec<F>],
) {
    let n = 2usize.pow(k);
    let usable_rows = n - blinding_rows;
    let cs = &circuit.cs;

    // Calculate blinding values
    let mut rng = ChaCha20Rng::seed_from_u64(0xdeadbeef);
    let mut blinders = vec![vec![F::ZERO; blinding_rows]; cs.num_advice_columns];
    for column_blinders in blinders.iter_mut() {
        for v in column_blinders.iter_mut() {
            *v = F::random(&mut rng);
        }
    }

    let mut blinded = vec![true; cs.num_advice_columns];
    for advice_column_index in &cs.unblinded_advice_columns {
        blinded[*advice_column_index] = false;
    }

    let assignments = Assignments {
        public,
        witness,
        fixed: &circuit.preprocessing.fixed,
        blinders: &blinders,
        blinded: &blinded,
        usable_rows,
        n,
    };

    // Verify all gates
    for (i, gate) in cs.gates.iter().enumerate() {
        for offset in 0..n {
            let res = assignments.eval(&gate.poly, offset);
            if !res.is_zero_vartime() {
                panic!(
                    "Unsatisfied gate {} \"{}\" at offset {}",
                    i, gate.name, offset
                );
            }
        }
    }

    // Verify all copy constraints
    for (lhs, rhs) in &circuit.preprocessing.permutation.copies {
        let value_lhs = assignments.query(lhs.column.column_type, lhs.column.index, lhs.row);
        let value_rhs = assignments.query(rhs.column.column_type, rhs.column.index, rhs.row);
        if value_lhs != value_rhs {
            panic!(
                "Unsatisfied copy constraint ({:?},{:?}): {} != {}",
                lhs,
                rhs,
                FDisp(&value_lhs),
                FDisp(&value_rhs)
            )
        }
    }

    // Verify all lookups
    let f_len = F::Repr::default().as_ref().len();
    for (i, lookup) in cs.lookups.iter().enumerate() {
        let mut virtual_table = HashSet::new();
        for offset in 0..usable_rows {
            let table_eval_buf = assignments.eval_to_buf(f_len, &lookup.table_expressions, offset);
            virtual_table.insert(table_eval_buf);
        }
        for offset in 0..usable_rows {
            let input_eval_buf = assignments.eval_to_buf(f_len, &lookup.input_expressions, offset);
            if !virtual_table.contains(&input_eval_buf) {
                panic!(
                    "Unsatisfied lookup {} \"{}\" at offset {}",
                    i, lookup.name, offset
                );
            }
        }
    }

    // Verify all shuffles
    for (i, shuffle) in cs.shuffles.iter().enumerate() {
        let mut virtual_shuffle = Vec::with_capacity(usable_rows);
        for offset in 0..usable_rows {
            let shuffle_eval_buf =
                assignments.eval_to_buf(f_len, &shuffle.shuffle_expressions, offset);
            virtual_shuffle.push(shuffle_eval_buf);
        }
        let mut virtual_input = Vec::with_capacity(usable_rows);
        for offset in 0..usable_rows {
            let input_eval_buf = assignments.eval_to_buf(f_len, &shuffle.input_expressions, offset);
            virtual_input.push(input_eval_buf);
        }

        virtual_shuffle.sort_unstable();
        virtual_input.sort_unstable();

        if virtual_input != virtual_shuffle {
            panic!("Unsatisfied shuffle {} \"{}\"", i, shuffle.name);
        }
    }
}
