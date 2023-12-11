//! The cost estimator takes high-level parameters for a circuit design, and estimates the
//! verification cost, as well as resulting proof size.

use std::{cmp, iter, num::ParseIntError, str::FromStr};

use crate::plonk::Circuit;
use ff::{Field, FromUniformBytes};

use super::MockProver;

/// Options to build a circuit specifiction to measure the cost model of.
#[derive(Debug)]
pub struct CostOptions {
    /// An advice column with the given rotations. May be repeated.
    pub advice: Vec<Poly>,

    /// An instance column with the given rotations. May be repeated.
    pub instance: Vec<Poly>,

    /// A fixed column with the given rotations. May be repeated.
    pub fixed: Vec<Poly>,

    /// Maximum degree of the custom gates.
    pub gate_degree: usize,

    /// A lookup over N columns with max input degree I and max table degree T. May be repeated.
    pub lookup: Vec<Lookup>,

    /// A permutation over N columns. May be repeated.
    pub permutation: Vec<Permutation>,

    /// 2^K bound on the number of rows.
    pub k: usize,
}

/// Structure holding polynomial related data for benchmarks
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Poly {
    /// Rotations for the given polynomial
    pub rotations: Vec<isize>,
}

impl FromStr for Poly {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut rotations: Vec<isize> =
            s.split(',').map(|r| r.parse()).collect::<Result<_, _>>()?;
        rotations.sort_unstable();
        Ok(Poly { rotations })
    }
}

/// Structure holding the Lookup related data for circuit benchmarks.
#[derive(Debug, Clone)]
pub struct Lookup {
    _columns: usize,
    input_deg: usize,
    table_deg: usize,
}

impl FromStr for Lookup {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut parts = s.split(',');
        let _columns = parts.next().unwrap().parse()?;
        let input_deg = parts.next().unwrap().parse()?;
        let table_deg = parts.next().unwrap().parse()?;
        Ok(Lookup {
            _columns,
            input_deg,
            table_deg,
        })
    }
}

impl Lookup {
    fn required_degree(&self) -> usize {
        2 + cmp::max(1, self.input_deg) + cmp::max(1, self.table_deg)
    }

    fn queries(&self) -> impl Iterator<Item = Poly> {
        // - product commitments at x and x_inv
        // - input commitments at x and x_inv
        // - table commitments at x
        let product = "0,-1".parse().unwrap();
        let input = "0,-1".parse().unwrap();
        let table = "0".parse().unwrap();

        iter::empty()
            .chain(Some(product))
            .chain(Some(input))
            .chain(Some(table))
    }
}

/// Number of permutation enabled columns
#[derive(Debug, Clone)]
pub struct Permutation {
    columns: usize,
}

impl FromStr for Permutation {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Permutation {
            columns: s.parse()?,
        })
    }
}

impl Permutation {
    fn required_degree(&self) -> usize {
        cmp::max(self.columns + 1, 2)
    }

    fn queries(&self) -> impl Iterator<Item = Poly> {
        // - product commitments at x and x_inv
        // - polynomial commitments at x
        let product = "0,-1".parse().unwrap();
        let poly = "0".parse().unwrap();

        iter::empty()
            .chain(Some(product))
            .chain(iter::repeat(poly).take(self.columns))
    }
}

/// High-level specifications of an abstract circuit.
#[derive(Debug)]
pub struct ModelCircuit {
    /// Power-of-2 bound on the number of rows in the circuit.
    pub k: usize,
    /// Maximum degree of the circuit.
    pub max_deg: usize,
    /// Number of advice columns.
    pub advice_columns: usize,
    /// Number of lookup arguments.
    pub lookups: usize,
    /// Equality constraint permutation arguments.
    pub permutations: Vec<Permutation>,
    /// Number of distinct column queries across all gates.
    pub column_queries: usize,
    /// Number of distinct sets of points in the multiopening argument.
    pub point_sets: usize,
}

impl From<CostOptions> for ModelCircuit {
    fn from(opts: CostOptions) -> Self {
        let max_deg = [1, opts.gate_degree]
            .iter()
            .cloned()
            .chain(opts.lookup.iter().map(|l| l.required_degree()))
            .chain(opts.permutation.iter().map(|p| p.required_degree()))
            .max()
            .unwrap();

        let mut queries: Vec<_> = iter::empty()
            .chain(opts.advice.iter())
            .chain(opts.instance.iter())
            .chain(opts.fixed.iter())
            .cloned()
            .chain(opts.lookup.iter().flat_map(|l| l.queries()))
            .chain(opts.permutation.iter().flat_map(|p| p.queries()))
            .chain(iter::repeat("0".parse().unwrap()).take(max_deg - 1))
            .collect();

        let column_queries = queries.len();
        queries.sort_unstable();
        queries.dedup();
        let point_sets = queries.len();

        ModelCircuit {
            k: opts.k,
            max_deg,
            advice_columns: opts.advice.len(),
            lookups: opts.lookup.len(),
            permutations: opts.permutation,
            column_queries,
            point_sets,
        }
    }
}

impl ModelCircuit {
    /// Size of the proof in bytes
    pub fn proof_size(&self) -> usize {
        let size = |points: usize, scalars: usize| points * 32 + scalars * 32;

        // PLONK:
        // - 32 bytes (commitment) per advice column
        // - 3 * 32 bytes (commitments) + 5 * 32 bytes (evals) per lookup argument
        // - 32 bytes (commitment) + 2 * 32 bytes (evals) per permutation argument
        // - 32 bytes (eval) per column per permutation argument
        let plonk = size(1, 0) * self.advice_columns
            + size(3, 5) * self.lookups
            + self
                .permutations
                .iter()
                .map(|p| size(1, 2 + p.columns))
                .sum::<usize>();

        // Vanishing argument:
        // - (max_deg - 1) * 32 bytes (commitments) + (max_deg - 1) * 32 bytes (h_evals)
        //   for quotient polynomial
        // - 32 bytes (eval) per column query
        let vanishing = size(self.max_deg - 1, self.max_deg - 1) + size(0, self.column_queries);

        // Multiopening argument:
        // - f_commitment (32 bytes)
        // - 32 bytes (evals) per set of points in multiopen argument
        let multiopen = size(1, self.point_sets);

        // Polycommit:
        // - s_poly commitment (32 bytes)
        // - inner product argument (k rounds * 2 * 32 bytes)
        // - a (32 bytes)
        // - xi (32 bytes)
        let polycomm = size(1 + 2 * self.k, 2);

        plonk + vanishing + multiopen + polycomm
    }

    /// Generate a report.
    pub fn report(&self) -> String {
        let mut str = String::new();
        str.push_str(&format!("{:#?}", self));
        str.push_str(&format!("Proof size: {} bytes", self.proof_size()));
        str
    }

    /// Write a CSV report
    pub fn report_csv<W: std::io::Write>(&self, w: &mut W) -> std::io::Result<()> {
        let mut w = csv::Writer::from_writer(w);
        w.write_record(["max_deg", &self.max_deg.to_string()])?;
        w.write_record(["advice_columns", &self.advice_columns.to_string()])?;
        w.write_record(["lookups", &self.lookups.to_string()])?;
        w.write_record(["permutations", &{
            let mut str = String::new();
            for p in self.permutations.iter() {
                str.push_str(&format!(" {}", p.columns));
            }
            str
        }])?;
        w.write_record(["column_queries", &self.column_queries.to_string()])?;
        w.write_record(["point_sets", &self.point_sets.to_string()])?;
        w.write_record(["proof_size", &self.proof_size().to_string()])?;
        Ok(())
    }
}

/// Given a Plonk circuit, this function returns a [ModelCircuit]
pub fn from_circuit_to_model_circuit<F: Ord + Field + FromUniformBytes<64>, C: Circuit<F>>(
    k: u32,
    circuit: &C,
    instances: Vec<Vec<F>>,
) -> ModelCircuit {
    let options = from_circuit_to_cost_model_options(k, circuit, instances);
    ModelCircuit::from(options)
}

/// Given a Plonk circuit, this function returns [CostOptions]
pub fn from_circuit_to_cost_model_options<F: Ord + Field + FromUniformBytes<64>, C: Circuit<F>>(
    k: u32,
    circuit: &C,
    instances: Vec<Vec<F>>,
) -> CostOptions {
    let prover = MockProver::run(k, circuit, instances).unwrap();
    let cs = prover.cs;

    let fixed = {
        // init the fixed polynomials with no rotations
        let mut fixed = vec![Poly { rotations: vec![] }; cs.num_fixed_columns()];
        for (col, rot) in cs.fixed_queries() {
            fixed[col.index()].rotations.push(rot.0 as isize);
        }
        fixed
    };

    let advice = {
        // init the advice polynomials with no rotations
        let mut advice = vec![Poly { rotations: vec![] }; cs.num_advice_columns()];
        for (col, rot) in cs.advice_queries() {
            advice[col.index()].rotations.push(rot.0 as isize);
        }
        advice
    };

    let instance = {
        // init the instance polynomials with no rotations
        let mut instance = vec![Poly { rotations: vec![] }; cs.num_instance_columns()];
        for (col, rot) in cs.instance_queries() {
            instance[col.index()].rotations.push(rot.0 as isize);
        }
        instance
    };

    let lookup = {
        let mut lookup = vec![];
        for l in cs.lookups().iter() {
            lookup.push(Lookup {
                // this isn't actually used for estimation right now, so ignore it.
                _columns: 1,
                input_deg: l.input_expressions().len(),
                table_deg: l.table_expressions().len(),
            });
        }
        lookup
    };

    let permutation = vec![Permutation {
        columns: cs.permutation().get_columns().len(),
    }];

    let gate_degree = cs.degree();

    let k = prover.k.try_into().unwrap();

    CostOptions {
        advice,
        instance,
        fixed,
        gate_degree,
        lookup,
        permutation,
        k,
    }
}
