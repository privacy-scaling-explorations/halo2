//! Developer tools for investigating the cost of a circuit.

use std::{
    cmp,
    collections::{HashMap, HashSet},
    iter,
    marker::PhantomData,
    ops::{Add, Mul},
};

use group::prime::PrimeGroup;
use halo2_middleware::circuit::Any;
use halo2_middleware::ff::{Field, PrimeField};
use halo2_middleware::poly::Rotation;

use crate::{
    circuit::{layouter::RegionColumn, Value},
    plonk::{
        Advice, Assigned, Assignment, Challenge, Circuit, Column, ConstraintSystem, Error, Fixed,
        FloorPlanner, Instance, Selector,
    },
};

/// Measures a circuit to determine its costs, and explain what contributes to them.
#[allow(dead_code)]
#[derive(Debug)]
pub struct CircuitCost<G: PrimeGroup, ConcreteCircuit: Circuit<G::Scalar>> {
    /// Power-of-2 bound on the number of rows in the circuit.
    k: u32,
    /// Maximum degree of the circuit.
    max_deg: usize,
    /// Number of advice columns.
    advice_columns: usize,
    /// Number of direct queries for each column type.
    instance_queries: usize,
    advice_queries: usize,
    fixed_queries: usize,
    /// Number of lookup arguments.
    lookups: usize,
    /// Number of columns in the global permutation.
    permutation_cols: usize,
    /// Number of distinct sets of points in the multiopening argument.
    point_sets: usize,
    /// Maximum rows used over all columns
    max_rows: usize,
    /// Maximum rows used over all advice columns
    max_advice_rows: usize,
    /// Maximum rows used over all fixed columns
    max_fixed_rows: usize,
    num_fixed_columns: usize,
    num_advice_columns: usize,
    num_instance_columns: usize,
    num_total_columns: usize,

    _marker: PhantomData<(G, ConcreteCircuit)>,
}

/// Region implementation used by Layout
#[allow(dead_code)]
#[derive(Debug)]
pub(crate) struct LayoutRegion {
    /// The name of the region. Not required to be unique.
    pub(crate) name: String,
    /// The columns used by this region.
    pub(crate) columns: HashSet<RegionColumn>,
    /// The row that this region starts on, if known.
    pub(crate) offset: Option<usize>,
    /// The number of rows that this region takes up.
    pub(crate) rows: usize,
    /// The cells assigned in this region.
    pub(crate) cells: Vec<(RegionColumn, usize)>,
}

/// Cost and graphing layouter
#[derive(Default, Debug)]
pub(crate) struct Layout {
    /// k = 1 << n
    pub(crate) k: u32,
    /// Regions of the layout
    pub(crate) regions: Vec<LayoutRegion>,
    current_region: Option<usize>,
    /// Total row count
    pub(crate) total_rows: usize,
    /// Total advice rows
    pub(crate) total_advice_rows: usize,
    /// Total fixed rows
    pub(crate) total_fixed_rows: usize,
    /// Any cells assigned outside of a region.
    pub(crate) loose_cells: Vec<(RegionColumn, usize)>,
    /// Pairs of cells between which we have equality constraints.
    pub(crate) equality: Vec<(Column<Any>, usize, Column<Any>, usize)>,
    /// Selector assignments used for optimization pass
    pub(crate) selectors: Vec<Vec<bool>>,
}

impl Layout {
    /// Creates a empty layout
    pub(crate) fn new(k: u32, n: usize, num_selectors: usize) -> Self {
        Layout {
            k,
            regions: vec![],
            current_region: None,
            total_rows: 0,
            total_advice_rows: 0,
            total_fixed_rows: 0,
            // Any cells assigned outside of a region.
            loose_cells: vec![],
            // Pairs of cells between which we have equality constraints.
            equality: vec![],
            // Selector assignments used for optimization pass
            selectors: vec![vec![false; n]; num_selectors],
        }
    }

    /// Update layout metadata
    pub(crate) fn update(&mut self, column: RegionColumn, row: usize) {
        self.total_rows = cmp::max(self.total_rows, row + 1);

        if let RegionColumn::Column(col) = column {
            match col.column_type() {
                Any::Advice => self.total_advice_rows = cmp::max(self.total_advice_rows, row + 1),
                Any::Fixed => self.total_fixed_rows = cmp::max(self.total_fixed_rows, row + 1),
                _ => {}
            }
        }

        if let Some(region) = self.current_region {
            let region = &mut self.regions[region];
            region.columns.insert(column);

            // The region offset is the earliest row assigned to.
            let mut offset = region.offset.unwrap_or(row);
            if row < offset {
                // The first row assigned was not at offset 0 within the region.
                region.rows += offset - row;
                offset = row;
            }
            // The number of rows in this region is the gap between the earliest and
            // latest rows assigned.
            region.rows = cmp::max(region.rows, row - offset + 1);
            region.offset = Some(offset);

            region.cells.push((column, row));
        } else {
            self.loose_cells.push((column, row));
        }
    }
}

impl<F: Field> Assignment<F> for Layout {
    fn enter_region<NR, N>(&mut self, name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        assert!(self.current_region.is_none());
        self.current_region = Some(self.regions.len());
        self.regions.push(LayoutRegion {
            name: name_fn().into(),
            columns: HashSet::default(),
            offset: None,
            rows: 0,
            cells: vec![],
        })
    }

    fn annotate_column<A, AR>(&mut self, _: A, _: Column<Any>)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
    }

    fn exit_region(&mut self) {
        assert!(self.current_region.is_some());
        self.current_region = None;
    }

    fn enable_selector<A, AR>(&mut self, _: A, selector: &Selector, row: usize) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if let Some(cell) = self.selectors[selector.0].get_mut(row) {
            *cell = true;
        } else {
            return Err(Error::not_enough_rows_available(self.k));
        }

        self.update((*selector).into(), row);
        Ok(())
    }

    fn query_instance(&self, _: Column<Instance>, _: usize) -> Result<Value<F>, Error> {
        Ok(Value::unknown())
    }

    fn assign_advice<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<Advice>,
        row: usize,
        _: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.update(Column::<Any>::from(column).into(), row);
        Ok(())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<Fixed>,
        row: usize,
        _: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.update(Column::<Any>::from(column).into(), row);
        Ok(())
    }

    fn copy(
        &mut self,
        l_col: Column<Any>,
        l_row: usize,
        r_col: Column<Any>,
        r_row: usize,
    ) -> Result<(), crate::plonk::Error> {
        self.equality.push((l_col, l_row, r_col, r_row));
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

    fn get_challenge(&self, _: Challenge) -> Value<F> {
        Value::unknown()
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

impl<G: PrimeGroup, ConcreteCircuit: Circuit<G::Scalar>> CircuitCost<G, ConcreteCircuit> {
    /// Measures a circuit with parameter constant `k`.
    ///
    /// Panics if `k` is not large enough for the circuit.
    pub fn measure(k: u32, circuit: &ConcreteCircuit) -> Self {
        // Collect the layout details.
        let mut cs = ConstraintSystem::default();
        let config = ConcreteCircuit::configure(&mut cs);
        let mut layout = Layout::new(k, 1 << k, cs.num_selectors);
        ConcreteCircuit::FloorPlanner::synthesize(
            &mut layout,
            circuit,
            config,
            cs.constants.clone(),
        )
        .unwrap();
        let (cs, _) = cs.compress_selectors(layout.selectors);

        assert!((1 << k) >= cs.minimum_rows());

        // Figure out how many point sets we have due to queried cells.
        let mut column_queries: HashMap<Column<Any>, HashSet<i32>> = HashMap::new();
        for (c, r) in iter::empty()
            .chain(
                cs.advice_queries
                    .iter()
                    .map(|(c, r)| (Column::<Any>::from(*c), *r)),
            )
            .chain(cs.instance_queries.iter().map(|(c, r)| ((*c).into(), *r)))
            .chain(cs.fixed_queries.iter().map(|(c, r)| ((*c).into(), *r)))
            .chain(
                cs.permutation
                    .get_columns()
                    .into_iter()
                    .map(|c| (c, Rotation::cur())),
            )
        {
            column_queries.entry(c).or_default().insert(r.0);
        }
        let mut point_sets: HashSet<Vec<i32>> = HashSet::new();
        for (_, r) in column_queries {
            // Sort the query sets so we merge duplicates.
            let mut query_set: Vec<_> = r.into_iter().collect();
            query_set.sort_unstable();
            point_sets.insert(query_set);
        }

        // Include lookup polynomials in point sets:
        point_sets.insert(vec![0, 1]); // product_poly
        point_sets.insert(vec![-1, 0]); // permuted_input_poly
        point_sets.insert(vec![0]); // permuted_table_poly

        // Include permutation polynomials in point sets.
        point_sets.insert(vec![0, 1]); // permutation_product_poly
        let max_deg = cs.degree();
        let permutation_cols = cs.permutation.get_columns().len();
        if permutation_cols > max_deg - 2 {
            // permutation_product_poly for chaining chunks.
            point_sets.insert(vec![-((cs.blinding_factors() + 1) as i32), 0, 1]);
        }

        CircuitCost {
            k,
            max_deg,
            advice_columns: cs.num_advice_columns,
            instance_queries: cs.instance_queries.len(),
            advice_queries: cs.advice_queries.len(),
            fixed_queries: cs.fixed_queries.len(),
            lookups: cs.lookups.len(),
            permutation_cols,
            point_sets: point_sets.len(),
            max_rows: layout.total_rows,
            max_advice_rows: layout.total_advice_rows,
            max_fixed_rows: layout.total_fixed_rows,
            num_advice_columns: cs.num_advice_columns,
            num_fixed_columns: cs.num_fixed_columns,
            num_instance_columns: cs.num_instance_columns,
            num_total_columns: cs.num_instance_columns
                + cs.num_advice_columns
                + cs.num_fixed_columns,
            _marker: PhantomData,
        }
    }

    fn permutation_chunks(&self) -> usize {
        let chunk_size = self.max_deg - 2;
        (self.permutation_cols + chunk_size - 1) / chunk_size
    }

    /// Returns the marginal proof size per instance of this circuit.
    pub fn marginal_proof_size(&self) -> MarginalProofSize<G> {
        let chunks = self.permutation_chunks();

        MarginalProofSize {
            // Cells:
            // - 1 commitment per advice column per instance
            // - 1 eval per instance column query per instance
            // - 1 eval per advice column query per instance
            instance: ProofContribution::new(0, self.instance_queries),
            advice: ProofContribution::new(self.advice_columns, self.advice_queries),

            // Lookup arguments:
            // - 3 commitments per lookup argument per instance
            // - 5 evals per lookup argument per instance
            lookups: ProofContribution::new(3 * self.lookups, 5 * self.lookups),

            // Global permutation argument:
            // - chunks commitments per instance
            // - 2 * chunks + (chunks - 1) evals per instance
            equality: ProofContribution::new(
                chunks,
                if chunks == 0 { chunks } else { 3 * chunks - 1 },
            ),

            _marker: PhantomData,
        }
    }

    /// Returns the proof size for the given number of instances of this circuit.
    pub fn proof_size(&self, instances: usize) -> ProofSize<G> {
        let marginal = self.marginal_proof_size();

        ProofSize {
            // Cells:
            // - marginal cost per instance
            // - 1 eval per fixed column query
            instance: marginal.instance * instances,
            advice: marginal.advice * instances,
            fixed: ProofContribution::new(0, self.fixed_queries),

            // Lookup arguments:
            // - marginal cost per instance
            lookups: marginal.lookups * instances,

            // Global permutation argument:
            // - marginal cost per instance
            // - 1 eval per column
            equality: marginal.equality * instances
                + ProofContribution::new(0, self.permutation_cols),

            // Vanishing argument:
            // - 1 + (max_deg - 1) commitments
            // - 1 random_poly eval
            vanishing: ProofContribution::new(self.max_deg, 1),

            // Multiopening argument:
            // - f_commitment
            // - 1 eval per set of points in multiopen argument
            multiopen: ProofContribution::new(1, self.point_sets),

            // Polycommit:
            // - s_poly commitment
            // - inner product argument (2 * k round commitments)
            // - a
            // - xi
            polycomm: ProofContribution::new((1 + 2 * self.k).try_into().unwrap(), 2),

            _marker: PhantomData,
        }
    }
}

/// (commitments, evaluations)
#[derive(Debug)]
struct ProofContribution {
    commitments: usize,
    evaluations: usize,
}

impl ProofContribution {
    fn new(commitments: usize, evaluations: usize) -> Self {
        ProofContribution {
            commitments,
            evaluations,
        }
    }

    fn len(&self, point: usize, scalar: usize) -> usize {
        self.commitments * point + self.evaluations * scalar
    }
}

impl Add for ProofContribution {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            commitments: self.commitments + rhs.commitments,
            evaluations: self.evaluations + rhs.evaluations,
        }
    }
}

impl Mul<usize> for ProofContribution {
    type Output = Self;

    fn mul(self, instances: usize) -> Self::Output {
        Self {
            commitments: self.commitments * instances,
            evaluations: self.evaluations * instances,
        }
    }
}

/// The marginal size of a Halo 2 proof, broken down into its contributing factors.
#[derive(Debug)]
pub struct MarginalProofSize<G: PrimeGroup> {
    instance: ProofContribution,
    advice: ProofContribution,
    lookups: ProofContribution,
    equality: ProofContribution,
    _marker: PhantomData<G>,
}

impl<G: PrimeGroup> From<MarginalProofSize<G>> for usize {
    fn from(proof: MarginalProofSize<G>) -> Self {
        let point = G::Repr::default().as_ref().len();
        let scalar = <G::Scalar as PrimeField>::Repr::default().as_ref().len();

        proof.instance.len(point, scalar)
            + proof.advice.len(point, scalar)
            + proof.lookups.len(point, scalar)
            + proof.equality.len(point, scalar)
    }
}

/// The size of a Halo 2 proof, broken down into its contributing factors.
#[derive(Debug)]
pub struct ProofSize<G: PrimeGroup> {
    instance: ProofContribution,
    advice: ProofContribution,
    fixed: ProofContribution,
    lookups: ProofContribution,
    equality: ProofContribution,
    vanishing: ProofContribution,
    multiopen: ProofContribution,
    polycomm: ProofContribution,
    _marker: PhantomData<G>,
}

impl<G: PrimeGroup> From<ProofSize<G>> for usize {
    fn from(proof: ProofSize<G>) -> Self {
        let point = G::Repr::default().as_ref().len();
        let scalar = <G::Scalar as PrimeField>::Repr::default().as_ref().len();

        proof.instance.len(point, scalar)
            + proof.advice.len(point, scalar)
            + proof.fixed.len(point, scalar)
            + proof.lookups.len(point, scalar)
            + proof.equality.len(point, scalar)
            + proof.vanishing.len(point, scalar)
            + proof.multiopen.len(point, scalar)
            + proof.polycomm.len(point, scalar)
    }
}

#[cfg(test)]
mod tests {
    use halo2curves::pasta::{Eq, Fp};

    use crate::circuit::SimpleFloorPlanner;

    use super::*;

    #[test]
    fn circuit_cost_without_permutation() {
        const K: u32 = 4;

        struct MyCircuit;
        impl Circuit<Fp> for MyCircuit {
            type Config = ();
            type FloorPlanner = SimpleFloorPlanner;
            #[cfg(feature = "circuit-params")]
            type Params = ();

            fn without_witnesses(&self) -> Self {
                Self
            }

            fn configure(_meta: &mut ConstraintSystem<Fp>) -> Self::Config {}

            fn synthesize(
                &self,
                _config: Self::Config,
                _layouter: impl crate::circuit::Layouter<Fp>,
            ) -> Result<(), Error> {
                Ok(())
            }
        }
        let cost = CircuitCost::<Eq, MyCircuit>::measure(K, &MyCircuit);

        let marginal_proof_size = cost.marginal_proof_size();
        assert_eq!(usize::from(marginal_proof_size), 0);

        let proof_size = cost.proof_size(1);
        assert_eq!(usize::from(proof_size), 608);
    }

    #[test]
    fn test_circuit_cost_from_complex_circuit() {
        use crate::{
            circuit::{AssignedCell, Layouter, Region},
            plonk::{Error as ErrorFront, Expression, FirstPhase, SecondPhase},
        };

        #[derive(Clone)]
        struct MyCircuitConfig {
            // A gate that uses selector, fixed, advice, has addition, multiplication and rotation
            // s_gate[0] * (a[0] + b[0] * c[0] * d[0] - a[1])
            s_gate: Selector,
            a: Column<Advice>,
            b: Column<Advice>,
            c: Column<Advice>,
            d: Column<Fixed>,

            // Copy constraints between columns (a, b) and (a, d)

            // A dynamic lookup: s_lookup * [1, a[0], b[0]] in s_ltable * [1, d[0], c[0]]
            s_lookup: Column<Fixed>,
            s_ltable: Column<Fixed>,

            // A shuffle: s_shufle * [1, a[0]] shuffle_of s_stable * [1, b[0]]
            s_shuffle: Column<Fixed>,
            s_stable: Column<Fixed>,

            // A FirstPhase challenge and SecondPhase column.  We define the following gates:
            // s_rlc * (a[0] + challenge * b[0] - e[0])
            // s_rlc * (c[0] + challenge * d[0] - e[0])
            s_rlc: Selector,
            e: Column<Advice>,
            challenge: Challenge,

            // Instance with a gate: s_instance * (a[0] - instance[0])
            s_instance: Selector,
            instance: Column<Instance>,
        }

        impl MyCircuitConfig {
            #[allow(clippy::type_complexity)]
            fn assign_gate<F: Field + From<u64>>(
                &self,
                region: &mut Region<'_, F>,
                offset: &mut usize,
                a_assigned: Option<AssignedCell<F, F>>,
                abcd: [u64; 4],
            ) -> Result<(AssignedCell<F, F>, [AssignedCell<F, F>; 4]), ErrorFront> {
                let [a, b, c, d] = abcd;
                self.s_gate.enable(region, *offset)?;
                let a_assigned = if let Some(a_assigned) = a_assigned {
                    a_assigned
                } else {
                    region.assign_advice(|| "", self.a, *offset, || Value::known(F::from(a)))?
                };
                let a = a_assigned.value();
                let [b, c, d] = [b, c, d].map(|v| Value::known(F::from(v)));
                let b_assigned = region.assign_advice(|| "", self.b, *offset, || b)?;
                let c_assigned = region.assign_advice(|| "", self.c, *offset, || c)?;
                let d_assigned = region.assign_fixed(|| "", self.d, *offset, || d)?;
                *offset += 1;
                // let res = a + b * c * d;
                let res = a
                    .zip(b.zip(c.zip(d)))
                    .map(|(a, (b, (c, d)))| *a + b * c * d);
                let res_assigned = region.assign_advice(|| "", self.a, *offset, || res)?;
                Ok((
                    res_assigned,
                    [a_assigned, b_assigned, c_assigned, d_assigned],
                ))
            }
        }

        #[allow(dead_code)]
        #[derive(Clone)]
        struct MyCircuit<F: Field, const WIDTH_FACTOR: usize> {
            k: u32,
            input: u64,
            _marker: std::marker::PhantomData<F>,
        }

        impl<F: Field + From<u64>, const WIDTH_FACTOR: usize> MyCircuit<F, WIDTH_FACTOR> {
            fn new(k: u32, input: u64) -> Self {
                Self {
                    k,
                    input,
                    _marker: std::marker::PhantomData {},
                }
            }

            fn configure_single(meta: &mut ConstraintSystem<F>, id: usize) -> MyCircuitConfig {
                let s_gate = meta.selector();
                let a = meta.advice_column();
                let b = meta.advice_column();
                let c = meta.advice_column();
                let d = meta.fixed_column();

                meta.enable_equality(a);
                meta.enable_equality(b);
                meta.enable_equality(d);

                let s_lookup = meta.fixed_column();
                let s_ltable = meta.fixed_column();

                let s_shuffle = meta.fixed_column();
                let s_stable = meta.fixed_column();

                let s_rlc = meta.selector();
                let e = meta.advice_column_in(SecondPhase);
                let challenge = meta.challenge_usable_after(FirstPhase);

                let s_instance = meta.selector();
                let instance = meta.instance_column();
                meta.enable_equality(instance);

                let one = Expression::Constant(F::ONE);

                meta.create_gate(format!("gate_a.{id}"), |meta| {
                    let s_gate = meta.query_selector(s_gate);
                    let b = meta.query_advice(b, Rotation::cur());
                    let a1 = meta.query_advice(a, Rotation::next());
                    let a0 = meta.query_advice(a, Rotation::cur());
                    let c = meta.query_advice(c, Rotation::cur());
                    let d = meta.query_fixed(d, Rotation::cur());

                    vec![s_gate * (a0 + b * c * d - a1)]
                });

                meta.lookup_any(format!("lookup.{id}"), |meta| {
                    let s_lookup = meta.query_fixed(s_lookup, Rotation::cur());
                    let s_ltable = meta.query_fixed(s_ltable, Rotation::cur());
                    let a = meta.query_advice(a, Rotation::cur());
                    let b = meta.query_advice(b, Rotation::cur());
                    let c = meta.query_advice(c, Rotation::cur());
                    let d = meta.query_fixed(d, Rotation::cur());
                    let lhs = [one.clone(), a, b].map(|c| c * s_lookup.clone());
                    let rhs = [one.clone(), d, c].map(|c| c * s_ltable.clone());
                    lhs.into_iter().zip(rhs).collect()
                });

                meta.shuffle(format!("shuffle.{id}"), |meta| {
                    let s_shuffle = meta.query_fixed(s_shuffle, Rotation::cur());
                    let s_stable = meta.query_fixed(s_stable, Rotation::cur());
                    let a = meta.query_advice(a, Rotation::cur());
                    let b = meta.query_advice(b, Rotation::cur());
                    let lhs = [one.clone(), a].map(|c| c * s_shuffle.clone());
                    let rhs = [one.clone(), b].map(|c| c * s_stable.clone());
                    lhs.into_iter().zip(rhs).collect()
                });

                meta.create_gate(format!("gate_rlc.{id}"), |meta| {
                    let s_rlc = meta.query_selector(s_rlc);
                    let a = meta.query_advice(a, Rotation::cur());
                    let b = meta.query_advice(b, Rotation::cur());
                    let c = meta.query_advice(c, Rotation::cur());
                    let d = meta.query_fixed(d, Rotation::cur());
                    let e = meta.query_advice(e, Rotation::cur());
                    let challenge = meta.query_challenge(challenge);

                    vec![
                        s_rlc.clone() * (a + challenge.clone() * b - e.clone()),
                        s_rlc * (c + challenge * d - e),
                    ]
                });

                MyCircuitConfig {
                    s_gate,
                    a,
                    b,
                    c,
                    d,
                    s_lookup,
                    s_ltable,
                    s_rlc,
                    e,
                    challenge,
                    s_shuffle,
                    s_stable,
                    s_instance,
                    instance,
                }
            }

            fn synthesize_unit(
                &self,
                config: &MyCircuitConfig,
                layouter: &mut impl Layouter<F>,
                id: usize,
                unit_id: usize,
            ) -> Result<(usize, Vec<AssignedCell<F, F>>), ErrorFront> {
                let challenge = layouter.get_challenge(config.challenge);
                let (rows, instance_copy) = layouter.assign_region(
                    || format!("unit.{id}-{unit_id}"),
                    |mut region| {
                        // Column annotations
                        region.name_column(|| format!("a.{id}"), config.a);
                        region.name_column(|| format!("b.{id}"), config.b);
                        region.name_column(|| format!("c.{id}"), config.c);
                        region.name_column(|| format!("d.{id}"), config.d);
                        region.name_column(|| format!("e.{id}"), config.e);
                        region.name_column(|| format!("instance.{id}"), config.instance);
                        region.name_column(|| format!("s_lookup.{id}"), config.s_lookup);
                        region.name_column(|| format!("s_ltable.{id}"), config.s_ltable);
                        region.name_column(|| format!("s_shuffle.{id}"), config.s_shuffle);
                        region.name_column(|| format!("s_stable.{id}"), config.s_stable);

                        let mut offset = 0;
                        let mut instance_copy = Vec::new();
                        // First "a" value comes from instance
                        config.s_instance.enable(&mut region, offset).unwrap();
                        let res = region
                            .assign_advice_from_instance(
                                || "",
                                config.instance,
                                0,
                                config.a,
                                offset,
                            )
                            .unwrap();
                        // Enable the gate on a few consecutive rows with rotations
                        let (res, _) = config
                            .assign_gate(&mut region, &mut offset, Some(res), [0, 3, 4, 1])
                            .unwrap();
                        instance_copy.push(res.clone());
                        let (res, _) = config
                            .assign_gate(&mut region, &mut offset, Some(res), [0, 6, 7, 1])
                            .unwrap();
                        instance_copy.push(res.clone());
                        let (res, _) = config
                            .assign_gate(&mut region, &mut offset, Some(res), [0, 8, 9, 1])
                            .unwrap();
                        instance_copy.push(res.clone());
                        let (res, _) = config
                            .assign_gate(
                                &mut region,
                                &mut offset,
                                Some(res),
                                [0, 0xffffffff, 0xdeadbeef, 1],
                            )
                            .unwrap();
                        let _ = config
                            .assign_gate(
                                &mut region,
                                &mut offset,
                                Some(res),
                                [0, 0xabad1d3a, 0x12345678, 0x42424242],
                            )
                            .unwrap();
                        offset += 1;

                        // Enable the gate on non-consecutive rows with advice-advice copy constraints enabled
                        let (_, abcd1) = config
                            .assign_gate(&mut region, &mut offset, None, [5, 2, 1, 1])
                            .unwrap();
                        offset += 1;
                        let (_, abcd2) = config
                            .assign_gate(&mut region, &mut offset, None, [2, 3, 1, 1])
                            .unwrap();
                        offset += 1;
                        let (_, abcd3) = config
                            .assign_gate(&mut region, &mut offset, None, [4, 2, 1, 1])
                            .unwrap();
                        offset += 1;
                        region
                            .constrain_equal(abcd1[1].cell(), abcd2[0].cell())
                            .unwrap();
                        region
                            .constrain_equal(abcd2[0].cell(), abcd3[1].cell())
                            .unwrap();
                        instance_copy.push(abcd1[1].clone());
                        instance_copy.push(abcd2[0].clone());

                        // Enable the gate on non-consecutive rows with advice-fixed copy constraints enabled
                        let (_, abcd1) = config
                            .assign_gate(&mut region, &mut offset, None, [5, 9, 1, 9])
                            .unwrap();
                        offset += 1;
                        let (_, abcd2) = config
                            .assign_gate(&mut region, &mut offset, None, [2, 9, 1, 1])
                            .unwrap();
                        offset += 1;
                        let (_, abcd3) = config
                            .assign_gate(&mut region, &mut offset, None, [9, 2, 1, 1])
                            .unwrap();
                        offset += 1;
                        region
                            .constrain_equal(abcd1[1].cell(), abcd1[3].cell())
                            .unwrap();
                        region
                            .constrain_equal(abcd2[1].cell(), abcd1[3].cell())
                            .unwrap();
                        region
                            .constrain_equal(abcd3[0].cell(), abcd1[3].cell())
                            .unwrap();

                        // Enable a dynamic lookup (powers of two)
                        let table: Vec<_> =
                            (0u64..=10).map(|exp| (exp, 2u64.pow(exp as u32))).collect();
                        let lookups = [(2, 4), (2, 4), (10, 1024), (0, 1), (2, 4)];
                        for (table_row, lookup_row) in table
                            .iter()
                            .zip(lookups.iter().chain(std::iter::repeat(&(0, 1))))
                        {
                            region
                                .assign_fixed(
                                    || "",
                                    config.s_lookup,
                                    offset,
                                    || Value::known(F::ONE),
                                )
                                .unwrap();
                            region
                                .assign_fixed(
                                    || "",
                                    config.s_ltable,
                                    offset,
                                    || Value::known(F::ONE),
                                )
                                .unwrap();
                            let lookup_row0 = Value::known(F::from(lookup_row.0));
                            let lookup_row1 = Value::known(F::from(lookup_row.1));
                            region
                                .assign_advice(|| "", config.a, offset, || lookup_row0)
                                .unwrap();
                            region
                                .assign_advice(|| "", config.b, offset, || lookup_row1)
                                .unwrap();
                            let table_row0 = Value::known(F::from(table_row.0));
                            let table_row1 = Value::known(F::from(table_row.1));
                            region
                                .assign_fixed(|| "", config.d, offset, || table_row0)
                                .unwrap();
                            region
                                .assign_advice(|| "", config.c, offset, || table_row1)
                                .unwrap();
                            offset += 1;
                        }

                        // Enable RLC gate 3 times
                        for abcd in [[3, 5, 3, 5], [8, 9, 8, 9], [111, 222, 111, 222]] {
                            config.s_rlc.enable(&mut region, offset)?;
                            let (_, _) = config
                                .assign_gate(&mut region, &mut offset, None, abcd)
                                .unwrap();
                            let rlc = challenge.map(|ch| {
                                let [a, b, ..] = abcd;
                                F::from(a) + ch * F::from(b)
                            });
                            region
                                .assign_advice(|| "", config.e, offset - 1, || rlc)
                                .unwrap();
                            offset += 1;
                        }

                        // Enable a dynamic shuffle (sequence from 0 to 15)
                        let table: Vec<_> = (0u64..16).collect();
                        let shuffle = [0u64, 2, 4, 6, 8, 10, 12, 14, 1, 3, 5, 7, 9, 11, 13, 15];
                        assert_eq!(table.len(), shuffle.len());

                        for (table_row, shuffle_row) in table.iter().zip(shuffle.iter()) {
                            region
                                .assign_fixed(
                                    || "",
                                    config.s_shuffle,
                                    offset,
                                    || Value::known(F::ONE),
                                )
                                .unwrap();
                            region
                                .assign_fixed(
                                    || "",
                                    config.s_stable,
                                    offset,
                                    || Value::known(F::ONE),
                                )
                                .unwrap();
                            let shuffle_row0 = Value::known(F::from(*shuffle_row));
                            region
                                .assign_advice(|| "", config.a, offset, || shuffle_row0)
                                .unwrap();
                            let table_row0 = Value::known(F::from(*table_row));
                            region
                                .assign_advice(|| "", config.b, offset, || table_row0)
                                .unwrap();
                            offset += 1;
                        }

                        Ok((offset, instance_copy))
                    },
                )?;

                Ok((rows, instance_copy))
            }
        }

        impl<F: Field + From<u64>, const WIDTH_FACTOR: usize> Circuit<F> for MyCircuit<F, WIDTH_FACTOR> {
            type Config = Vec<MyCircuitConfig>;
            type FloorPlanner = SimpleFloorPlanner;
            #[cfg(feature = "circuit-params")]
            type Params = ();

            fn without_witnesses(&self) -> Self {
                self.clone()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Vec<MyCircuitConfig> {
                assert!(WIDTH_FACTOR > 0);
                (0..WIDTH_FACTOR)
                    .map(|id| Self::configure_single(meta, id))
                    .collect()
            }

            fn synthesize(
                &self,
                config: Vec<MyCircuitConfig>,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), ErrorFront> {
                // - 2 queries from first gate
                // - 3 for permutation argument
                // - 1 for multipoen
                // - 1 for the last row of grand product poly to check that the product result is 1
                // - 1 for off-by-one errors
                let unusable_rows = 2 + 3 + 1 + 1 + 1;
                let max_rows = 2usize.pow(self.k) - unusable_rows;
                for (id, config) in config.iter().enumerate() {
                    let mut total_rows = 0;
                    let mut unit_id = 0;
                    loop {
                        let (rows, instance_copy) = self
                            .synthesize_unit(config, &mut layouter, id, unit_id)
                            .unwrap();
                        if total_rows == 0 {
                            for (i, instance) in instance_copy.iter().enumerate() {
                                layouter.constrain_instance(
                                    instance.cell(),
                                    config.instance,
                                    1 + i,
                                )?;
                            }
                        }
                        total_rows += rows;
                        if total_rows + rows > max_rows {
                            break;
                        }
                        unit_id += 1;
                    }
                    assert!(total_rows <= max_rows);
                }
                Ok(())
            }
        }

        const K: u32 = 6;
        let my_circuit = MyCircuit::<Fp, 2>::new(K, 42);
        let cost = CircuitCost::<Eq, MyCircuit<Fp, 2>>::measure(K, &my_circuit);

        let marginal_proof_size = cost.marginal_proof_size();
        assert_eq!(usize::from(marginal_proof_size), 1376);

        let proof_size = cost.proof_size(1);
        assert_eq!(usize::from(proof_size), 3008);
    }
}
