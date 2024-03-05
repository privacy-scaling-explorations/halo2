use crate::multicore;
use crate::plonk::lookup::prover::Committed;
use crate::plonk::permutation::Argument;
use crate::plonk::{lookup, permutation, ProvingKey};
use crate::poly::Basis;
use crate::{
    arithmetic::{eval_polynomial, parallelize, CurveAffine},
    poly::{
        commitment::Params, Coeff, EvaluationDomain, ExtendedLagrangeCoeff, LagrangeCoeff,
        Polynomial, ProverQuery,
    },
    transcript::{EncodedChallenge, TranscriptWrite},
};
use group::prime::PrimeCurve;
use group::{
    ff::{BatchInvert, Field, PrimeField, WithSmallOrderMulGroup},
    Curve,
};
use halo2_common::plonk::{ConstraintSystem, Expression};
use halo2_middleware::circuit::Any;
use halo2_middleware::poly::Rotation;
use itertools::Itertools;
use std::any::TypeId;
use std::convert::TryInto;
use std::num::ParseIntError;
use std::slice;
use std::time::Instant;
use std::{
    collections::BTreeMap,
    iter,
    ops::{Index, Mul, MulAssign},
};

/// Return the index in the polynomial of size `isize` after rotation `rot`.
fn get_rotation_idx(idx: usize, rot: i32, rot_scale: i32, isize: i32) -> usize {
    (((idx as i32) + (rot * rot_scale)).rem_euclid(isize)) as usize
}

/// Value used in a calculation
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd)]
pub enum ValueSource {
    /// This is a constant value
    Constant(usize),
    /// This is an intermediate value
    Intermediate(usize),
    /// This is a fixed column
    Fixed(usize, usize),
    /// This is an advice (witness) column
    Advice(usize, usize),
    /// This is an instance (external) column
    Instance(usize, usize),
    /// This is a challenge
    Challenge(usize),
    /// beta
    Beta(),
    /// gamma
    Gamma(),
    /// theta
    Theta(),
    /// y
    Y(usize),
}

impl Default for ValueSource {
    fn default() -> Self {
        ValueSource::Constant(0)
    }
}

impl ValueSource {
    /// Get the value for this source
    pub fn get<F: Field, B: Basis>(
        &self,
        rotations: &[usize],
        constants: &[F],
        intermediates: &[F],
        fixed_values: &[Option<Polynomial<F, B>>],
        advice_values: &[Option<Polynomial<F, B>>],
        instance_values: &[Option<Polynomial<F, B>>],
        challenges: &[F],
        y_powers: &[F],
        beta: &F,
        gamma: &F,
        theta: &F,
    ) -> F {
        match self {
            ValueSource::Constant(idx) => constants[*idx],
            ValueSource::Intermediate(idx) => intermediates[*idx],
            ValueSource::Fixed(column_index, rotation) => {
                assert!(fixed_values[*column_index].is_some());
                fixed_values[*column_index].as_ref().unwrap()[rotations[*rotation]]
            }
            ValueSource::Advice(column_index, rotation) => {
                assert!(advice_values[*column_index].is_some());
                advice_values[*column_index].as_ref().unwrap()[rotations[*rotation]]
            }
            ValueSource::Instance(column_index, rotation) => {
                assert!(instance_values[*column_index].is_some());
                instance_values[*column_index].as_ref().unwrap()[rotations[*rotation]]
            }
            ValueSource::Challenge(index) => challenges[*index],
            ValueSource::Beta() => *beta,
            ValueSource::Gamma() => *gamma,
            ValueSource::Theta() => *theta,
            ValueSource::Y(idx) => y_powers[*idx],
        }
    }
}

/// Calculation
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Calculation {
    /// This is an addition
    Add(ValueSource, ValueSource),
    /// This is a subtraction
    Sub(ValueSource, ValueSource),
    /// This is a product
    Mul(ValueSource, ValueSource),
    /// This is a square
    Square(ValueSource),
    /// This is a double
    Double(ValueSource),
    /// This is a negation
    Negate(ValueSource),
    /// This is Horner's rule: `val = a; val = val * c + b[]`
    Horner(ValueSource, Vec<ValueSource>, ValueSource),
    /// This is a simple assignment
    Store(ValueSource),
}

impl Calculation {
    /// Get the resulting value of this calculation
    pub fn evaluate<F: Field, B: Basis>(
        &self,
        rotations: &[usize],
        constants: &[F],
        intermediates: &[F],
        fixed_values: &[Option<Polynomial<F, B>>],
        advice_values: &[Option<Polynomial<F, B>>],
        instance_values: &[Option<Polynomial<F, B>>],
        challenges: &[F],
        y_powers: &[F],
        beta: &F,
        gamma: &F,
        theta: &F,
    ) -> F {
        let get_value = |value: &ValueSource| {
            value.get(
                rotations,
                constants,
                intermediates,
                fixed_values,
                advice_values,
                instance_values,
                challenges,
                y_powers,
                beta,
                gamma,
                theta,
            )
        };
        match self {
            Calculation::Add(a, b) => get_value(a) + get_value(b),
            Calculation::Sub(a, b) => get_value(a) - get_value(b),
            Calculation::Mul(a, b) => get_value(a) * get_value(b),
            Calculation::Square(v) => get_value(v).square(),
            Calculation::Double(v) => get_value(v).double(),
            Calculation::Negate(v) => -get_value(v),
            Calculation::Horner(start_value, parts, factor) => {
                let factor = get_value(factor);
                let mut value = get_value(start_value);
                for part in parts.iter() {
                    value = value * factor + get_value(part);
                }
                value
            }
            Calculation::Store(v) => get_value(v),
        }
    }
}

#[derive(Clone, Default, Debug)]
struct ConstraintCluster<F: Field> {
    /// Used fixed columns in each cluster
    used_fixed_columns: Vec<usize>,
    /// Used instance columns in each cluster
    used_instance_columns: Vec<usize>,
    /// Used advice columns in each cluster
    used_advice_columns: Vec<usize>,
    /// Custom gates evalution
    evaluator: GraphEvaluator<F>,
    /// The first index of constraints are being evaluated at in each cluster
    first_constraint_idx: usize,
    /// The last index of constraints are being evaluated at in each cluster
    last_constraint_idx: usize,
    /// The last value source
    last_value_source: Option<ValueSource>,
}

/// Evaluator
#[derive(Clone, Default, Debug)]
pub struct Evaluator<F: Field> {
    /// list of constraint clusters
    custom_gate_clusters: Vec<ConstraintCluster<F>>,
    /// Number of custom gate constraints
    num_custom_gate_constraints: usize,
    ///  Lookups evalution, degree, used instance and advice columns
    #[allow(clippy::type_complexity)]
    lookups: Vec<(
        GraphEvaluator<F>,
        usize,
        (Vec<usize>, Vec<usize>, Vec<usize>),
    )>,

    /// Powers of y
    num_y_powers: usize,
}

/// GraphEvaluator
#[derive(Clone, Debug)]
pub struct GraphEvaluator<F: Field> {
    /// Constants
    pub constants: Vec<F>,
    /// Rotations
    pub rotations: Vec<i32>,
    /// Calculations
    pub calculations: Vec<CalculationInfo>,
    /// Number of intermediates
    pub num_intermediates: usize,
}

/// EvaluationData
#[derive(Default, Debug)]
pub struct EvaluationData<F: Field> {
    /// Intermediates
    pub intermediates: Vec<F>,
    /// Rotations
    pub rotations: Vec<usize>,
}

/// CaluclationInfo
#[derive(Clone, Debug)]
pub struct CalculationInfo {
    /// Calculation
    pub calculation: Calculation,
    /// Target
    pub target: usize,
}

fn merge_unique(a: Vec<usize>, b: Vec<usize>) -> Vec<usize> {
    let mut result = a;
    result.extend(b);
    result.into_iter().unique().collect()
}

impl<F: WithSmallOrderMulGroup<3>> Evaluator<F> {
    /// Creates a new evaluation structure
    pub fn new(cs: &ConstraintSystem<F>) -> Self {
        let mut ev = Evaluator::default();
        let mut constraint_idx = 0;

        // Compute the max cluster index
        let quotient_poly_degree = (cs.degree() - 1) as u64;
        let mut max_cluster_idx = 0;
        while (1 << max_cluster_idx) < quotient_poly_degree {
            max_cluster_idx += 1;
        }

        ev.custom_gate_clusters
            .resize(max_cluster_idx + 1, ConstraintCluster::default());

        // Custom gates
        for gate in cs.gates.iter() {
            for poly in gate.polynomials() {
                constraint_idx += 1;
                let cluster_idx = Self::compute_cluster_idx(poly.degree(), max_cluster_idx);
                let custom_gate_cluster = &mut ev.custom_gate_clusters[cluster_idx];
                custom_gate_cluster.used_fixed_columns = merge_unique(
                    custom_gate_cluster.used_fixed_columns.clone(),
                    poly.extract_fixed(),
                );
                custom_gate_cluster.used_instance_columns = merge_unique(
                    custom_gate_cluster.used_instance_columns.clone(),
                    poly.extract_instances(),
                );
                custom_gate_cluster.used_advice_columns = merge_unique(
                    custom_gate_cluster.used_advice_columns.clone(),
                    poly.extract_advices(),
                );
                let curr = custom_gate_cluster.evaluator.add_expression(poly);
                if let Some(last) = custom_gate_cluster.last_value_source {
                    custom_gate_cluster.last_value_source = Some(
                        custom_gate_cluster
                            .evaluator
                            .add_calculation(Calculation::Horner(
                                last,
                                vec![curr],
                                ValueSource::Y(
                                    constraint_idx - custom_gate_cluster.last_constraint_idx,
                                ),
                            )),
                    );
                } else {
                    assert_eq!(custom_gate_cluster.last_constraint_idx, 0);
                    custom_gate_cluster.last_value_source = Some(curr);
                    custom_gate_cluster.first_constraint_idx = constraint_idx;
                }
                custom_gate_cluster.last_constraint_idx = constraint_idx;
            }
        }

        ev.num_custom_gate_constraints = constraint_idx;

        // Lookups
        for lookup in cs.lookups.iter() {
            constraint_idx += 5;
            let mut graph = GraphEvaluator::default();

            let mut evaluate_lc = |expressions: &Vec<Expression<_>>| {
                let mut max_degree = 0;
                let mut used_fixed_columns = vec![];
                let mut used_instance_columns = vec![];
                let mut used_advice_columns = vec![];
                let parts = expressions
                    .iter()
                    .map(|expr| {
                        max_degree = max_degree.max(expr.degree());
                        used_fixed_columns =
                            merge_unique(used_fixed_columns.clone(), expr.extract_fixed());
                        used_instance_columns =
                            merge_unique(used_instance_columns.clone(), expr.extract_instances());
                        used_advice_columns =
                            merge_unique(used_advice_columns.clone(), expr.extract_advices());
                        graph.add_expression(expr)
                    })
                    .collect();
                (
                    graph.add_calculation(Calculation::Horner(
                        ValueSource::Constant(0),
                        parts,
                        ValueSource::Theta(),
                    )),
                    max_degree,
                    used_fixed_columns,
                    used_instance_columns,
                    used_advice_columns,
                )
            };

            // Input coset
            let (
                compressed_input_coset,
                max_input_degree,
                input_used_fixed,
                input_used_instances,
                input_used_advices,
            ) = evaluate_lc(&lookup.input_expressions);
            // table coset
            let (
                compressed_table_coset,
                max_table_degree,
                table_used_fixed,
                table_used_instances,
                table_used_advices,
            ) = evaluate_lc(&lookup.table_expressions);
            // z(\omega X) (a'(X) + \beta) (s'(X) + \gamma)
            let right_gamma = graph.add_calculation(Calculation::Add(
                compressed_table_coset,
                ValueSource::Gamma(),
            ));
            let lc = graph.add_calculation(Calculation::Add(
                compressed_input_coset,
                ValueSource::Beta(),
            ));
            graph.add_calculation(Calculation::Mul(lc, right_gamma));
            ev.lookups.push((
                graph,
                max_input_degree + max_table_degree,
                (
                    merge_unique(input_used_fixed, table_used_fixed),
                    merge_unique(input_used_instances, table_used_instances),
                    merge_unique(input_used_advices, table_used_advices),
                ),
            ));
        }

        // Count the constraints in permutation
        let num_sets = (cs.permutation.get_columns().len() + (cs.degree() - 3)) / (cs.degree() - 2);
        constraint_idx += 1 + num_sets * 2;
        ev.num_y_powers = constraint_idx + 10;
        ev
    }

    /// Evaluate h poly
    pub(in crate::plonk) fn evaluate_h<C: CurveAffine<ScalarExt = F>>(
        &self,
        pk: &ProvingKey<C>,
        advice_polys: &[&[Polynomial<F, Coeff>]],
        instance_polys: &[&[Polynomial<F, Coeff>]],
        challenges: &[F],
        y: F,
        beta: F,
        gamma: F,
        theta: F,
        lookups: &[Vec<lookup::prover::Committed<C>>],
        permutations: &[permutation::prover::Committed<C>],
    ) -> Polynomial<F, ExtendedLagrangeCoeff> {
        let domain = &pk.vk.domain;
        let size = 1 << domain.k() as usize;
        let rot_scale = 1;
        let extended_omega = domain.get_extended_omega();
        let omega = domain.get_omega();
        let isize = size as i32;
        let one = F::ONE;
        let p = &pk.vk.cs.permutation;
        let num_parts = domain.extended_len() >> domain.k();
        let num_clusters = (domain.extended_k() - domain.k() + 1) as usize;

        assert!(self.custom_gate_clusters.len() <= num_clusters);

        // Initialize the the powers of y and constraint counter
        let mut y_powers = vec![F::ONE; self.num_y_powers * instance_polys.len()];
        for i in 1..self.num_y_powers {
            y_powers[i] = y_powers[i - 1] * y;
        }

        let need_to_compute = |part_idx, cluster_idx| part_idx % (num_parts >> cluster_idx) == 0;
        let compute_part_idx_in_cluster =
            |part_idx, cluster_idx| part_idx >> (num_clusters - cluster_idx - 1);

        let mut value_part_clusters = Vec::new();
        value_part_clusters.resize(num_clusters, Vec::new());
        for (cluster_idx, cluster) in value_part_clusters
            .iter_mut()
            .enumerate()
            .take(num_clusters)
        {
            cluster.resize(1 << cluster_idx, domain.empty_lagrange());
        }

        // Calculate the quotient polynomial for each part
        let mut current_extended_omega = one;
        for part_idx in 0..num_parts {
            let mut fixed: Vec<Option<Polynomial<F, LagrangeCoeff>>> =
                vec![None; pk.fixed_polys.len()];
            let l0 = domain.coeff_to_extended_part(pk.l0.clone(), current_extended_omega);
            let l_last = domain.coeff_to_extended_part(pk.l_last.clone(), current_extended_omega);
            let l_active_row =
                domain.coeff_to_extended_part(pk.l_active_row.clone(), current_extended_omega);

            let mut constraint_idx = 0;
            let mut cluster_last_constraint_idx = vec![0; num_clusters];

            // Core expression evaluations
            let num_threads = multicore::current_num_threads();
            for (((advice_polys, instance_polys), lookups), permutation) in advice_polys
                .iter()
                .zip(instance_polys.iter())
                .zip(lookups.iter())
                .zip(permutations.iter())
            {
                // Calculate the advice and instance cosets
                let mut advice: Vec<Option<Polynomial<C::Scalar, LagrangeCoeff>>> =
                    vec![None; advice_polys.len()];
                let mut instance: Vec<Option<Polynomial<C::Scalar, LagrangeCoeff>>> =
                    vec![None; instance_polys.len()];

                // Custom gates
                for (cluster_idx, custom_gates) in self.custom_gate_clusters.iter().enumerate() {
                    if !need_to_compute(part_idx, cluster_idx)
                        || custom_gates.last_value_source.is_none()
                    {
                        continue;
                    }
                    let values = &mut value_part_clusters[cluster_idx]
                        [compute_part_idx_in_cluster(part_idx, cluster_idx)];
                    for fixed_idx in custom_gates.used_fixed_columns.iter() {
                        if fixed[*fixed_idx].is_none() {
                            fixed[*fixed_idx] = Some(domain.coeff_to_extended_part(
                                pk.fixed_polys[*fixed_idx].clone(),
                                current_extended_omega,
                            ));
                        }
                    }
                    for instance_idx in custom_gates.used_instance_columns.iter() {
                        if instance[*instance_idx].is_none() {
                            instance[*instance_idx] = Some(domain.coeff_to_extended_part(
                                instance_polys[*instance_idx].clone(),
                                current_extended_omega,
                            ));
                        }
                    }
                    for advice_idx in custom_gates.used_advice_columns.iter() {
                        if advice[*advice_idx].is_none() {
                            advice[*advice_idx] = Some(domain.coeff_to_extended_part(
                                advice_polys[*advice_idx].clone(),
                                current_extended_omega,
                            ));
                        }
                    }
                    let fixed_slice = &fixed[..];
                    let advice_slice = &advice[..];
                    let instance_slice = &instance[..];
                    let y_power_slice = &y_powers[..];
                    let y_power = y_powers[constraint_idx + custom_gates.first_constraint_idx
                        - cluster_last_constraint_idx[cluster_idx]];
                    multicore::scope(|scope| {
                        let chunk_size = (size + num_threads - 1) / num_threads;
                        for (thread_idx, values) in values.chunks_mut(chunk_size).enumerate() {
                            let start = thread_idx * chunk_size;
                            scope.spawn(move |_| {
                                let mut eval_data = custom_gates.evaluator.instance();
                                for (i, value) in values.iter_mut().enumerate() {
                                    let idx = start + i;
                                    *value = *value * y_power
                                        + custom_gates.evaluator.evaluate(
                                            &mut eval_data,
                                            fixed_slice,
                                            advice_slice,
                                            instance_slice,
                                            challenges,
                                            y_power_slice,
                                            &beta,
                                            &gamma,
                                            &theta,
                                            idx,
                                            rot_scale,
                                            isize,
                                        );
                                }
                            });
                        }
                    });

                    // Update the constraint index
                    cluster_last_constraint_idx[cluster_idx] =
                        constraint_idx + custom_gates.last_constraint_idx;
                }
                constraint_idx += self.num_custom_gate_constraints;

                // Permutations
                let sets = &permutation.sets;
                if !sets.is_empty() {
                    let blinding_factors = pk.vk.cs.blinding_factors();
                    let last_rotation = Rotation(-((blinding_factors + 1) as i32));
                    let chunk_len = pk.vk.cs.degree() - 2;
                    let delta_start = beta * &C::Scalar::ZETA;

                    let permutation_product_cosets: Vec<Polynomial<F, LagrangeCoeff>> = sets
                        .iter()
                        .map(|set| {
                            domain.coeff_to_extended_part(
                                set.permutation_product_poly.clone(),
                                current_extended_omega,
                            )
                        })
                        .collect();

                    let first_set_permutation_product_coset =
                        permutation_product_cosets.first().unwrap();
                    let last_set_permutation_product_coset =
                        permutation_product_cosets.last().unwrap();

                    // Permutation constraints
                    constraint_idx += 1;
                    if need_to_compute(part_idx, 1) {
                        let y_power = y_powers[constraint_idx - cluster_last_constraint_idx[1]];
                        parallelize(
                            &mut value_part_clusters[1][compute_part_idx_in_cluster(part_idx, 1)],
                            |values, start| {
                                for (i, value) in values.iter_mut().enumerate() {
                                    let idx = start + i;
                                    // Enforce only for the first set.
                                    // l_0(X) * (1 - z_0(X)) = 0, degree = 2
                                    *value = *value * y_power
                                        + ((one - first_set_permutation_product_coset[idx])
                                            * l0[idx]);
                                }
                            },
                        );
                        cluster_last_constraint_idx[1] = constraint_idx;
                    }

                    constraint_idx += 1;
                    if need_to_compute(part_idx, 2) {
                        let y_power = y_powers[constraint_idx - cluster_last_constraint_idx[2]];
                        parallelize(
                            &mut value_part_clusters[2][compute_part_idx_in_cluster(part_idx, 2)],
                            |values, start| {
                                for (i, value) in values.iter_mut().enumerate() {
                                    let idx = start + i;
                                    // Enforce only for the last set.
                                    // l_last(X) * (z_l(X)^2 - z_l(X)) = 0, degree = 3
                                    *value = *value * y_power
                                        + ((last_set_permutation_product_coset[idx]
                                            * last_set_permutation_product_coset[idx]
                                            - last_set_permutation_product_coset[idx])
                                            * l_last[idx]);
                                }
                            },
                        );
                        cluster_last_constraint_idx[2] = constraint_idx;
                    }

                    constraint_idx += sets.len() - 1;
                    if need_to_compute(part_idx, 1) {
                        let y_skip = y_powers
                            [constraint_idx + 1 - sets.len() - cluster_last_constraint_idx[1]];
                        parallelize(
                            &mut value_part_clusters[1][compute_part_idx_in_cluster(part_idx, 1)],
                            |values, start| {
                                for (i, value) in values.iter_mut().enumerate() {
                                    let idx = start + i;
                                    // Except for the first set, enforce.
                                    // l_0(X) * (z_i(X) - z_{i-1}(\omega^(last) X)) = 0, degree = 2
                                    let r_last =
                                        get_rotation_idx(idx, last_rotation.0, rot_scale, isize);

                                    *value = *value * y_skip;

                                    for (set_idx, permutation_product_coset) in
                                        permutation_product_cosets.iter().enumerate()
                                    {
                                        if set_idx != 0 {
                                            *value = *value * y
                                                + ((permutation_product_coset[idx]
                                                    - permutation_product_cosets[set_idx - 1]
                                                        [r_last])
                                                    * l0[idx]);
                                        }
                                    }
                                }
                            },
                        );
                        cluster_last_constraint_idx[1] = constraint_idx;
                    }

                    constraint_idx += sets.len();
                    let running_prod_cluster =
                        Self::compute_cluster_idx(2 + chunk_len, num_clusters - 1);
                    if need_to_compute(part_idx, running_prod_cluster) {
                        for column in p.columns.iter() {
                            match column.column_type() {
                                Any::Advice(_) => {
                                    let advice = &mut advice[column.index()];
                                    if (*advice).is_none() {
                                        *advice = Some(domain.coeff_to_extended_part(
                                            advice_polys[column.index()].clone(),
                                            current_extended_omega,
                                        ));
                                    }
                                }
                                Any::Instance => {
                                    let instance = &mut instance[column.index()];
                                    if instance.is_none() {
                                        *instance = Some(domain.coeff_to_extended_part(
                                            instance_polys[column.index()].clone(),
                                            current_extended_omega,
                                        ));
                                    }
                                }
                                Any::Fixed => {
                                    let fixed = &mut fixed[column.index()];
                                    if fixed.is_none() {
                                        *fixed = Some(domain.coeff_to_extended_part(
                                            pk.fixed_polys[column.index()].clone(),
                                            current_extended_omega,
                                        ));
                                    }
                                }
                            }
                        }

                        let permutation_cosets: Vec<Polynomial<F, LagrangeCoeff>> = pk
                            .permutation
                            .polys
                            .iter()
                            .map(|p| {
                                domain.coeff_to_extended_part(p.clone(), current_extended_omega)
                            })
                            .collect();

                        let y_skip = y_powers[constraint_idx
                            - sets.len()
                            - cluster_last_constraint_idx[running_prod_cluster]];

                        parallelize(
                            &mut value_part_clusters[running_prod_cluster]
                                [compute_part_idx_in_cluster(part_idx, running_prod_cluster)],
                            |values, start| {
                                let mut beta_term = current_extended_omega
                                    * omega.pow_vartime(&[start as u64, 0, 0, 0]);
                                for (i, value) in values.iter_mut().enumerate() {
                                    let idx = start + i;
                                    let r_next = get_rotation_idx(idx, 1, rot_scale, isize);

                                    *value = *value * y_skip;

                                    // And for all the sets we enforce:
                                    // (1 - (l_last(X) + l_blind(X))) * (
                                    //   z_i(\omega X) \prod_j (p(X) + \beta s_j(X) + \gamma)
                                    // - z_i(X) \prod_j (p(X) + \delta^j \beta X + \gamma)
                                    // ), degree = 2 + chunk_len
                                    let mut current_delta = delta_start * beta_term;
                                    for (
                                        (columns, permutation_product_coset),
                                        permutation_coset_chunk,
                                    ) in p
                                        .columns
                                        .chunks(chunk_len)
                                        .zip(permutation_product_cosets.iter())
                                        .zip(permutation_cosets.chunks(chunk_len))
                                    {
                                        let mut left = permutation_product_coset[r_next];
                                        for (values, permutation) in columns
                                            .iter()
                                            .map(|&column| match column.column_type() {
                                                Any::Advice(_) => {
                                                    advice[column.index()].as_ref().unwrap()
                                                }
                                                Any::Fixed => {
                                                    fixed[column.index()].as_ref().unwrap()
                                                }
                                                Any::Instance => {
                                                    instance[column.index()].as_ref().unwrap()
                                                }
                                            })
                                            .zip(permutation_coset_chunk.iter())
                                        {
                                            left *= values[idx] + beta * permutation[idx] + gamma;
                                        }

                                        let mut right = permutation_product_coset[idx];
                                        for values in columns.iter().map(|&column| {
                                            match column.column_type() {
                                                Any::Advice(_) => {
                                                    advice[column.index()].as_ref().unwrap()
                                                }
                                                Any::Fixed => {
                                                    fixed[column.index()].as_ref().unwrap()
                                                }
                                                Any::Instance => {
                                                    instance[column.index()].as_ref().unwrap()
                                                }
                                            }
                                        }) {
                                            right *= values[idx] + current_delta + gamma;
                                            current_delta *= &C::Scalar::DELTA;
                                        }

                                        *value = *value * y + ((left - right) * l_active_row[idx]);
                                    }
                                    beta_term *= &omega;
                                }
                            },
                        );
                        cluster_last_constraint_idx[running_prod_cluster] = constraint_idx;
                    }
                }

                // Lookups
                for (n, lookup) in lookups.iter().enumerate() {
                    let (lookup_evaluator, max_degree, used_columns) = &self.lookups[n];
                    let running_prod_cluster =
                        Self::compute_cluster_idx(max_degree + 2, num_clusters - 1);
                    if !need_to_compute(part_idx, 1)
                        && !need_to_compute(part_idx, 2)
                        && !need_to_compute(part_idx, running_prod_cluster)
                    {
                        constraint_idx += 5;
                        continue;
                    }

                    // Polynomials required for this lookup.
                    // Calculated here so these only have to be kept in memory for the short time
                    // they are actually needed.
                    let product_coset = pk.vk.domain.coeff_to_extended_part(
                        lookup.product_poly.clone(),
                        current_extended_omega,
                    );
                    let permuted_input_coset = pk.vk.domain.coeff_to_extended_part(
                        lookup.permuted_input_poly.clone(),
                        current_extended_omega,
                    );
                    let permuted_table_coset = pk.vk.domain.coeff_to_extended_part(
                        lookup.permuted_table_poly.clone(),
                        current_extended_omega,
                    );

                    // Lookup constraints
                    constraint_idx += 1;
                    if need_to_compute(part_idx, 1) {
                        let y_power = y_powers[constraint_idx - cluster_last_constraint_idx[1]];

                        parallelize(
                            &mut value_part_clusters[1][compute_part_idx_in_cluster(part_idx, 1)],
                            |values, start| {
                                for (i, value) in values.iter_mut().enumerate() {
                                    let idx = start + i;
                                    // l_0(X) * (1 - z(X)) = 0, degree = 2
                                    *value =
                                        *value * y_power + ((one - product_coset[idx]) * l0[idx]);
                                }
                            },
                        );
                        cluster_last_constraint_idx[1] = constraint_idx;
                    }

                    constraint_idx += 1;
                    if need_to_compute(part_idx, 2) {
                        let y_power = y_powers[constraint_idx - cluster_last_constraint_idx[2]];
                        parallelize(
                            &mut value_part_clusters[2][compute_part_idx_in_cluster(part_idx, 2)],
                            |values, start| {
                                for (i, value) in values.iter_mut().enumerate() {
                                    let idx = start + i;
                                    // l_last(X) * (z(X)^2 - z(X)) = 0, degree = 3
                                    *value = *value * y_power
                                        + ((product_coset[idx] * product_coset[idx]
                                            - product_coset[idx])
                                            * l_last[idx]);
                                }
                            },
                        );
                        cluster_last_constraint_idx[2] = constraint_idx;
                    }
                    constraint_idx += 1;
                    if need_to_compute(part_idx, running_prod_cluster) {
                        for fixed_column in used_columns.0.iter() {
                            let fixed = &mut fixed[*fixed_column];
                            if fixed.is_none() {
                                *fixed = Some(domain.coeff_to_extended_part(
                                    pk.fixed_polys[*fixed_column].clone(),
                                    current_extended_omega,
                                ));
                            }
                        }
                        for instance_column in used_columns.1.iter() {
                            let instance = &mut instance[*instance_column];
                            if instance.is_none() {
                                *instance = Some(domain.coeff_to_extended_part(
                                    instance_polys[*instance_column].clone(),
                                    current_extended_omega,
                                ));
                            }
                        }

                        for advice_column in used_columns.2.iter() {
                            let advice = &mut advice[*advice_column];
                            if (*advice).is_none() {
                                *advice = Some(domain.coeff_to_extended_part(
                                    advice_polys[*advice_column].clone(),
                                    current_extended_omega,
                                ));
                            }
                        }

                        let y_power = y_powers
                            [constraint_idx - cluster_last_constraint_idx[running_prod_cluster]];
                        let fixed_slice = &fixed[..];
                        let advice_slice = &advice[..];
                        let instance_slice = &instance[..];
                        let y_power_slice = &y_powers[..];
                        parallelize(
                            &mut value_part_clusters[running_prod_cluster]
                                [compute_part_idx_in_cluster(part_idx, running_prod_cluster)],
                            |values, start| {
                                let mut eval_data = lookup_evaluator.instance();
                                for (i, value) in values.iter_mut().enumerate() {
                                    let idx = start + i;
                                    let table_value = lookup_evaluator.evaluate(
                                        &mut eval_data,
                                        fixed_slice,
                                        advice_slice,
                                        instance_slice,
                                        challenges,
                                        y_power_slice,
                                        &beta,
                                        &gamma,
                                        &theta,
                                        idx,
                                        rot_scale,
                                        isize,
                                    );

                                    let r_next = get_rotation_idx(idx, 1, rot_scale, isize);

                                    // (1 - (l_last(X) + l_blind(X))) * (
                                    //   z(\omega X) (a'(X) + \beta) (s'(X) + \gamma)
                                    //   - z(X) (\theta^{m-1} a_0(X) + ... + a_{m-1}(X) + \beta)
                                    //          (\theta^{m-1} s_0(X) + ... + s_{m-1}(X) + \gamma)
                                    // ) = 0, degree = 2 + max(deg(a)) + max(deg(s))
                                    *value = *value * y_power
                                        + ((product_coset[r_next]
                                            * (permuted_input_coset[idx] + beta)
                                            * (permuted_table_coset[idx] + gamma)
                                            - product_coset[idx] * table_value)
                                            * l_active_row[idx]);
                                }
                            },
                        );
                        cluster_last_constraint_idx[running_prod_cluster] = constraint_idx;
                    }

                    constraint_idx += 1;
                    if need_to_compute(part_idx, 1) {
                        let y_power = y_powers[constraint_idx - cluster_last_constraint_idx[1]];
                        parallelize(
                            &mut value_part_clusters[1][compute_part_idx_in_cluster(part_idx, 1)],
                            |values, start| {
                                for (i, value) in values.iter_mut().enumerate() {
                                    let idx = start + i;
                                    let a_minus_s =
                                        permuted_input_coset[idx] - permuted_table_coset[idx];
                                    // Check that the first values in the permuted input expression and permuted
                                    // fixed expression are the same.
                                    // l_0(X) * (a'(X) - s'(X)) = 0, degree = 2
                                    *value = *value * y_power + (a_minus_s * l0[idx]);
                                }
                            },
                        );
                        cluster_last_constraint_idx[1] = constraint_idx;
                    }

                    constraint_idx += 1;
                    if need_to_compute(part_idx, 2) {
                        let y_power = y_powers[constraint_idx - cluster_last_constraint_idx[2]];
                        parallelize(
                            &mut value_part_clusters[2][compute_part_idx_in_cluster(part_idx, 2)],
                            |values, start| {
                                for (i, value) in values.iter_mut().enumerate() {
                                    let idx = start + i;
                                    let r_prev = get_rotation_idx(idx, -1, rot_scale, isize);

                                    // Check that each value in the permuted lookup input expression is either
                                    // equal to the value above it, or the value at the same index in the
                                    // permuted table expression.
                                    // (1 - (l_last + l_blind)) * (a′(X) − s′(X))⋅(a′(X) − a′(\omega^{-1} X)) = 0, degree = 3
                                    let a_minus_s =
                                        permuted_input_coset[idx] - permuted_table_coset[idx];
                                    *value = *value * y_power
                                        + (a_minus_s
                                            * (permuted_input_coset[idx]
                                                - permuted_input_coset[r_prev])
                                            * l_active_row[idx]);
                                }
                            },
                        );
                        cluster_last_constraint_idx[2] = constraint_idx;
                    }
                }
            }
            // Align the constraints by different powers of y.
            for (i, cluster) in value_part_clusters.iter_mut().enumerate() {
                if need_to_compute(part_idx, i) && cluster_last_constraint_idx[i] > 0 {
                    let y_power = y_powers[constraint_idx - cluster_last_constraint_idx[i]];
                    parallelize(
                        &mut cluster[compute_part_idx_in_cluster(part_idx, i)],
                        |values, _| {
                            for value in values.iter_mut() {
                                *value = *value * y_power;
                            }
                        },
                    );
                }
            }
            current_extended_omega *= extended_omega;
        }
        domain.lagrange_vecs_to_extended(value_part_clusters)
    }

    fn compute_cluster_idx(degree: usize, max_cluster_idx: usize) -> usize {
        let mut idx = (31 - (degree as u32).leading_zeros()) as usize;
        if 1 << idx < degree {
            idx = idx + 1;
        }
        std::cmp::min(max_cluster_idx, idx)
    }
}

impl<F: Field> Default for GraphEvaluator<F> {
    fn default() -> Self {
        Self {
            // Fixed positions to allow easy access
            constants: vec![F::ZERO, F::ONE, F::ONE + F::ONE],
            rotations: Vec::new(),
            calculations: Vec::new(),
            num_intermediates: 0,
        }
    }
}

impl<F: Field> GraphEvaluator<F> {
    /// Adds a rotation
    fn add_rotation(&mut self, rotation: &Rotation) -> usize {
        let position = self.rotations.iter().position(|&c| c == rotation.0);
        match position {
            Some(pos) => pos,
            None => {
                self.rotations.push(rotation.0);
                self.rotations.len() - 1
            }
        }
    }

    /// Adds a constant
    fn add_constant(&mut self, constant: &F) -> ValueSource {
        let position = self.constants.iter().position(|&c| c == *constant);
        ValueSource::Constant(match position {
            Some(pos) => pos,
            None => {
                self.constants.push(*constant);
                self.constants.len() - 1
            }
        })
    }

    /// Adds a calculation.
    /// Currently does the simplest thing possible: just stores the
    /// resulting value so the result can be reused  when that calculation
    /// is done multiple times.
    fn add_calculation(&mut self, calculation: Calculation) -> ValueSource {
        let existing_calculation = self
            .calculations
            .iter()
            .find(|c| c.calculation == calculation);
        match existing_calculation {
            Some(existing_calculation) => ValueSource::Intermediate(existing_calculation.target),
            None => {
                let target = self.num_intermediates;
                self.calculations.push(CalculationInfo {
                    calculation,
                    target,
                });
                self.num_intermediates += 1;
                ValueSource::Intermediate(target)
            }
        }
    }

    /// Generates an optimized evaluation for the expression
    fn add_expression(&mut self, expr: &Expression<F>) -> ValueSource {
        match expr {
            Expression::Constant(scalar) => self.add_constant(scalar),
            Expression::Selector(_selector) => unreachable!(),
            Expression::Fixed(query) => {
                let rot_idx = self.add_rotation(&query.rotation);
                self.add_calculation(Calculation::Store(ValueSource::Fixed(
                    query.column_index,
                    rot_idx,
                )))
            }
            Expression::Advice(query) => {
                let rot_idx = self.add_rotation(&query.rotation);
                self.add_calculation(Calculation::Store(ValueSource::Advice(
                    query.column_index,
                    rot_idx,
                )))
            }
            Expression::Instance(query) => {
                let rot_idx = self.add_rotation(&query.rotation);
                self.add_calculation(Calculation::Store(ValueSource::Instance(
                    query.column_index,
                    rot_idx,
                )))
            }
            Expression::Challenge(challenge) => self.add_calculation(Calculation::Store(
                ValueSource::Challenge(challenge.index()),
            )),
            Expression::Negated(a) => match **a {
                Expression::Constant(scalar) => self.add_constant(&-scalar),
                _ => {
                    let result_a = self.add_expression(a);
                    match result_a {
                        ValueSource::Constant(0) => result_a,
                        _ => self.add_calculation(Calculation::Negate(result_a)),
                    }
                }
            },
            Expression::Sum(a, b) => {
                // Undo subtraction stored as a + (-b) in expressions
                match &**b {
                    Expression::Negated(b_int) => {
                        let result_a = self.add_expression(a);
                        let result_b = self.add_expression(b_int);
                        if result_a == ValueSource::Constant(0) {
                            self.add_calculation(Calculation::Negate(result_b))
                        } else if result_b == ValueSource::Constant(0) {
                            result_a
                        } else {
                            self.add_calculation(Calculation::Sub(result_a, result_b))
                        }
                    }
                    _ => {
                        let result_a = self.add_expression(a);
                        let result_b = self.add_expression(b);
                        if result_a == ValueSource::Constant(0) {
                            result_b
                        } else if result_b == ValueSource::Constant(0) {
                            result_a
                        } else if result_a <= result_b {
                            self.add_calculation(Calculation::Add(result_a, result_b))
                        } else {
                            self.add_calculation(Calculation::Add(result_b, result_a))
                        }
                    }
                }
            }
            Expression::Product(a, b) => {
                let result_a = self.add_expression(a);
                let result_b = self.add_expression(b);
                if result_a == ValueSource::Constant(0) || result_b == ValueSource::Constant(0) {
                    ValueSource::Constant(0)
                } else if result_a == ValueSource::Constant(1) {
                    result_b
                } else if result_b == ValueSource::Constant(1) {
                    result_a
                } else if result_a == ValueSource::Constant(2) {
                    self.add_calculation(Calculation::Double(result_b))
                } else if result_b == ValueSource::Constant(2) {
                    self.add_calculation(Calculation::Double(result_a))
                } else if result_a == result_b {
                    self.add_calculation(Calculation::Square(result_a))
                } else if result_a <= result_b {
                    self.add_calculation(Calculation::Mul(result_a, result_b))
                } else {
                    self.add_calculation(Calculation::Mul(result_b, result_a))
                }
            }
            Expression::Scaled(a, f) => {
                if *f == F::ZERO {
                    ValueSource::Constant(0)
                } else if *f == F::ONE {
                    self.add_expression(a)
                } else {
                    let cst = self.add_constant(f);
                    let result_a = self.add_expression(a);
                    self.add_calculation(Calculation::Mul(result_a, cst))
                }
            }
        }
    }

    /// Creates a new evaluation structure
    pub fn instance(&self) -> EvaluationData<F> {
        EvaluationData {
            intermediates: vec![F::ZERO; self.num_intermediates],
            rotations: vec![0usize; self.rotations.len()],
        }
    }

    pub fn evaluate<B: Basis>(
        &self,
        data: &mut EvaluationData<F>,
        fixed: &[Option<Polynomial<F, B>>],
        advice: &[Option<Polynomial<F, B>>],
        instance: &[Option<Polynomial<F, B>>],
        challenges: &[F],
        y_powers: &[F],
        beta: &F,
        gamma: &F,
        theta: &F,
        idx: usize,
        rot_scale: i32,
        isize: i32,
    ) -> F {
        // All rotation index values
        for (rot_idx, rot) in self.rotations.iter().enumerate() {
            data.rotations[rot_idx] = get_rotation_idx(idx, *rot, rot_scale, isize);
        }

        // All calculations, with cached intermediate results
        for calc in self.calculations.iter() {
            data.intermediates[calc.target] = calc.calculation.evaluate(
                &data.rotations,
                &self.constants,
                &data.intermediates,
                fixed,
                advice,
                instance,
                challenges,
                y_powers,
                beta,
                gamma,
                theta,
            );
        }

        // Return the result of the last calculation (if any)
        if let Some(calc) = self.calculations.last() {
            data.intermediates[calc.target]
        } else {
            F::ZERO
        }
    }
}

/// Simple evaluation of an expression
pub fn evaluate<F: Field, B: Basis>(
    expression: &Expression<F>,
    size: usize,
    rot_scale: i32,
    fixed: &[Polynomial<F, B>],
    advice: &[Polynomial<F, B>],
    instance: &[Polynomial<F, B>],
    challenges: &[F],
) -> Vec<F> {
    let mut values = vec![F::ZERO; size];
    let isize = size as i32;
    parallelize(&mut values, |values, start| {
        for (i, value) in values.iter_mut().enumerate() {
            let idx = start + i;
            *value = expression.evaluate(
                &|scalar| scalar,
                &|_| panic!("virtual selectors are removed during optimization"),
                &|query| {
                    fixed[query.column_index]
                        [get_rotation_idx(idx, query.rotation.0, rot_scale, isize)]
                },
                &|query| {
                    advice[query.column_index]
                        [get_rotation_idx(idx, query.rotation.0, rot_scale, isize)]
                },
                &|query| {
                    instance[query.column_index]
                        [get_rotation_idx(idx, query.rotation.0, rot_scale, isize)]
                },
                &|challenge| challenges[challenge.index()],
                &|a| -a,
                &|a, b| a + &b,
                &|a, b| a * b,
                &|a, scalar| a * scalar,
            );
        }
    });
    values
}
