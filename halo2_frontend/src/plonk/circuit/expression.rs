use crate::plonk::circuit::{
    Advice, AdviceQuery, Challenge, Column, Fixed, FixedQuery, Instance, InstanceQuery, Selector,
    VirtualCells,
};
use core::cmp::max;
use core::ops::{Add, Mul};
use halo2_middleware::circuit::{Any, ExpressionMid, QueryMid, VarMid};
use halo2_middleware::ff::Field;
use std::iter::{Product, Sum};
use std::ops::{Neg, Sub};

/// Low-degree expression representing an identity that must hold over the committed columns.
#[derive(Clone, PartialEq, Eq)]
pub enum Expression<F> {
    /// This is a constant polynomial
    Constant(F),
    /// This is a virtual selector
    Selector(Selector),
    /// This is a fixed column queried at a certain relative location
    Fixed(FixedQuery),
    /// This is an advice (witness) column queried at a certain relative location
    Advice(AdviceQuery),
    /// This is an instance (external) column queried at a certain relative location
    Instance(InstanceQuery),
    /// This is a challenge
    Challenge(Challenge),
    /// This is a negated polynomial
    Negated(Box<Expression<F>>),
    /// This is the sum of two polynomials
    Sum(Box<Expression<F>>, Box<Expression<F>>),
    /// This is the product of two polynomials
    Product(Box<Expression<F>>, Box<Expression<F>>),
    /// This is a scaled polynomial
    Scaled(Box<Expression<F>>, F),
}

impl<F> From<Expression<F>> for ExpressionMid<F> {
    fn from(val: Expression<F>) -> Self {
        match val {
            Expression::Constant(c) => ExpressionMid::Constant(c),
            Expression::Selector(_) => unreachable!(),
            Expression::Fixed(FixedQuery {
                column_index,
                rotation,
                ..
            }) => ExpressionMid::Var(VarMid::Query(QueryMid {
                column_index,
                column_type: Any::Fixed,
                rotation,
            })),
            Expression::Advice(AdviceQuery {
                column_index,
                rotation,
                ..
            }) => ExpressionMid::Var(VarMid::Query(QueryMid {
                column_index,
                column_type: Any::Advice,
                rotation,
            })),
            Expression::Instance(InstanceQuery {
                column_index,
                rotation,
                ..
            }) => ExpressionMid::Var(VarMid::Query(QueryMid {
                column_index,
                column_type: Any::Instance,
                rotation,
            })),
            Expression::Challenge(c) => ExpressionMid::Var(VarMid::Challenge(c.into())),
            Expression::Negated(e) => ExpressionMid::Negated(Box::new((*e).into())),
            Expression::Sum(lhs, rhs) => {
                ExpressionMid::Sum(Box::new((*lhs).into()), Box::new((*rhs).into()))
            }
            Expression::Product(lhs, rhs) => {
                ExpressionMid::Product(Box::new((*lhs).into()), Box::new((*rhs).into()))
            }
            Expression::Scaled(e, c) => {
                ExpressionMid::Product(Box::new((*e).into()), Box::new(ExpressionMid::Constant(c)))
            }
        }
    }
}

impl<F: Field> Expression<F> {
    /// Make side effects
    pub fn query_cells(&mut self, cells: &mut VirtualCells<'_, F>) {
        match self {
            Expression::Constant(_) => (),
            Expression::Selector(selector) => {
                if !cells.queried_selectors.contains(selector) {
                    cells.queried_selectors.push(*selector);
                }
            }
            Expression::Fixed(query) => {
                if query.index.is_none() {
                    let col = Column {
                        index: query.column_index,
                        column_type: Fixed,
                    };
                    cells.queried_cells.push((col, query.rotation).into());
                    query.index = Some(cells.meta.query_fixed_index(col, query.rotation));
                }
            }
            Expression::Advice(query) => {
                if query.index.is_none() {
                    let col = Column {
                        index: query.column_index,
                        column_type: Advice,
                    };
                    cells.queried_cells.push((col, query.rotation).into());
                    query.index = Some(cells.meta.query_advice_index(col, query.rotation));
                }
            }
            Expression::Instance(query) => {
                if query.index.is_none() {
                    let col = Column {
                        index: query.column_index,
                        column_type: Instance,
                    };
                    cells.queried_cells.push((col, query.rotation).into());
                    query.index = Some(cells.meta.query_instance_index(col, query.rotation));
                }
            }
            Expression::Challenge(_) => (),
            Expression::Negated(a) => a.query_cells(cells),
            Expression::Sum(a, b) => {
                a.query_cells(cells);
                b.query_cells(cells);
            }
            Expression::Product(a, b) => {
                a.query_cells(cells);
                b.query_cells(cells);
            }
            Expression::Scaled(a, _) => a.query_cells(cells),
        };
    }

    /// Evaluate the polynomial using the provided closures to perform the
    /// operations.
    #[allow(clippy::too_many_arguments)]
    pub fn evaluate<T>(
        &self,
        constant: &impl Fn(F) -> T,
        selector_column: &impl Fn(Selector) -> T,
        fixed_column: &impl Fn(FixedQuery) -> T,
        advice_column: &impl Fn(AdviceQuery) -> T,
        instance_column: &impl Fn(InstanceQuery) -> T,
        challenge: &impl Fn(Challenge) -> T,
        negated: &impl Fn(T) -> T,
        sum: &impl Fn(T, T) -> T,
        product: &impl Fn(T, T) -> T,
        scaled: &impl Fn(T, F) -> T,
    ) -> T {
        match self {
            Expression::Constant(scalar) => constant(*scalar),
            Expression::Selector(selector) => selector_column(*selector),
            Expression::Fixed(query) => fixed_column(*query),
            Expression::Advice(query) => advice_column(*query),
            Expression::Instance(query) => instance_column(*query),
            Expression::Challenge(value) => challenge(*value),
            Expression::Negated(a) => {
                let a = a.evaluate(
                    constant,
                    selector_column,
                    fixed_column,
                    advice_column,
                    instance_column,
                    challenge,
                    negated,
                    sum,
                    product,
                    scaled,
                );
                negated(a)
            }
            Expression::Sum(a, b) => {
                let a = a.evaluate(
                    constant,
                    selector_column,
                    fixed_column,
                    advice_column,
                    instance_column,
                    challenge,
                    negated,
                    sum,
                    product,
                    scaled,
                );
                let b = b.evaluate(
                    constant,
                    selector_column,
                    fixed_column,
                    advice_column,
                    instance_column,
                    challenge,
                    negated,
                    sum,
                    product,
                    scaled,
                );
                sum(a, b)
            }
            Expression::Product(a, b) => {
                let a = a.evaluate(
                    constant,
                    selector_column,
                    fixed_column,
                    advice_column,
                    instance_column,
                    challenge,
                    negated,
                    sum,
                    product,
                    scaled,
                );
                let b = b.evaluate(
                    constant,
                    selector_column,
                    fixed_column,
                    advice_column,
                    instance_column,
                    challenge,
                    negated,
                    sum,
                    product,
                    scaled,
                );
                product(a, b)
            }
            Expression::Scaled(a, f) => {
                let a = a.evaluate(
                    constant,
                    selector_column,
                    fixed_column,
                    advice_column,
                    instance_column,
                    challenge,
                    negated,
                    sum,
                    product,
                    scaled,
                );
                scaled(a, *f)
            }
        }
    }

    /// Evaluate the polynomial lazily using the provided closures to perform the
    /// operations.
    #[allow(clippy::too_many_arguments)]
    pub fn evaluate_lazy<T: PartialEq>(
        &self,
        constant: &impl Fn(F) -> T,
        selector_column: &impl Fn(Selector) -> T,
        fixed_column: &impl Fn(FixedQuery) -> T,
        advice_column: &impl Fn(AdviceQuery) -> T,
        instance_column: &impl Fn(InstanceQuery) -> T,
        challenge: &impl Fn(Challenge) -> T,
        negated: &impl Fn(T) -> T,
        sum: &impl Fn(T, T) -> T,
        product: &impl Fn(T, T) -> T,
        scaled: &impl Fn(T, F) -> T,
        zero: &T,
    ) -> T {
        match self {
            Expression::Constant(scalar) => constant(*scalar),
            Expression::Selector(selector) => selector_column(*selector),
            Expression::Fixed(query) => fixed_column(*query),
            Expression::Advice(query) => advice_column(*query),
            Expression::Instance(query) => instance_column(*query),
            Expression::Challenge(value) => challenge(*value),
            Expression::Negated(a) => {
                let a = a.evaluate_lazy(
                    constant,
                    selector_column,
                    fixed_column,
                    advice_column,
                    instance_column,
                    challenge,
                    negated,
                    sum,
                    product,
                    scaled,
                    zero,
                );
                negated(a)
            }
            Expression::Sum(a, b) => {
                let a = a.evaluate_lazy(
                    constant,
                    selector_column,
                    fixed_column,
                    advice_column,
                    instance_column,
                    challenge,
                    negated,
                    sum,
                    product,
                    scaled,
                    zero,
                );
                let b = b.evaluate_lazy(
                    constant,
                    selector_column,
                    fixed_column,
                    advice_column,
                    instance_column,
                    challenge,
                    negated,
                    sum,
                    product,
                    scaled,
                    zero,
                );
                sum(a, b)
            }
            Expression::Product(a, b) => {
                let (a, b) = if a.complexity() <= b.complexity() {
                    (a, b)
                } else {
                    (b, a)
                };
                let a = a.evaluate_lazy(
                    constant,
                    selector_column,
                    fixed_column,
                    advice_column,
                    instance_column,
                    challenge,
                    negated,
                    sum,
                    product,
                    scaled,
                    zero,
                );

                if a == *zero {
                    a
                } else {
                    let b = b.evaluate_lazy(
                        constant,
                        selector_column,
                        fixed_column,
                        advice_column,
                        instance_column,
                        challenge,
                        negated,
                        sum,
                        product,
                        scaled,
                        zero,
                    );
                    product(a, b)
                }
            }
            Expression::Scaled(a, f) => {
                let a = a.evaluate_lazy(
                    constant,
                    selector_column,
                    fixed_column,
                    advice_column,
                    instance_column,
                    challenge,
                    negated,
                    sum,
                    product,
                    scaled,
                    zero,
                );
                scaled(a, *f)
            }
        }
    }

    fn write_identifier<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        match self {
            Expression::Constant(scalar) => write!(writer, "{scalar:?}"),
            Expression::Selector(selector) => write!(writer, "selector[{}]", selector.0),
            Expression::Fixed(query) => {
                write!(
                    writer,
                    "fixed[{}][{}]",
                    query.column_index, query.rotation.0
                )
            }
            Expression::Advice(query) => {
                write!(
                    writer,
                    "advice[{}][{}]",
                    query.column_index, query.rotation.0
                )
            }
            Expression::Instance(query) => {
                write!(
                    writer,
                    "instance[{}][{}]",
                    query.column_index, query.rotation.0
                )
            }
            Expression::Challenge(challenge) => {
                write!(writer, "challenge[{}]", challenge.index())
            }
            Expression::Negated(a) => {
                writer.write_all(b"(-")?;
                a.write_identifier(writer)?;
                writer.write_all(b")")
            }
            Expression::Sum(a, b) => {
                writer.write_all(b"(")?;
                a.write_identifier(writer)?;
                writer.write_all(b"+")?;
                b.write_identifier(writer)?;
                writer.write_all(b")")
            }
            Expression::Product(a, b) => {
                writer.write_all(b"(")?;
                a.write_identifier(writer)?;
                writer.write_all(b"*")?;
                b.write_identifier(writer)?;
                writer.write_all(b")")
            }
            Expression::Scaled(a, f) => {
                a.write_identifier(writer)?;
                write!(writer, "*{f:?}")
            }
        }
    }

    /// Identifier for this expression. Expressions with identical identifiers
    /// do the same calculation (but the expressions don't need to be exactly equal
    /// in how they are composed e.g. `1 + 2` and `2 + 1` can have the same identifier).
    pub fn identifier(&self) -> String {
        let mut cursor = std::io::Cursor::new(Vec::new());
        self.write_identifier(&mut cursor).unwrap();
        String::from_utf8(cursor.into_inner()).unwrap()
    }

    /// Compute the degree of this polynomial
    pub fn degree(&self) -> usize {
        match self {
            Expression::Constant(_) => 0,
            Expression::Selector(_) => 1,
            Expression::Fixed(_) => 1,
            Expression::Advice(_) => 1,
            Expression::Instance(_) => 1,
            Expression::Challenge(_) => 0,
            Expression::Negated(poly) => poly.degree(),
            Expression::Sum(a, b) => max(a.degree(), b.degree()),
            Expression::Product(a, b) => a.degree() + b.degree(),
            Expression::Scaled(poly, _) => poly.degree(),
        }
    }

    /// Approximate the computational complexity of this expression.
    pub fn complexity(&self) -> usize {
        match self {
            Expression::Constant(_) => 0,
            Expression::Selector(_) => 1,
            Expression::Fixed(_) => 1,
            Expression::Advice(_) => 1,
            Expression::Instance(_) => 1,
            Expression::Challenge(_) => 0,
            Expression::Negated(poly) => poly.complexity() + 5,
            Expression::Sum(a, b) => a.complexity() + b.complexity() + 15,
            Expression::Product(a, b) => a.complexity() + b.complexity() + 30,
            Expression::Scaled(poly, _) => poly.complexity() + 30,
        }
    }

    /// Square this expression.
    pub fn square(self) -> Self {
        self.clone() * self
    }

    /// Returns whether or not this expression contains a simple `Selector`.
    pub(super) fn contains_simple_selector(&self) -> bool {
        self.evaluate(
            &|_| false,
            &|selector| selector.is_simple(),
            &|_| false,
            &|_| false,
            &|_| false,
            &|_| false,
            &|a| a,
            &|a, b| a || b,
            &|a, b| a || b,
            &|a, _| a,
        )
    }

    // TODO: Where is this used?
    /// Extracts a simple selector from this gate, if present
    pub(super) fn extract_simple_selector(&self) -> Option<Selector> {
        let op = |a, b| match (a, b) {
            (Some(a), None) | (None, Some(a)) => Some(a),
            (Some(_), Some(_)) => panic!("two simple selectors cannot be in the same expression"),
            _ => None,
        };

        self.evaluate(
            &|_| None,
            &|selector| {
                if selector.is_simple() {
                    Some(selector)
                } else {
                    None
                }
            },
            &|_| None,
            &|_| None,
            &|_| None,
            &|_| None,
            &|a| a,
            &op,
            &op,
            &|a, _| a,
        )
    }
}

impl<F: std::fmt::Debug> std::fmt::Debug for Expression<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Constant(scalar) => f.debug_tuple("Constant").field(scalar).finish(),
            Expression::Selector(selector) => f.debug_tuple("Selector").field(selector).finish(),
            // Skip enum variant and print query struct directly to maintain backwards compatibility.
            Expression::Fixed(query) => {
                let mut debug_struct = f.debug_struct("Fixed");
                match query.index {
                    None => debug_struct.field("query_index", &query.index),
                    Some(idx) => debug_struct.field("query_index", &idx),
                };
                debug_struct
                    .field("column_index", &query.column_index)
                    .field("rotation", &query.rotation)
                    .finish()
            }
            Expression::Advice(query) => {
                let mut debug_struct = f.debug_struct("Advice");
                match query.index {
                    None => debug_struct.field("query_index", &query.index),
                    Some(idx) => debug_struct.field("query_index", &idx),
                };
                debug_struct
                    .field("column_index", &query.column_index)
                    .field("rotation", &query.rotation);
                debug_struct.finish()
            }
            Expression::Instance(query) => {
                let mut debug_struct = f.debug_struct("Instance");
                match query.index {
                    None => debug_struct.field("query_index", &query.index),
                    Some(idx) => debug_struct.field("query_index", &idx),
                };
                debug_struct
                    .field("column_index", &query.column_index)
                    .field("rotation", &query.rotation)
                    .finish()
            }
            Expression::Challenge(challenge) => {
                f.debug_tuple("Challenge").field(challenge).finish()
            }
            Expression::Negated(poly) => f.debug_tuple("Negated").field(poly).finish(),
            Expression::Sum(a, b) => f.debug_tuple("Sum").field(a).field(b).finish(),
            Expression::Product(a, b) => f.debug_tuple("Product").field(a).field(b).finish(),
            Expression::Scaled(poly, scalar) => {
                f.debug_tuple("Scaled").field(poly).field(scalar).finish()
            }
        }
    }
}

impl<F: Field> Neg for Expression<F> {
    type Output = Expression<F>;
    fn neg(self) -> Self::Output {
        Expression::Negated(Box::new(self))
    }
}

impl<F: Field> Add for Expression<F> {
    type Output = Expression<F>;
    fn add(self, rhs: Expression<F>) -> Expression<F> {
        if self.contains_simple_selector() || rhs.contains_simple_selector() {
            panic!("attempted to use a simple selector in an addition");
        }
        Expression::Sum(Box::new(self), Box::new(rhs))
    }
}

impl<F: Field> Sub for Expression<F> {
    type Output = Expression<F>;
    fn sub(self, rhs: Expression<F>) -> Expression<F> {
        if self.contains_simple_selector() || rhs.contains_simple_selector() {
            panic!("attempted to use a simple selector in a subtraction");
        }
        Expression::Sum(Box::new(self), Box::new(-rhs))
    }
}

impl<F: Field> Mul for Expression<F> {
    type Output = Expression<F>;
    fn mul(self, rhs: Expression<F>) -> Expression<F> {
        if self.contains_simple_selector() && rhs.contains_simple_selector() {
            panic!("attempted to multiply two expressions containing simple selectors");
        }
        Expression::Product(Box::new(self), Box::new(rhs))
    }
}

impl<F: Field> Mul<F> for Expression<F> {
    type Output = Expression<F>;
    fn mul(self, rhs: F) -> Expression<F> {
        Expression::Scaled(Box::new(self), rhs)
    }
}

impl<F: Field> Sum<Self> for Expression<F> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|acc, x| acc + x)
            .unwrap_or(Expression::Constant(F::ZERO))
    }
}

impl<F: Field> Product<Self> for Expression<F> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|acc, x| acc * x)
            .unwrap_or(Expression::Constant(F::ONE))
    }
}

#[cfg(test)]
mod tests {
    use super::Expression;
    use halo2curves::bn256::Fr;

    #[test]
    fn iter_sum() {
        let exprs: Vec<Expression<Fr>> = vec![
            Expression::Constant(1.into()),
            Expression::Constant(2.into()),
            Expression::Constant(3.into()),
        ];
        let happened: Expression<Fr> = exprs.into_iter().sum();
        let expected: Expression<Fr> = Expression::Sum(
            Box::new(Expression::Sum(
                Box::new(Expression::Constant(1.into())),
                Box::new(Expression::Constant(2.into())),
            )),
            Box::new(Expression::Constant(3.into())),
        );

        assert_eq!(happened, expected);
    }

    #[test]
    fn iter_product() {
        let exprs: Vec<Expression<Fr>> = vec![
            Expression::Constant(1.into()),
            Expression::Constant(2.into()),
            Expression::Constant(3.into()),
        ];
        let happened: Expression<Fr> = exprs.into_iter().product();
        let expected: Expression<Fr> = Expression::Product(
            Box::new(Expression::Product(
                Box::new(Expression::Constant(1.into())),
                Box::new(Expression::Constant(2.into())),
            )),
            Box::new(Expression::Constant(3.into())),
        );

        assert_eq!(happened, expected);
    }
}
