use super::ExprRef;
use super::Expression;

use halo2_middleware::ff::Field;

/// A field that allows to store `Expression`s in an arena.
pub trait FieldFront: Field {
    // Since base trait is not referenciable, we need a way to access it.
    // This is necessary to provide a way to transform fields from/to backend.
    type Field: Field;

    /// Transform FieldFront to Field
    fn into_field(self) -> Self::Field;

    /// Transform Field to FieldFront
    fn into_fieldfront(f: Self::Field) -> Self;

    /// Allocate a new expression to the arena.
    fn alloc(expr: Expression<Self>) -> ExprRef<Self>;

    /// Get an expression from the arena, panics if the reference is invalid.
    fn get(ref_: ExprRef<Self>) -> Expression<Self>;

    /// Replace old expression for a new one
    fn replace(ref_: crate::plonk::ExprRef<Self>, expr: Expression<Self>);
}

#[derive(Default)]
struct ExprArena<F: FieldFront>(Vec<Expression<F>>);

impl<F: FieldFront> ExprArena<F> {
    fn push(&mut self, expr: Expression<F>) -> crate::plonk::ExprRef<F> {
        let index = self.0.len();
        self.0.push(expr);
        ExprRef(index, std::marker::PhantomData)
    }
    fn get(&self, ref_: crate::plonk::ExprRef<F>) -> &Expression<F> {
        &self.0[ref_.0]
    }
    fn replace(&mut self, ref_: crate::plonk::ExprRef<F>, expr: Expression<F>) {
        self.0[ref_.0] = expr;
    }
}

#[macro_export]
macro_rules! expression_arena {
    ($arena:ident, $field:ty) => {
        fn $arena() -> &'static std::sync::RwLock<ExprArena<$field>> {
            static LINES: std::sync::OnceLock<std::sync::RwLock<ExprArena<$field>>> =
                std::sync::OnceLock::new();
            LINES.get_or_init(|| std::sync::RwLock::new(ExprArena::default()))
        }

        impl $crate::plonk::FieldFront for $field {
            type Field = $field;
            fn into_field(self) -> Self::Field {
                self
            }
            fn into_fieldfront(f: Self::Field) -> Self {
                f
            }
            fn alloc(expr: $crate::plonk::Expression<Self>) -> $crate::plonk::ExprRef<Self> {
                $arena().write().unwrap().push(expr)
            }
            fn get(ref_: $crate::plonk::ExprRef<Self>) -> $crate::plonk::Expression<Self> {
                *$arena().read().unwrap().get(ref_)
            }
            fn replace(ref_: $crate::plonk::ExprRef<Self>, expr: $crate::plonk::Expression<Self>) {
                $arena().write().unwrap().replace(ref_, expr);
            }
        }
        impl From<$field> for $crate::plonk::ExprRef<$field> {
            fn from(f: $field) -> Self {
                $crate::plonk::FieldFront::alloc($crate::plonk::Expression::Constant(f))
            }
        }
    };
}

// Field scalar arenas
expression_arena!(arena_bn256_fr, halo2curves::bn256::Fr);
expression_arena!(arena_pasta_fp, halo2curves::pasta::Fp);
