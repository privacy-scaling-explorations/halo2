use crate::arithmetic::{best_multiexp, parallelize};
use pairing::arithmetic::CurveAffine;

/// A multiscalar multiplication in the polynomial commitment scheme
#[derive(Debug, Clone)]
pub struct MSM<C: CurveAffine> {
    scalars: Vec<C::Scalar>,
    bases: Vec<C>,
}

impl<C: CurveAffine> Default for MSM<C> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, C: CurveAffine> MSM<C> {
    /// Create a new, empty MSM using the provided parameters.
    pub fn new() -> Self {
        MSM {
            scalars: vec![],
            bases: vec![],
        }
    }

    /// Add another multiexp into this one
    pub fn add_msm(&mut self, other: &Self) {
        self.scalars.extend(other.scalars.iter());
        self.bases.extend(other.bases.iter());
    }

    /// Add arbitrary term (the scalar and the point)
    pub fn append_term(&mut self, scalar: C::Scalar, point: C) {
        self.scalars.push(scalar);
        self.bases.push(point);
    }

    /// Scale all scalars in the MSM by some scaling factor
    pub fn scale(&mut self, factor: C::Scalar) {
        if !self.scalars.is_empty() {
            parallelize(&mut self.scalars, |scalars, _| {
                for other_scalar in scalars {
                    *other_scalar *= &factor;
                }
            })
        }
    }

    /// Perform multiexp and check that it results in zero
    pub fn eval(self) -> C {
        best_multiexp(&self.scalars, &self.bases).into()
    }
    
    /// Check if eval is equal to identity
    pub fn check(self) -> bool {
        bool::from(self.eval().is_identity())
    }
}
