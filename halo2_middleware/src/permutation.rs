use serde::{Serialize, Deserialize};
use crate::circuit::{Cell, ColumnMid};

#[derive(Clone, Debug)]
pub struct AssemblyMid {
    pub copies: Vec<(Cell, Cell)>,
}

/// A permutation argument.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ArgumentMid {
    /// A sequence of columns involved in the argument.
    pub columns: Vec<ColumnMid>,
}
