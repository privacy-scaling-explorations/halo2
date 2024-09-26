use std::fmt;

use super::TableColumn;
use crate::plonk::{Column, Selector};
use halo2_middleware::circuit::Any;

/// This is an error that could occur during circuit synthesis.  
///
/// **NOTE**: [`AssignError`] is introduced to provide more debugging info     
/// to developers when assigning witnesses to circuit cells.  
/// Hence, they are used for [`MockProver`] and [`WitnessCollection`].  
/// The [`keygen`] process use the [`NotEnoughRowsAvailable`], since it is just enough.
#[derive(Debug)]
pub enum Error {
    /// This is an error that can occur during synthesis of the circuit, for
    /// example, when the witness is not present.
    Synthesis,
    /// Out of bounds index passed to a backend
    BoundsFailure,
    /// `k` is too small for the given circuit.
    NotEnoughRowsAvailable {
        /// The current value of `k` being used.
        current_k: u32,
    },
    /// Circuit synthesis requires global constants, but circuit configuration did not
    /// call [`ConstraintSystem::enable_constant`] on fixed columns with sufficient space.
    ///
    /// [`ConstraintSystem::enable_constant`]: crate::plonk::ConstraintSystem::enable_constant
    NotEnoughColumnsForConstants,
    /// The instance sets up a copy constraint involving a column that has not been
    /// included in the permutation.
    ColumnNotInPermutation(Column<Any>),
    /// An error relating to a lookup table.
    TableError(TableError),
    /// An error relating to a circuit assignment.
    AssignError(AssignError),
    /// Generic error not covered by previous cases
    Other(String),
}

impl Error {
    /// Constructs an `Error::NotEnoughRowsAvailable`.
    pub fn not_enough_rows_available(current_k: u32) -> Self {
        Error::NotEnoughRowsAvailable { current_k }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Synthesis => write!(f, "General synthesis error"),
            Error::BoundsFailure => write!(f, "An out-of-bounds index was passed to the backend"),
            Error::NotEnoughRowsAvailable { current_k } => write!(
                f,
                "k = {current_k} is too small for the given circuit. Try using a larger value of k",
            ),
            Error::NotEnoughColumnsForConstants => {
                write!(
                    f,
                    "Too few fixed columns are enabled for global constants usage"
                )
            }
            Error::ColumnNotInPermutation(column) => write!(
                f,
                "Column {column:?} must be included in the permutation. Help: try applying `meta.enable_equalty` on the column",
            ),
            Error::TableError(error) => write!(f, "{error}"),
            Error::AssignError(error) => write!(f, "{error}"),
            Error::Other(error) => write!(f, "Other: {error}"),
        }
    }
}

/// This is an error that could occur during table synthesis.
#[derive(Debug)]
pub enum TableError {
    /// A `TableColumn` has not been assigned.
    ColumnNotAssigned(TableColumn),
    /// A Table has columns of uneven lengths.
    UnevenColumnLengths((TableColumn, usize), (TableColumn, usize)),
    /// Attempt to assign a used `TableColumn`
    UsedColumn(TableColumn),
    /// Attempt to overwrite a default value
    OverwriteDefault(TableColumn, String, String),
}

impl fmt::Display for TableError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TableError::ColumnNotAssigned(col) => {
                write!(
                    f,
                    "{col:?} not fully assigned. Help: assign a value at offset 0.",
                )
            }
            TableError::UnevenColumnLengths((col, col_len), (table, table_len)) => write!(
                f,
                "{col:?} has length {col_len} while {table:?} has length {table_len}",
            ),
            TableError::UsedColumn(col) => {
                write!(f, "{col:?} has already been used")
            }
            TableError::OverwriteDefault(col, default, val) => {
                write!(
                    f,
                    "Attempted to overwrite default value {default} with {val} in {col:?}",
                )
            }
        }
    }
}

/// This is an error that could occur during `assign_advice`, `assign_fixed`, `copy`, etc.
#[derive(Debug)]
pub enum AssignError {
    AssignAdvice {
        desc: String,
        col: Column<Any>,
        row: usize,
        usable_rows: (usize, usize),
        k: u32,
    },
    AssignFixed {
        desc: String,
        col: Column<Any>,
        row: usize,
        usable_rows: (usize, usize),
        k: u32,
    },
    EnableSelector {
        desc: String,
        selector: Selector,
        row: usize,
        usable_rows: (usize, usize),
        k: u32,
    },
    QueryInstance {
        col: Column<Any>,
        row: usize,
        usable_rows: (usize, usize),
        k: u32,
    },
    Copy {
        left_col: Column<Any>,
        left_row: usize,
        right_col: Column<Any>,
        right_row: usize,
        usable_rows: (usize, usize),
        k: u32,
    },
    FillFromRow {
        col: Column<Any>,
        from_row: usize,
        usable_rows: (usize, usize),
        k: u32,
    },
    WitnessMissing {
        func: String,
        desc: String,
    },
}

impl fmt::Display for AssignError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AssignError::AssignAdvice { desc, col, row, usable_rows:(start, end), k } => write!(
                f,
                "assign_advice `{}` error: column={:?}({}), row={}, usable_rows={}..{}, k={}",
                desc,
                col.column_type(),
                col.index(),
                row,
                start, end,
                k,
            ),
            AssignError::AssignFixed {desc, col, row, usable_rows: (start, end), k } => write!(
                f,
                "assign_fixed `{}` error: column={:?}({}), row={}, usable_rows={}..{}, k={}",
                desc,
                col.column_type(),
                col.index(),
                row,
                start, end,
                k,
            ),
            AssignError::EnableSelector { desc, selector, row, usable_rows: (start, end), k } => write!(
                f,
                "enable_selector `{}` error: column=Selector({:?}), row={}, usable_rows={}..{}, k={}",
                desc,
                selector.index(),
                row,
                start, end,
                k,
            ),
            AssignError::QueryInstance { col, row, usable_rows:(start, end), k } => write!(
                f,
                "query_instance error: column={:?}({}), row={}, usable_rows={}..{}, k={}",
                col.column_type,
                col.index(),
                row,
                start,
                end,
                k,
            ),
            AssignError::Copy { left_col, left_row, right_col, right_row, usable_rows:(start, end), k } => write!(
                f,
                "copy error: left_column={:?}({}), left_row={}, right_column={:?}({}), right_row={}, usable_rows={}..{}, k={}",
                left_col.column_type(),
                left_col.index(),
                left_row,
                right_col.column_type(),
                right_col.index(),
                right_row,
                start, end,
                k,
            ),
            AssignError::FillFromRow { col, from_row, usable_rows:(start, end), k } => write!(
                f,
                "fill_from_row error: column={:?}({}), from_row={}, usable_rows={}..{}, k={}",
                col.column_type(),
                col.index(),
                from_row,
                start, end,
                k,
            ),
            AssignError::WitnessMissing { func, desc } => write!(f, "witness missing/unknown when {} `{}`", func, desc),
        }
    }
}
