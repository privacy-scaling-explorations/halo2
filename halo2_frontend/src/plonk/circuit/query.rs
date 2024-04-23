use halo2_middleware::poly::Rotation;

/// Query of fixed column at a certain relative location
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct FixedQuery {
    /// Query index
    pub index: Option<usize>,
    /// Column index
    pub column_index: usize,
    /// Rotation of this query
    pub rotation: Rotation,
}

impl FixedQuery {
    /// Column index
    pub fn column_index(&self) -> usize {
        self.column_index
    }

    /// Rotation of this query
    pub fn rotation(&self) -> Rotation {
        self.rotation
    }
}

/// Query of advice column at a certain relative location
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct AdviceQuery {
    /// Query index
    pub index: Option<usize>,
    /// Column index
    pub column_index: usize,
    /// Rotation of this query
    pub rotation: Rotation,
}

impl AdviceQuery {
    /// Column index
    pub fn column_index(&self) -> usize {
        self.column_index
    }

    /// Rotation of this query
    pub fn rotation(&self) -> Rotation {
        self.rotation
    }
}

/// Query of instance column at a certain relative location
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct InstanceQuery {
    /// Query index
    pub index: Option<usize>,
    /// Column index
    pub column_index: usize,
    /// Rotation of this query
    pub rotation: Rotation,
}

impl InstanceQuery {
    /// Column index
    pub fn column_index(&self) -> usize {
        self.column_index
    }

    /// Rotation of this query
    pub fn rotation(&self) -> Rotation {
        self.rotation
    }
}
