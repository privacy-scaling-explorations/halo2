use self::sealed::SealedPhase;

pub mod sealed {
    /// Phase of advice column
    #[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
    pub struct Phase(pub u8);

    impl Phase {
        pub fn prev(&self) -> Option<Phase> {
            self.0.checked_sub(1).map(Phase)
        }
    }

    impl SealedPhase for Phase {
        fn to_sealed(self) -> Phase {
            self
        }
    }

    /// Sealed trait to help keep `Phase` private.
    pub trait SealedPhase {
        fn to_sealed(self) -> Phase;
    }
}

/// Phase of advice column
pub trait Phase: SealedPhase {}

impl<P: SealedPhase> Phase for P {}

/// First phase
#[derive(Debug)]
pub struct FirstPhase;

impl SealedPhase for FirstPhase {
    fn to_sealed(self) -> sealed::Phase {
        sealed::Phase(0)
    }
}

/// Second phase
#[derive(Debug)]
pub struct SecondPhase;

impl SealedPhase for SecondPhase {
    fn to_sealed(self) -> sealed::Phase {
        sealed::Phase(1)
    }
}

/// Third phase
#[derive(Debug)]
pub struct ThirdPhase;

impl SealedPhase for ThirdPhase {
    fn to_sealed(self) -> sealed::Phase {
        sealed::Phase(2)
    }
}
