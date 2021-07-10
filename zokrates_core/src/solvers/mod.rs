use serde::{Deserialize, Serialize};
use std::fmt;

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize, Hash, Eq)]
pub enum Solver {
    ConditionEq,
    Bits(usize),
    Div,
    Xor,
    Or,
    ShaAndXorAndXorAnd,
    ShaCh,
    EuclideanDiv,
    #[cfg(feature = "bellman")]
    Sha256Round,
    #[cfg(feature = "ark")]
    SnarkVerifyBls12377(usize),
}

impl fmt::Display for Solver {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Solver {
    pub fn get_signature(&self) -> (usize, usize) {
        match self {
            Solver::ConditionEq => (1, 2),
            Solver::Bits(bit_width) => (1, *bit_width),
            Solver::Div => (2, 1),
            Solver::Xor => (2, 1),
            Solver::Or => (2, 1),
            Solver::ShaAndXorAndXorAnd => (3, 1),
            Solver::ShaCh => (3, 1),
            Solver::EuclideanDiv => (2, 2),
            #[cfg(feature = "bellman")]
            Solver::Sha256Round => (768, 26935),
            #[cfg(feature = "ark")]
            Solver::SnarkVerifyBls12377(n) => (26 + 3 * n, 41991 + 4972 * n),
        }
    }
}

impl Solver {
    pub fn bits(width: usize) -> Self {
        Solver::Bits(width)
    }
}
