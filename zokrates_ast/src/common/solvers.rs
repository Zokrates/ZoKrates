use crate::zir::ZirFunction;
use serde::{Deserialize, Serialize};
use std::fmt;

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize, Hash, Eq)]
pub enum Solver<'ast, T> {
    ConditionEq,
    Bits(usize),
    Div,
    Xor,
    Or,
    ShaAndXorAndXorAnd,
    ShaCh,
    EuclideanDiv,
    #[serde(borrow)]
    Zir(ZirFunction<'ast, T>),
    #[cfg(feature = "bellman")]
    Sha256Round,
    #[cfg(feature = "ark")]
    SnarkVerifyBls12377(usize),
}

impl<'ast, T: fmt::Debug + fmt::Display> fmt::Display for Solver<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Solver::Zir(func) => write!(f, "Zir({})", func),
            _ => write!(f, "{:?}", self)
        }
    }
}

impl<'ast, T> Solver<'ast, T> {
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
            Solver::Zir(f) => (f.arguments.len(), 1),
            #[cfg(feature = "bellman")]
            Solver::Sha256Round => (768, 26935),
            #[cfg(feature = "ark")]
            Solver::SnarkVerifyBls12377(n) => (26 + 3 * n, 41991 + 4972 * n),
        }
    }
}

impl<'ast, T> Solver<'ast, T> {
    pub fn bits(width: usize) -> Self {
        Solver::Bits(width)
    }
}
