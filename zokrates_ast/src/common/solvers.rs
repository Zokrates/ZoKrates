use crate::zir::ZirFunction;
use serde::{Deserialize, Serialize};
use std::fmt;

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize, Hash, Eq)]
pub struct RefCall {
    pub index: usize,
    pub argument_count: usize,
}

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
    Ref(RefCall),
    #[cfg(feature = "bellman")]
    Sha256Round,
    #[cfg(feature = "ark")]
    SnarkVerifyBls12377(usize),
}

impl<'ast, T> fmt::Display for Solver<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Solver::ConditionEq => write!(f, "ConditionEq"),
            Solver::Bits(n) => write!(f, "Bits({})", n),
            Solver::Div => write!(f, "Div"),
            Solver::Xor => write!(f, "Xor"),
            Solver::Or => write!(f, "Or"),
            Solver::ShaAndXorAndXorAnd => write!(f, "ShaAndXorAndXorAnd"),
            Solver::ShaCh => write!(f, "ShaCh"),
            Solver::EuclideanDiv => write!(f, "EuclideanDiv"),
            Solver::Zir(_) => write!(f, "Zir(..)"),
            Solver::Ref(call) => write!(f, "Ref@{}({})", call.index, call.argument_count),
            #[cfg(feature = "bellman")]
            Solver::Sha256Round => write!(f, "Sha256Round"),
            #[cfg(feature = "ark")]
            Solver::SnarkVerifyBls12377(n) => write!(f, "SnarkVerifyBls12377({})", n),
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
            Solver::Ref(c) => (c.argument_count, 1),
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
