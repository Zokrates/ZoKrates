// see https://github.com/mcarton/rust-derivative/issues/115
#![allow(clippy::incorrect_partial_ord_impl_on_ord_type)]

pub mod common;
pub mod flat;
pub mod ir;
pub mod typed;
pub mod untyped;
pub mod zir;

pub use common::Solver;
