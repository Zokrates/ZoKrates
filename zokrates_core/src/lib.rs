#![feature(box_patterns, box_syntax)]

cfg_if::cfg_if! {
    if #[cfg(feature = "bellman")] {
        extern crate bellman_ce as bellman;
        extern crate ff_ce as ff;
        extern crate pairing_ce as pairing;
    }
}

mod embed;
mod flatten;
pub mod imports;
mod macros;
mod optimizer;
mod parser;
mod semantics;
mod solvers;
mod static_analysis;
mod zir;

pub mod absy;
pub mod compile;
pub mod flat_absy;
pub mod ir;
pub mod proof_system;
pub mod typed_absy;
