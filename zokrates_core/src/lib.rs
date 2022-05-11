#![feature(box_patterns, box_syntax)]

cfg_if::cfg_if! {
    if #[cfg(feature = "bellman")] {
        extern crate bellman_ce as bellman;
        extern crate ff_ce as ff;
        extern crate pairing_ce as pairing;
    }
}

mod flatten;
pub mod imports;
mod macros;
mod optimizer;
mod semantics;
mod static_analysis;
use zokrates_ast::zir;

pub use zokrates_ast::untyped as absy;
pub mod compile;
pub use zokrates_ast::flat as flat_absy;
pub mod proof_system;
pub use zokrates_ast::typed as typed_absy;
