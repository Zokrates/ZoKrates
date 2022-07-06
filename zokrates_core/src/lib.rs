#![feature(box_patterns, box_syntax)]

pub mod compile;
mod flatten;
pub mod imports;
mod macros;
mod optimizer;
mod semantics;
mod static_analysis;
