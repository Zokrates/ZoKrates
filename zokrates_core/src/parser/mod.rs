//!
//! @file parser.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

mod tokenize;
mod error;
mod parse;

pub use parser::error::Error;
pub use parser::parse::parse_program;
