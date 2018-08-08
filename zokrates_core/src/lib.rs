#![feature(box_patterns, box_syntax)]

#[macro_use]
extern crate lazy_static;
extern crate num;
extern crate reduce; // better reduce function than Iter.fold
extern crate serde; // serialization deserialization
extern crate serde_json;
#[macro_use]
extern crate serde_derive;
extern crate bincode;
extern crate regex;

mod parser;
mod imports;
mod semantics;
mod substitution;
mod flatten;
mod optimizer;
mod standard;
mod helpers;
mod types;
mod typed_absy;

pub mod absy;
pub mod flat_absy;
pub mod compile;
pub mod r1cs;
pub mod field;
pub mod verification;
#[cfg(feature = "libsnark")]
pub mod libsnark;