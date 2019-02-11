#![feature(box_patterns, box_syntax)]

extern crate num;
extern crate num_bigint;
extern crate reduce; // better reduce function than Iter.fold
extern crate serde; // serialization deserialization
extern crate serde_json;
#[macro_use]
extern crate serde_derive;
extern crate bimap;
extern crate bincode;
#[cfg(feature = "wasm")]
extern crate parity_wasm;
extern crate regex;
#[cfg(feature = "wasm")]
extern crate rustc_hex;
#[cfg(feature = "wasm")]
extern crate serde_bytes;
#[cfg(feature = "wasm")]
extern crate wasmi;
extern crate zokrates_field;

mod flatten;
mod helpers;
mod imports;
mod optimizer;
mod parser;
mod semantics;
#[cfg(feature = "libsnark")]
mod standard;
mod static_analysis;
mod typed_absy;
mod types;

pub mod absy;
pub mod compile;
pub mod flat_absy;
pub mod ir;
#[cfg(feature = "libsnark")]
pub mod libsnark;
#[cfg(feature = "libsnark")]
pub mod proof_system;
