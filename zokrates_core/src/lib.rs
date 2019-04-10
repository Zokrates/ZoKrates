#![feature(box_patterns, box_syntax)]

extern crate num;
extern crate num_bigint;
extern crate reduce; // better reduce function than Iter.fold
extern crate serde; // serialization deserialization
extern crate serde_json;
#[macro_use]
extern crate serde_derive;
extern crate bellman;
extern crate bimap;
extern crate bincode;
extern crate ff;
extern crate pairing;
#[cfg(feature = "wasm")]
extern crate parity_wasm;
extern crate regex;
#[cfg(feature = "wasm")]
extern crate rustc_hex;
#[cfg(feature = "wasm")]
extern crate serde_bytes;
#[cfg(feature = "wasm")]
extern crate wasmi;
extern crate zokrates_embed;
extern crate zokrates_field;

mod flatten;
mod helpers;
mod imports;
mod optimizer;
mod parser;
mod semantics;
mod standard;
mod static_analysis;
mod typed_absy;
mod types;

pub mod absy;
pub mod compile;
pub mod flat_absy;
pub mod ir;
pub mod proof_system;
