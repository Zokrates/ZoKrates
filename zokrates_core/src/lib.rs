#![feature(box_patterns, box_syntax)]

extern crate fnv;
extern crate num;
extern crate num_bigint;
extern crate reduce; // better reduce function than Iter.fold
extern crate serde; // serialization deserialization
extern crate serde_json;
extern crate typed_arena;
#[macro_use]
extern crate serde_derive;
extern crate bellman;
extern crate bincode;
extern crate ff;
extern crate lazy_static;
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
extern crate zokrates_pest_ast;

mod embed;
mod flatten;
mod helpers;
mod imports;
mod parser;
mod semantics;
mod static_analysis;
mod typed_absy;
mod types;

pub mod absy;
pub mod compile;
pub mod flat_absy;
pub mod ir;
pub mod optimizer;
pub mod proof_system;
