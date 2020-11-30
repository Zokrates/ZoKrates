#![feature(box_patterns, box_syntax)]

extern crate cfg_if;
extern crate num;
extern crate num_bigint;
extern crate reduce; // better reduce function than Iter.fold
extern crate serde; // serialization deserialization
extern crate serde_json;
extern crate typed_arena;
#[macro_use]
extern crate serde_derive;
extern crate bincode;
extern crate csv;
extern crate hex;
extern crate lazy_static;
extern crate rand_0_4;
extern crate regex;
extern crate zokrates_common;
extern crate zokrates_field;
extern crate zokrates_pest_ast;

extern crate log;

extern crate bellman_ce as bellman;
extern crate ff_ce as ff;
extern crate pairing_ce as pairing;

cfg_if::cfg_if! {
    if #[cfg(feature = "ark")] {
        extern crate ark_bls12_377;
        extern crate ark_bn254;
        extern crate ark_bw6_761;
        extern crate ark_gm17;
        extern crate ark_ff;
        extern crate ark_ec;
        extern crate ark_serialize;
        extern crate ark_relations;
        extern crate rand_0_7;
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
