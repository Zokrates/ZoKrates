#[macro_use]
extern crate serde_derive;

#[macro_use]
mod utils;

include!(concat!(env!("OUT_DIR"), "/tests.rs"));
