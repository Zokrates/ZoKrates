extern crate serde_json;
extern crate zokrates_core;
#[macro_use]
extern crate serde_derive;

#[macro_use]
mod utils;

use utils::compare;
use utils::compile;
use utils::read_file;
use utils::Tests;
use zokrates_core::field::Field;
use zokrates_core::field::FieldPrime;

zokrates_test! {
    add,
    sub,
}
