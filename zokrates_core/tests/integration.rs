extern crate serde_json;
#[macro_use]
extern crate serde_derive;
extern crate zokrates_core;
extern crate zokrates_field;

#[macro_use]
mod utils;

zokrates_test! {
    add,
    assert_one,
    array_if,
}
