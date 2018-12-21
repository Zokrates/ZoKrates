extern crate zokrates_core;

mod utils;

use utils::compile_test;
use zokrates_core::field::FieldPrime;

#[test]
fn add() {
    let code = include_str!("add.code");
    let bin = compile_test(code).unwrap();

    let input = vec![21, 33];
    let expected_output = vec![FieldPrime::from(21 + 33)];

    let output = bin.execute(&input).unwrap().return_values();

    assert_eq!(
        output, expected_output,
        "

{}

Called with {:?}
Expected {:?}
Returned {:?}
",
        code, input, expected_output, output
    );
}
