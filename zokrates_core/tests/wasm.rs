wasm_bindgen_test_configure!(run_in_browser);

extern crate wasm_bindgen_test;
extern crate zokrates_core;
extern crate zokrates_field;
use wasm_bindgen_test::*;
use zokrates_core::flat_absy::FlatVariable;
use zokrates_core::ir::{Function, Prog, Statement};
use zokrates_core::proof_system::ProofSystem;
use zokrates_core::typed_absy::{Signature, Type};
use zokrates_field::field::FieldPrime;

use zokrates_core::proof_system::G16;

#[wasm_bindgen_test]
fn generate_proof() {
    let program: Prog<FieldPrime> = Prog {
        main: Function {
            id: String::from("main"),
            arguments: vec![FlatVariable::new(0)],
            returns: vec![FlatVariable::public(0)],
            statements: vec![Statement::Constraint(
                FlatVariable::new(0).into(),
                FlatVariable::public(0).into(),
            )],
        },
        private: vec![false],
        signature: Signature::new()
            .inputs(vec![Type::FieldElement])
            .outputs(vec![Type::FieldElement]),
    };

    let witness = program
        .clone()
        .execute(&vec![FieldPrime::from(42)])
        .unwrap();

    let keys = G16::setup(program.clone());
    let proof = G16::generate_proof(program, witness, keys.pk);
    println!("{:?}", proof);
}
