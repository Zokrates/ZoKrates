wasm_bindgen_test_configure!(run_in_browser);

extern crate wasm_bindgen_test;
extern crate zokrates_core;
extern crate zokrates_field;
use wasm_bindgen_test::*;
use zokrates_core::flat_absy::FlatVariable;
use zokrates_core::ir::{Function, Interpreter, Prog, Statement};
use zokrates_core::proof_system::Backend;
use zokrates_field::Bn128Field;

use zokrates_core::proof_system::bellman::Bellman;
use zokrates_core::proof_system::groth16::G16;

#[wasm_bindgen_test]
fn generate_proof() {
    let program: Prog<Bn128Field> = Prog {
        main: Function {
            id: String::from("main"),
            arguments: vec![FlatVariable::new(0)],
            returns: vec![FlatVariable::new(0)],
            statements: vec![Statement::Constraint(
                FlatVariable::new(0).into(),
                FlatVariable::new(0).into(),
            )],
        },
        private: vec![false],
    };

    let interpreter = Interpreter::default();
    let witness = interpreter
        .execute(&program, &[Bn128Field::from(42)])
        .unwrap();

    let keypair = <Bellman as Backend<Bn128Field, G16>>::setup(program.clone());
    let _proof =
        <Bellman as Backend<Bn128Field, G16>>::generate_proof(program, witness, keypair.pk);
}
