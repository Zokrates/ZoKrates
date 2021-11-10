wasm_bindgen_test_configure!(run_in_browser);

extern crate wasm_bindgen_test;
extern crate zokrates_core;
extern crate zokrates_field;
use wasm_bindgen_test::*;
use zokrates_core::flat_absy::{FlatParameter, FlatVariable};
use zokrates_core::ir::{Interpreter, Prog, Statement};
use zokrates_core::proof_system::{Backend, NonUniversalBackend};
use zokrates_field::Bn128Field;

use zokrates_core::proof_system::bellman::Bellman;
use zokrates_core::proof_system::groth16::G16;

#[wasm_bindgen_test]
fn generate_proof() {
    let program: Prog<Bn128Field> = Prog {
        arguments: vec![FlatParameter::public(FlatVariable::new(0))],
        return_count: 1,
        statements: vec![Statement::constraint(
            FlatVariable::new(0),
            FlatVariable::new(0),
        )]
        .into(),
    };

    let interpreter = Interpreter::default();
    let witness = interpreter
        .execute(program.clone(), &[Bn128Field::from(42)])
        .unwrap();

    let keypair = <Bellman as NonUniversalBackend<Bn128Field, G16>>::setup(program.clone());
    let _proof =
        <Bellman as Backend<Bn128Field, G16>>::generate_proof(program, witness, keypair.pk);
}
