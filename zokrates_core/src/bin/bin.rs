extern crate zokrates_core;
extern crate zokrates_field;

use zokrates_core::flat_absy::FlatVariable;
use zokrates_core::ir::*;
use zokrates_core::typed_absy::types::{Signature, Type};
use zokrates_field::field::FieldPrime;
use zokrates_core::proof_system::{self, ProofSystem};

fn main() {
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

    let result: (String, Vec<u8>) = proof_system::GM17{}.setup(program.clone());
    let witness = program
                    .clone()
                    .execute(&vec![FieldPrime::from(42)])
                    .unwrap();

    println!("\n{}", result.0.as_str());
    println!("\n{:?}", result.1);
}