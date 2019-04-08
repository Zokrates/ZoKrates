extern crate libc;

use self::libc::{c_char, c_int, uint8_t};
use flat_absy::flat_variable::FlatVariable;
use proof_system::utils::{
    prepare_generate_proof, prepare_setup, SOLIDITY_G2_ADDITION_LIB, SOLIDITY_PAIRING_LIB,
};
use proof_system::ProofSystem;
use regex::Regex;
use std::fs::File;
use std::io::{BufRead, BufReader};
use zokrates_field::field::FieldPrime;
use zkinterface_builder::ZKinterfaceBuilder;
use core::borrow::Borrow;

pub struct ZkInterface {}

impl ZkInterface {
    pub fn new() -> ZkInterface {
        ZkInterface {}
    }
}

impl ProofSystem for ZkInterface {
    fn setup(
        &self,
        variables: Vec<FlatVariable>,
        a: Vec<Vec<(usize, FieldPrime)>>,
        b: Vec<Vec<(usize, FieldPrime)>>,
        c: Vec<Vec<(usize, FieldPrime)>>,
        num_inputs: usize,
        pk_path: &str,
        vk_path: &str,
    ) -> bool {
        let num_constraints = a.len();
        let num_variables = variables.len();

        // generate the r1cs (variables is not relevant)
        // this message should be output to a file "pk_path":
        // message type:
        //zkstandard::zkinterface_generated::zkinterface::R1CSConstraints

        create_zkinterface_r1cs(num_constraints,a,b,c, pk_path)
    }

    fn generate_proof(
        &self,
        pk_path: &str,
        proof_path: &str,
        publquery_inputs: Vec<FieldPrime>,
        private_inputs: Vec<FieldPrime>,
    ) -> bool {
        println!(
            "func generate_proof  is not implemented",
        );
        // assign the vars and create the witness
        // this message should be output to a file "proof_path":
        // message type:
        //zkstandard::zkinterface_generated::zkinterface::AssignedVariables
        return false
    }

    fn export_solidity_verifier(&self, reader: BufReader<File>) -> String {
        format!(
            "func export_solidity_verifier is not implemented",
        );

        return String::from("func export_solidity_verifier is not implemented")
    }
}

fn create_zkinterface_r1cs(
    num_constraints: usize,
    a: Vec<Vec<(usize, FieldPrime)>>,
    b: Vec<Vec<(usize, FieldPrime)>>,
    c: Vec<Vec<(usize, FieldPrime)>>,
    output_path: &str,
    ) -> bool {

    let builder = ZKinterfaceBuilder::new();

    builder.create_file(num_constraints,&a,&b,&c,output_path);

    return true
}

