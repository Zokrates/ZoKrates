mod bn128;
mod utils;

use ir::{Prog, Witness};
use std::fs::File;
use zokrates_field::field::FieldPrime;

pub use self::bn128::GM17;
pub use self::bn128::PGHR13;
use std::io::BufReader;

pub trait ProofSystem {
    fn setup(&self, program: Prog<FieldPrime>, pk_path: &str, vk_path: &str) -> bool;

    fn generate_proof(&self, witness: Witness<FieldPrime>, pk_path: &str, proof_path: &str)
        -> bool;

    fn export_solidity_verifier(&self, reader: BufReader<File>) -> String;
}
