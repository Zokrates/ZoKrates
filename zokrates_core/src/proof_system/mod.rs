mod bn128;

use std::fs::File;
use zokrates_field::field::FieldPrime;

pub use self::bn128::G16;

use crate::ir;
use std::io::BufReader;

pub trait ProofSystem {
    fn setup(&self, program: ir::Prog<FieldPrime>) -> (String, Vec<u8>);

    fn generate_proof(
        &self,
        program: ir::Prog<FieldPrime>,
        witness: ir::Witness<FieldPrime>,
        proving_key: &[u8],
    ) -> String;

    fn export_solidity_verifier(&self, vk: String, is_abiv2: bool) -> String;
}
