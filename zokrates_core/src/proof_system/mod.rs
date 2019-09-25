mod bn128;

use std::fs::File;
use zokrates_field::field::FieldPrime;

pub use self::bn128::G16;
#[cfg(feature = "libsnark")]
pub use self::bn128::GM17;
#[cfg(feature = "libsnark")]
pub use self::bn128::PGHR13;

use crate::ir;
use std::io::BufReader;

pub trait ProofSystem {
    fn setup(&self, program: ir::Prog<FieldPrime>, pk_path: &str, vk_path: &str);

    fn setup_c(&self, program: ir::Prog<FieldPrime>) -> (String, Vec<u8>);

    fn generate_proof(
        &self,
        program: ir::Prog<FieldPrime>,
        witness: ir::Witness<FieldPrime>,
        pk_path: &str,
        proof_path: &str,
    ) -> bool;

    fn generate_proof_c(
        &self,
        program: ir::Prog<FieldPrime>,
        witness: ir::Witness<FieldPrime>,
        proving_key: &[u8],
    ) -> String;

    fn export_solidity_verifier(&self, reader: BufReader<File>, is_abiv2: bool) -> String;

    fn export_solidity_verifier_c(&self, vk: String, is_abiv2: bool) -> String;
}
