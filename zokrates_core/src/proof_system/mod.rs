mod bn128;
#[cfg(feature = "libsnark")]
mod utils;

use flat_absy::flat_variable::FlatVariable;
use std::fs::File;
use zokrates_field::field::FieldPrime;

#[cfg(feature = "libsnark")]
pub use self::bn128::GM17;
#[cfg(feature = "libsnark")]
pub use self::bn128::PGHR13;

use ir;
use std::io::BufReader;

pub trait ProofSystem {
    fn setup(&self, program: ir::Prog<FieldPrime>, pk_path: &str, vk_path: &str) -> Metadata;

    fn generate_proof(
        &self,
        program: ir::Prog<FieldPrime>,
        witness: ir::Witness<FieldPrime>,
        metadata: Metadata,
        pk_path: &str,
        proof_path: &str,
    ) -> bool;

    fn export_solidity_verifier(&self, reader: BufReader<File>) -> String;
}

#[derive(Serialize, Deserialize, Debug)]
pub struct Metadata {
    offset: usize,
    variables: Vec<FlatVariable>,
}
