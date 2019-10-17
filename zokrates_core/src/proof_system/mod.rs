mod bn128;

use std::fs::File;
use zokrates_field::Bn128Field;

pub use self::bn128::G16;
#[cfg(feature = "libsnark")]
pub use self::bn128::GM17;
#[cfg(feature = "libsnark")]
pub use self::bn128::PGHR13;

use crate::ir;
use std::io::BufReader;

pub trait ProofSystem {
    fn setup(&self, program: ir::Prog<Bn128Field>, pk_path: &str, vk_path: &str);

    fn generate_proof(
        &self,
        program: ir::Prog<Bn128Field>,
        witness: ir::Witness<Bn128Field>,
        pk_path: &str,
        proof_path: &str,
    ) -> bool;

    fn export_solidity_verifier(&self, reader: BufReader<File>, is_abiv2: bool) -> String;
}
