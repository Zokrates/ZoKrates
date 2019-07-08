mod bn128;

use std::fs::File;
use zokrates_field::Field;

pub use self::bn128::G16;
#[cfg(feature = "libsnark")]
pub use self::bn128::GM17;
#[cfg(feature = "libsnark")]
pub use self::bn128::PGHR13;

use crate::ir;
use std::io::BufReader;

pub trait ProofSystem {
    fn setup<T: Field>(program: ir::Prog<T>, pk_path: &str, vk_path: &str);

    fn generate_proof<T: Field>(
        program: ir::Prog<T>,
        witness: ir::Witness<T>,
        pk_path: &str,
        proof_path: &str,
    ) -> bool;

    fn export_solidity_verifier(reader: BufReader<File>, is_abiv2: bool) -> String;
}
