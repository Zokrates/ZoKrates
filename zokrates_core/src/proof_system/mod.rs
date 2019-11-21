mod bn128;

use zokrates_field::field::FieldPrime;

pub use self::bn128::G16;
#[cfg(feature = "libsnark")]
pub use self::bn128::GM17;
#[cfg(feature = "libsnark")]
pub use self::bn128::PGHR13;

use crate::ir;

pub struct SetupKeypair {
    pub vk: String,
    pub pk: Vec<u8>,
}

impl SetupKeypair {
    pub fn from(vk: String, pk: Vec<u8>) -> SetupKeypair {
        SetupKeypair { vk, pk }
    }
}

pub trait ProofSystem {
    fn setup(program: ir::Prog<FieldPrime>) -> SetupKeypair;

    fn generate_proof(
        program: ir::Prog<FieldPrime>,
        witness: ir::Witness<FieldPrime>,
        proving_key: Vec<u8>,
    ) -> String;

    fn export_solidity_verifier(vk: String, is_abiv2: bool) -> String;
}
