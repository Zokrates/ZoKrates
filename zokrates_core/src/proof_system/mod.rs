mod bn128;

use zokrates_field::field::FieldPrime;

pub use self::bn128::G16;
#[cfg(feature = "libsnark")]
pub use self::bn128::GM17;
#[cfg(feature = "libsnark")]
pub use self::bn128::PGHR13;

use crate::ir;

// We only need to serialize this struct, there is no need for deserialization as keys are
// used separately in other use cases
#[derive(Serialize)]
pub struct SetupKeypair {
    pub vk: Vec<u8>,
    pub pk: Vec<u8>,
}

impl SetupKeypair {
    pub fn from(vk: Vec<u8>, pk: Vec<u8>) -> SetupKeypair {
        SetupKeypair { vk, pk }
    }
}

pub trait ProofSystem {
    fn setup(&self, program: ir::Prog<FieldPrime>) -> SetupKeypair;

    fn generate_proof(
        &self,
        program: ir::Prog<FieldPrime>,
        witness: ir::Witness<FieldPrime>,
        proving_key: Vec<u8>,
    ) -> String;

    fn export_solidity_verifier(&self, vk: Vec<u8>, abi_v2: bool) -> String;

    fn verify(&self, vk: Vec<u8>, proof: String) -> bool;
}
