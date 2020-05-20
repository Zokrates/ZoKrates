mod bn128;

pub use self::bn128::G16;
#[cfg(feature = "libsnark")]
pub use self::bn128::GM17;
#[cfg(feature = "libsnark")]
pub use self::bn128::PGHR13;

use crate::ir;
use zokrates_field::Field;

// We only need to serialize this struct, there is no need for deserialization as keys are
// used separately in other use cases
#[derive(Serialize)]
pub struct SetupKeypair {
    pub vk: String,
    pub pk: Vec<u8>,
}

impl SetupKeypair {
    pub fn from(vk: String, pk: Vec<u8>) -> SetupKeypair {
        SetupKeypair { vk, pk }
    }
}

pub enum SolidityAbi {
    V1,
    V2,
}

impl SolidityAbi {
    pub fn from(v: &str) -> Result<Self, &str> {
        match v {
            "v1" => Ok(SolidityAbi::V1),
            "v2" => Ok(SolidityAbi::V2),
            _ => Err("Invalid ABI version"),
        }
    }
}

pub trait ProofSystem<T: Field> {
    fn setup(program: ir::Prog<T>) -> SetupKeypair;

    fn generate_proof(
        program: ir::Prog<T>,
        witness: ir::Witness<T>,
        proving_key: Vec<u8>,
    ) -> String;

    fn export_solidity_verifier(vk: String, abi: SolidityAbi) -> String;

    fn verify(vk: String, proof: String) -> bool;
}
