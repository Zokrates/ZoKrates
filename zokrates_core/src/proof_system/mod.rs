mod bn128;

use zokrates_field::field::FieldPrime;
use serde::ser::{Serialize, SerializeStruct, Serializer};

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

impl Serialize for SetupKeypair {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut s = serializer.serialize_struct("SetupKeypair", 2)?;
        s.serialize_field("vk", &self.vk)?;
        s.serialize_field("pk", &self.pk)?;
        s.end()
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

    fn export_solidity_verifier(&self, vk: String, is_abiv2: bool) -> String;
}
