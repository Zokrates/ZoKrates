mod bn128;

pub use self::bn128::G16;
#[cfg(feature = "libsnark")]
pub use self::bn128::GM17;
#[cfg(feature = "libsnark")]
pub use self::bn128::PGHR13;

use crate::ir;
use serde::de::DeserializeOwned;
use serde::Serialize;
use zokrates_field::Field;

// We only need to serialize this struct, there is no need for deserialization as keys are
// used separately in other use cases
#[derive(Serialize)]
pub struct SetupKeypair<V> {
    pub vk: V,
    pub pk: Vec<u8>,
}

impl<V: Serialize + DeserializeOwned> SetupKeypair<V> {
    pub fn new(vk: V, pk: Vec<u8>) -> SetupKeypair<V> {
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

#[derive(Serialize, Deserialize)]
pub struct Proof<T> {
    points: T,
    inputs: Vec<String>,
    raw: String,
}

impl<T: Serialize + DeserializeOwned> Proof<T> {
    fn new(points: T, inputs: Vec<String>, raw: String) -> Self {
        Proof {
            points,
            inputs,
            raw,
        }
    }
}

pub trait ProofSystem<T: Field>
where
    Self::VerificationKey: Serialize + DeserializeOwned,
    Self::ProofPoints: Serialize + DeserializeOwned,
{
    type VerificationKey;
    type ProofPoints;

    fn setup(program: ir::Prog<T>) -> SetupKeypair<Self::VerificationKey>;

    fn generate_proof(
        program: ir::Prog<T>,
        witness: ir::Witness<T>,
        proving_key: Vec<u8>,
    ) -> Proof<Self::ProofPoints>;

    fn export_solidity_verifier(vk: Self::VerificationKey, abi: SolidityAbi) -> String;

    fn verify(vk: Self::VerificationKey, proof: Proof<Self::ProofPoints>) -> bool;
}
