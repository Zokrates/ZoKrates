pub mod bellman;
#[cfg(feature = "libsnark")]
pub mod libsnark;
pub mod zexe;

mod solidity;

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
    proof: T,
    inputs: Vec<String>,
    raw: String,
}

impl<T: Serialize + DeserializeOwned> Proof<T> {
    fn new(proof: T, inputs: Vec<String>, raw: String) -> Self {
        Proof { proof, inputs, raw }
    }
}

#[derive(Serialize, Deserialize)]
pub struct G1Affine(String, String);

// When G2 is defined on Fq2 field
#[derive(Serialize, Deserialize)]
pub struct G2Affine(G1Affine, G1Affine);

// When G2 is defined on Fq field. For BW6_761 curve
#[derive(Serialize, Deserialize)]
pub struct G2affineG2Fq(String, String);

impl ToString for G1Affine {
    fn to_string(&self) -> String {
        format!("{}, {}", self.0, self.1)
    }
}

impl ToString for G2Affine {
    fn to_string(&self) -> String {
        format!("[{}], [{}]", self.0.to_string(), self.1.to_string())
    }
}

impl ToString for G2affineG2Fq {
    fn to_string(&self) -> String {
        format!("{}, {}", self.0, self.1)
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
