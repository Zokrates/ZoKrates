pub mod bellman;
#[cfg(feature = "libsnark")]
pub mod libsnark;
pub mod zexe;

pub mod solidity;

use crate::ir;
use proof_system::solidity::SolidityAbi;
use serde::de::DeserializeOwned;
use serde::Serialize;
use zokrates_field::Field;

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

#[derive(Serialize, Deserialize)]
pub struct Proof<T> {
    proof: T,
    inputs: Vec<String>,
    raw: Option<String>,
}

impl<T: Serialize + DeserializeOwned> Proof<T> {
    fn new(proof: T, inputs: Vec<String>, raw: Option<String>) -> Self {
        Proof { proof, inputs, raw }
    }
}

pub type Fr = String;
pub type Fq = String;
pub type Fq2 = (String, String);

#[derive(Serialize, Deserialize)]
pub struct G1Affine(Fq, Fq);

// When G2 is defined on Fq2 field
#[derive(Serialize, Deserialize)]
pub struct G2Affine(Fq2, Fq2);

// When G2 is defined on a Fq field (BW6_761 curve)
#[derive(Serialize, Deserialize)]
pub struct G2AffineFq(Fq, Fq);

impl ToString for G1Affine {
    fn to_string(&self) -> String {
        format!("{}, {}", self.0, self.1)
    }
}

impl ToString for G2AffineFq {
    fn to_string(&self) -> String {
        format!("{}, {}", self.0, self.1)
    }
}
impl ToString for G2Affine {
    fn to_string(&self) -> String {
        format!(
            "[{}, {}], [{}, {}]",
            (self.0).0,
            (self.0).1,
            (self.1).0,
            (self.1).1
        )
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
