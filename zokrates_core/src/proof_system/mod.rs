pub mod bellman;
#[cfg(feature = "libsnark")]
pub mod libsnark;
pub mod schemes;
pub mod zexe;

pub mod solidity;

use crate::ir;
use proof_system::schemes::Scheme;
use serde::de::DeserializeOwned;
use serde::Serialize;
use zokrates_field::Field;

pub trait Backend<T: Field, S: Scheme<T>> {
    fn setup(prog: ir::Prog<T>) -> (S::ProvingKey, S::VerificationKey);

    fn generate_proof(
        program: ir::Prog<T>,
        witness: ir::Witness<T>,
        proving_key: S::ProvingKey,
    ) -> Proof<S::ProofPoints>;

    fn verify(vk: S::VerificationKey, proof: Proof<S::ProofPoints>) -> bool;
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
pub struct G2AffineFq(String, String);

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

impl ToString for G2AffineFq {
    fn to_string(&self) -> String {
        format!("{}, {}", self.0, self.1)
    }
}
