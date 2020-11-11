use serde::de::DeserializeOwned;
use serde::Serialize;
use zokrates_field::Field;

pub mod gm17;
pub mod groth16;
pub mod pghr13;

pub trait Scheme<T: Field> {
    type VerificationKey: Serialize + DeserializeOwned;
    type ProofPoints: Serialize + DeserializeOwned;
}
