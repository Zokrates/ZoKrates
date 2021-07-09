use crate::proof_system::scheme::{Scheme, UniversalScheme};
use serde::{Deserialize, Serialize};
use zokrates_field::Field;

#[allow(clippy::upper_case_acronyms)]
pub struct Marlin;

#[derive(Serialize, Deserialize)]
pub struct ProofPoints {
    pub raw: Vec<u8>,
}

#[derive(Serialize, Deserialize)]
pub struct VerificationKey {
    pub raw: Vec<u8>,
}

impl<T: Field> Scheme<T> for Marlin {
    type VerificationKey = VerificationKey;
    type ProofPoints = ProofPoints;
}

impl<T: Field> UniversalScheme<T> for Marlin {}
