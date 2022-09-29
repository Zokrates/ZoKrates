use crate::scheme::Scheme;
use crate::{G1Affine, G2Affine};

use serde::{Deserialize, Serialize};
use zokrates_field::Field;

#[allow(clippy::upper_case_acronyms)]
#[derive(Serialize)]
pub struct Nova;

#[derive(Serialize, Deserialize, Clone)]
pub struct ProofPoints<G1, G2> {
    foo: G1,
    bar: G2,
}

#[derive(Serialize, Deserialize)]
pub struct VerificationKey<G1, G2> {
    foo: G1,
    bar: G2,
}

impl<T: Field> Scheme<T> for Nova {
    const NAME: &'static str = "nova";

    type VerificationKey = VerificationKey<G1Affine, G2Affine>;
    type ProofPoints = ProofPoints<G1Affine, G2Affine>;
}
