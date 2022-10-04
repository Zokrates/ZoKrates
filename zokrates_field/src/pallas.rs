use ark_pallas::Fr as PallasBaseField;
#[cfg(feature = "bellperson_extensions")]
use pasta_curves::Fq;

#[cfg(feature = "bellperson_extensions")]
use crate::{Cycle, VestaField};

use crate::G2Type;

#[cfg(feature = "bellperson_extensions")]
impl Cycle for FieldPrime {
    type Other = VestaField;
    type Point = pasta_curves::pallas::Point;
}

prime_field!("pallas", PallasBaseField, G2Type::Fq2);

#[cfg(feature = "bellperson_extensions")]
bellperson_extensions!(Fq);
