use ark_pallas::Fr as PallasBaseField;
#[cfg(feature = "bellperson_extensions")]
use pasta_curves::Fq;

use crate::{Cycle, G2Type, VestaField};

impl Cycle for FieldPrime {
    type Other = VestaField;
    type Point = pasta_curves::pallas::Point;
}

prime_field!("pallas", PallasBaseField, G2Type::Fq2);

#[cfg(feature = "bellperson_extensions")]
bellperson_extensions!(Fq);
