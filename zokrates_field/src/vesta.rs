use ark_vesta::Fr as VestaBaseField;
#[cfg(feature = "bellperson_extensions")]
use pasta_curves::Fp;

use crate::{Cycle, G2Type, PallasField};

impl Cycle for FieldPrime {
    type Other = PallasField;
    type Point = pasta_curves::vesta::Point;
}

prime_field!("vesta", VestaBaseField, G2Type::Fq2);

#[cfg(feature = "bellperson_extensions")]
bellperson_extensions!(Fp);
