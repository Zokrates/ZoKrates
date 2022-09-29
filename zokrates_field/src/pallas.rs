use ark_pallas::Fr as PallasBaseField;
#[cfg(feature = "bellperson_extensions")]
use pasta_curves::Fq;

use crate::G2Type;

prime_field!("pallas", PallasBaseField, G2Type::Fq2);

#[cfg(feature = "bellperson_extensions")]
bellperson_extensions!(Fq);
