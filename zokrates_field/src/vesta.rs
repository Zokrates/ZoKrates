use ark_vesta::Fr as VestaBaseField;
#[cfg(feature = "bellperson_extensions")]
use pasta_curves::Fp;

use crate::G2Type;

prime_field!("vesta", VestaBaseField, G2Type::Fq2);

#[cfg(feature = "bellperson_extensions")]
bellperson_extensions!(Fp);
