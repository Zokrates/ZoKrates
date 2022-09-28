use ark_pallas::Fr as PallasBaseField;

use crate::G2Type;

prime_field!("pallas", PallasBaseField, G2Type::Fq2);
