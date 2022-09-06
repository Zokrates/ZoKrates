use ark_bls12_377::Bls12_377;

use crate::G2Type;

prime_field!("bls12_377", Bls12_377, G2Type::Fq2);

ark_extensions!(Bls12_377);
