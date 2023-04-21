use ark_bls12_377::Bls12_377;
use ark_ec::PairingEngine;

use crate::G2Type;

prime_field!("bls12_377", <Bls12_377 as PairingEngine>::Fr, G2Type::Fq2);

ark_extensions!(Bls12_377);
