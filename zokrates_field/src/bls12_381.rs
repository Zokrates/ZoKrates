use ark_bls12_381::Bls12_381;
use ark_ec::PairingEngine;

prime_field!("bls12_381", <Bls12_381 as PairingEngine>::Fr, G2Type::Fq2);

ark_extensions!(Bls12_381);

#[cfg(feature = "bellman_extensions")]
use bellman_ce::pairing::bls12_381::{Bls12, Fq2};

use crate::G2Type;
#[cfg(feature = "bellman_extensions")]
bellman_extensions!(Bls12, Fq2);
