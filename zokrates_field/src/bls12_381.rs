use ark_bls12_381::Bls12_381;

prime_field!("bls12_381", Bls12_381);

ark_extensions!(Bls12_381);

#[cfg(feature = "bellman")]
use bellman_ce::pairing::bls12_381::{Bls12, Fq2};
#[cfg(feature = "bellman")]
bellman_extensions!(Bls12, Fq2);
