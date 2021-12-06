#[cfg(feature = "ark")]
pub mod ark;
#[cfg(feature = "bellman")]
pub mod bellman;
#[cfg(feature = "libsnark")]
pub mod libsnark;

mod scheme;
mod solidity;

pub use self::scheme::*;
pub use self::solidity::*;

use crate::ir;
use rand_0_4::Rng;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use std::io::{Read, Write};
use zokrates_field::{BellmanFieldExtensions, Field};

#[derive(Serialize)]
pub struct SetupKeypair<V> {
    pub vk: V,
    pub pk: Vec<u8>,
}

impl<V: Serialize + DeserializeOwned> SetupKeypair<V> {
    pub fn new(vk: V, pk: Vec<u8>) -> SetupKeypair<V> {
        SetupKeypair { vk, pk }
    }
}

#[derive(Serialize, Deserialize)]
pub struct Proof<T> {
    pub proof: T,
    pub inputs: Vec<String>,
}

#[allow(dead_code)]
impl<T: Serialize + DeserializeOwned> Proof<T> {
    fn new(proof: T, inputs: Vec<String>) -> Self {
        Proof { proof, inputs }
    }
}

pub type Fr = String;
pub type Fq = String;
pub type Fq2 = (String, String);

#[derive(Serialize, Deserialize)]
pub struct G1Affine(Fq, Fq);

// When G2 is defined on Fq2 field
#[derive(Serialize, Deserialize)]
pub struct G2Affine(Fq2, Fq2);

// When G2 is defined on a Fq field (BW6_761 curve)
#[derive(Serialize, Deserialize)]
pub struct G2AffineFq(Fq, Fq);

impl ToString for G1Affine {
    fn to_string(&self) -> String {
        format!("{}, {}", self.0, self.1)
    }
}

impl ToString for G2AffineFq {
    fn to_string(&self) -> String {
        format!("{}, {}", self.0, self.1)
    }
}
impl ToString for G2Affine {
    fn to_string(&self) -> String {
        format!(
            "[{}, {}], [{}, {}]",
            (self.0).0,
            (self.0).1,
            (self.1).0,
            (self.1).1
        )
    }
}

pub trait Backend<T: Field, S: Scheme<T>> {
    fn generate_proof(
        program: ir::Prog<T>,
        witness: ir::Witness<T>,
        proving_key: Vec<u8>,
    ) -> Proof<S::ProofPoints>;

    fn verify(vk: S::VerificationKey, proof: Proof<S::ProofPoints>) -> bool;
}
pub trait NonUniversalBackend<T: Field, S: NonUniversalScheme<T>>: Backend<T, S> {
    fn setup(program: ir::Prog<T>) -> SetupKeypair<S::VerificationKey>;
}

pub trait UniversalBackend<T: Field, S: UniversalScheme<T>>: Backend<T, S> {
    fn universal_setup(size: u32) -> Vec<u8>;

    fn setup(
        srs: Vec<u8>,
        program: ir::Prog<T>,
    ) -> Result<SetupKeypair<S::VerificationKey>, String>;
}

#[cfg(feature = "bellman")]
pub trait MpcBackend<T: Field + BellmanFieldExtensions, S: Scheme<T>> {
    fn initialize<R: Read, W: Write>(
        program: ir::Prog<T>,
        phase1_radix: &mut R,
        output: &mut W,
    ) -> Result<(), String>;

    fn contribute<R: Read, W: Write, G: Rng>(
        params: &mut R,
        rng: &mut G,
        output: &mut W,
    ) -> Result<[u8; 64], String>;

    fn verify<R: Read>(
        params: &mut R,
        program: ir::Prog<T>,
        phase1_radix: &mut R,
    ) -> Result<Vec<[u8; 64]>, String>;

    fn export_keypair<R: Read>(params: &mut R) -> Result<SetupKeypair<S::VerificationKey>, String>;
}
