pub mod to_token;

mod scheme;
mod solidity;
mod tagged;

pub use self::scheme::*;
pub use self::solidity::*;
pub use tagged::{TaggedKeypair, TaggedProof, TaggedVerificationKey};

use zokrates_ast::ir;

use serde::{Deserialize, Serialize};

use rand_0_4::Rng;
use std::io::{Read, Write};

use zokrates_field::Field;

#[derive(Serialize)]
pub struct SetupKeypair<T: Field, S: Scheme<T>> {
    pub vk: S::VerificationKey,
    pub pk: Vec<u8>,
}

impl<T: Field, S: Scheme<T>> SetupKeypair<T, S> {
    pub fn new(vk: S::VerificationKey, pk: Vec<u8>) -> SetupKeypair<T, S> {
        SetupKeypair { vk, pk }
    }
}

#[derive(Serialize, Deserialize)]
pub struct Proof<T: Field, S: Scheme<T>> {
    pub proof: S::ProofPoints,
    pub inputs: Vec<Fr>,
}

impl<T: Field, S: Scheme<T>> Proof<T, S> {
    pub fn new(proof: S::ProofPoints, inputs: Vec<String>) -> Self {
        Proof { proof, inputs }
    }
}

pub type Fr = String;
pub type Fq = String;
pub type Fq2 = (String, String);

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct G1Affine(pub Fq, pub Fq);

#[derive(Serialize, Deserialize, Clone)]
#[serde(untagged)]
pub enum G2Affine {
    Fq2(G2AffineFq2),
    Fq(G2AffineFq),
}

impl ToString for G2Affine {
    fn to_string(&self) -> String {
        match self {
            G2Affine::Fq(e) => e.to_string(),
            G2Affine::Fq2(e) => e.to_string(),
        }
    }
}

// When G2 is defined on Fq2 field
#[derive(Serialize, Deserialize, Clone)]
pub struct G2AffineFq2(pub Fq2, pub Fq2);

// When G2 is defined on a Fq field (BW6_761 curve)
#[derive(Serialize, Deserialize, Clone)]
pub struct G2AffineFq(pub Fq, pub Fq);

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
impl ToString for G2AffineFq2 {
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
    fn generate_proof<I: IntoIterator<Item = ir::Statement<T>>>(
        program: ir::ProgIterator<T, I>,
        witness: ir::Witness<T>,
        proving_key: Vec<u8>,
    ) -> Proof<T, S>;

    fn verify(vk: S::VerificationKey, proof: Proof<T, S>) -> bool;
}
pub trait NonUniversalBackend<T: Field, S: NonUniversalScheme<T>>: Backend<T, S> {
    fn setup<I: IntoIterator<Item = ir::Statement<T>>>(
        program: ir::ProgIterator<T, I>,
    ) -> SetupKeypair<T, S>;
}

pub trait UniversalBackend<T: Field, S: UniversalScheme<T>>: Backend<T, S> {
    fn universal_setup(size: u32) -> Vec<u8>;

    fn setup<I: IntoIterator<Item = ir::Statement<T>>>(
        srs: Vec<u8>,
        program: ir::ProgIterator<T, I>,
    ) -> Result<SetupKeypair<T, S>, String>;
}

pub trait MpcBackend<T: Field, S: Scheme<T>> {
    fn initialize<R: Read, W: Write, I: IntoIterator<Item = ir::Statement<T>>>(
        program: ir::ProgIterator<T, I>,
        phase1_radix: &mut R,
        output: &mut W,
    ) -> Result<(), String>;

    fn contribute<R: Read, W: Write, G: Rng>(
        params: &mut R,
        rng: &mut G,
        output: &mut W,
    ) -> Result<[u8; 64], String>;

    fn verify<P: Read, R: Read, I: IntoIterator<Item = ir::Statement<T>>>(
        params: &mut P,
        program: ir::ProgIterator<T, I>,
        phase1_radix: &mut R,
    ) -> Result<Vec<[u8; 64]>, String>;

    fn export_keypair<R: Read>(params: &mut R) -> Result<SetupKeypair<T, S>, String>;
}
