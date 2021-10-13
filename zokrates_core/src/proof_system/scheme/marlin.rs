use crate::proof_system::scheme::{Scheme, UniversalScheme};
use crate::proof_system::{G1Affine, G2Affine};
use serde::{Deserialize, Serialize};
use zokrates_field::{ArkFieldExtensions, Field};

#[allow(clippy::upper_case_acronyms)]
pub struct Marlin;

#[derive(Serialize, Deserialize)]
pub struct ProofPoints<Fr, G1> {
    pub commitments: Vec<Vec<G1>>,
    pub evaluations: Vec<Fr>,
    pub pc_proof_proof: Vec<(G1, Option<Fr>)>,
    pub pc_proof_evals: Option<Vec<Fr>>,
    pub prover_messages_count: usize,
}

#[derive(Serialize, Deserialize)]
pub struct KZGVerifierKey<G1, G2> {
    /// The generator of G1.
    pub g: G1,
    /// The generator of G1 that is used for making a commitment hiding.
    pub gamma_g: G1,
    /// The generator of G2.
    pub h: G2,
    /// \beta times the above generator of G2.
    pub beta_h: G2,
    // /// The generator of G2, prepared for use in pairings.
    // #[derivative(Debug = "ignore")]
    // pub prepared_h: E::G2Prepared,
    // /// \beta times the above generator of G2, prepared for use in pairings.
    // #[derivative(Debug = "ignore")]
    // pub prepared_beta_h: E::G2Prepared,
}

#[derive(Serialize, Deserialize)]
pub struct VerificationKey<G1, G2> {
    // index_info
    pub num_variables: usize,
    pub num_constraints: usize,
    pub num_non_zero: usize,
    pub num_instance_variables: usize,
    // index comms
    pub index_comms: Vec<G1>,
    // verifier key
    pub vk: KZGVerifierKey<G1, G2>,
    pub max_degree: usize,
    pub supported_degree: usize,
}

impl<T: Field> Scheme<T> for Marlin {
    type VerificationKey = VerificationKey<G1Affine, G2Affine>;
    type ProofPoints = ProofPoints<T, G1Affine>;
}

impl<T: Field> UniversalScheme<T> for Marlin {}
