use std::fs::read_to_string;

use crate::scheme::{NonUniversalScheme, Scheme};
use crate::solidity::solidity_pairing_lib;
use crate::{
    Fr, G1Affine, G2Affine, SolidityCompatibleField, SolidityCompatibleScheme, UniversalScheme,
};
use regex::Regex;
use serde::{Deserialize, Serialize};
use zokrates_field::Field;

#[derive(Serialize, Debug, Clone, PartialEq)]
pub struct Plonk;

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq)]
pub struct VerificationKey<G1, G2> {
    pub n: u32,
    pub num_inputs: u32,
    pub selector_commitments: Vec<G1>,
    pub next_step_selector_commitments: Vec<G1>,
    pub permutation_commitments: Vec<G1>,
    pub non_residues: Vec<Fr>,
    pub g2_elements: [G2; 2],
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq)]
pub struct ProofPoints<G1> {
    pub num_inputs: u32,
    pub n: u32,
    pub wire_commitments: Vec<G1>,
    pub grand_product_commitment: G1,
    pub quotient_poly_commitments: Vec<G1>,
    pub wire_values_at_z: Vec<Fr>,
    pub wire_values_at_z_omega: Vec<Fr>,
    pub grand_product_at_z_omega: Fr,
    pub quotient_polynomial_at_z: Fr,
    pub linearization_polynomial_at_z: Fr,
    pub permutation_polynomials_at_z: Vec<Fr>,
    pub opening_at_z_proof: G1,
    pub opening_at_z_omega_proof: G1,
}

impl<T: Field> Scheme<T> for Plonk {
    const NAME: &'static str = "plonk";

    type VerificationKey = VerificationKey<G1Affine, G2Affine>;
    type ProofPoints = ProofPoints<G1Affine>;
}

impl<T: Field> UniversalScheme<T> for Plonk {}

impl<T: SolidityCompatibleField> SolidityCompatibleScheme<T> for Plonk {
    type Proof = Self::ProofPoints;

    fn export_solidity_verifier(vk: Self::VerificationKey) -> String {
        // TODO: Do this to compile the template into the binary
        // String::from(include_str!("../../solidity_templates/PlonkVerifier.sol"))
        read_to_string("/Users/georg/coding/zoKrates-georg/zokrates_proof_systems/solidity_templates/PlonkVerifier.sol").unwrap()
    }
}
