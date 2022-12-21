use ethabi::Token;

use crate::scheme::Scheme;
use crate::to_token::{encode_fr_element_as_tuple, encode_g1_element, ToToken};
use crate::{Fr, G1Affine, G2Affine, SolidityCompatibleScheme, UniversalScheme};
// use regex::Regex;
use serde::{Deserialize, Serialize};
use zokrates_field::{Bn128Field, Field};

use crate::solidity_renderers::plonk_solidity_renderer::render_verification_key;

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

    // The omega can be computed from n and the generator of Fr and is redundant.
    pub omega: Fr,
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

impl SolidityCompatibleScheme<Bn128Field> for Plonk {
    type Proof = Self::ProofPoints;

    fn export_solidity_verifier(vk: Self::VerificationKey) -> String {
        render_verification_key::<Bn128Field>(&vk)
    }
}

impl ToToken<Bn128Field> for Plonk {
    fn to_token(proof: Self::Proof) -> ethabi::Token {
        let wire_commitments = Token::FixedArray(
            proof
                .wire_commitments
                .iter()
                .map(|x| encode_g1_element(x))
                .collect(),
        );

        let grand_product_commitment = encode_g1_element(&proof.grand_product_commitment);

        let quotient_poly_commitments = Token::FixedArray(
            proof
                .quotient_poly_commitments
                .iter()
                .map(|x| encode_g1_element(x))
                .collect(),
        );

        let wire_values_at_z = Token::FixedArray(
            proof
                .wire_values_at_z
                .iter()
                .map(|x| encode_fr_element_as_tuple(x))
                .collect(),
        );

        let wire_values_at_z_omega = Token::FixedArray(
            proof
                .wire_values_at_z_omega
                .iter()
                .map(|x| encode_fr_element_as_tuple(x))
                .collect(),
        );

        let grand_product_at_z_omega = encode_fr_element_as_tuple(&proof.grand_product_at_z_omega);

        let quotient_polynomial_at_z = encode_fr_element_as_tuple(&proof.quotient_polynomial_at_z);

        let linearization_polynomial_at_z =
            encode_fr_element_as_tuple(&proof.linearization_polynomial_at_z);

        let permutation_polynomials_at_z = Token::FixedArray(
            proof
                .permutation_polynomials_at_z
                .iter()
                .map(|x| encode_fr_element_as_tuple(x))
                .collect(),
        );

        let opening_at_z_proof = encode_g1_element(&proof.opening_at_z_proof);

        let opening_at_z_omega_proof = encode_g1_element(&proof.opening_at_z_omega_proof);

        let proof_tokens = vec![
            wire_commitments,
            grand_product_commitment,
            quotient_poly_commitments,
            wire_values_at_z,
            wire_values_at_z_omega,
            grand_product_at_z_omega,
            quotient_polynomial_at_z,
            linearization_polynomial_at_z,
            permutation_polynomials_at_z,
            opening_at_z_proof,
            opening_at_z_omega_proof,
        ];

        Token::Tuple(proof_tokens)
    }

    fn modify(mut proof: Self::Proof) -> Self::Proof {
        proof.opening_at_z_omega_proof.x =
            "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into();
        proof
    }
}
