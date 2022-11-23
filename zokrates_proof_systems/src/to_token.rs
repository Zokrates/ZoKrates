use ethabi::Token;
use primitive_types::U256;

use super::{
    Fr, G1Affine, G2Affine, Marlin, Plonk, SolidityCompatibleField, SolidityCompatibleScheme, G16,
    GM17,
};

/// Helper methods for parsing group structure
pub fn encode_g1_element(g: &G1Affine) -> Token {
    let x = U256::from(&hex::decode(&g.x.trim_start_matches("0x")).unwrap()[..]);
    let y = U256::from(&hex::decode(&g.y.trim_start_matches("0x")).unwrap()[..]);

    Token::Tuple(vec![Token::Uint(x), Token::Uint(y)])
}

pub fn encode_g2_element(g: &G2Affine) -> Token {
    let ((x0, y0), (x1, y1)) = match g {
        G2Affine::Fq2(g) => (
            (
                U256::from(&hex::decode(&g.x.0.trim_start_matches("0x")).unwrap()[..]),
                U256::from(&hex::decode(&g.x.1.trim_start_matches("0x")).unwrap()[..]),
            ),
            (
                U256::from(&hex::decode(&g.y.0.trim_start_matches("0x")).unwrap()[..]),
                U256::from(&hex::decode(&g.y.1.trim_start_matches("0x")).unwrap()[..]),
            ),
        ),
        _ => unreachable!(),
    };

    Token::Tuple(vec![
        Token::FixedArray(vec![Token::Uint(x0), Token::Uint(y0)]),
        Token::FixedArray(vec![Token::Uint(x1), Token::Uint(y1)]),
    ])
}

pub fn encode_fr_element(f: &Fr) -> Token {
    Token::Uint(U256::from(
        &hex::decode(&f.trim_start_matches("0x")).unwrap()[..],
    ))
}

pub fn encode_fr_element_as_tuple(f: &Fr) -> Token {
    Token::Tuple(vec![Token::Uint(U256::from(
        &hex::decode(&f.trim_start_matches("0x")).unwrap()[..],
    ))])
}

pub trait ToToken<T: SolidityCompatibleField>: SolidityCompatibleScheme<T> {
    fn to_token(proof: Self::Proof) -> ethabi::Token;

    fn modify(proof: Self::Proof) -> Self::Proof;
}

impl<T: SolidityCompatibleField> ToToken<T> for G16 {
    fn to_token(proof: Self::Proof) -> Token {
        let a = encode_g1_element(&proof.a);

        let b = encode_g2_element(&proof.b);

        let c = encode_g1_element(&proof.c);

        let proof_tokens = vec![a, b, c];

        Token::Tuple(proof_tokens)
    }

    fn modify(mut proof: Self::Proof) -> Self::Proof {
        proof.a.x = "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into();
        proof
    }
}

impl<T: SolidityCompatibleField> ToToken<T> for Plonk {
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
        for t in &proof_tokens {
            println!("{:?}", t);
        }

        Token::Tuple(proof_tokens)
    }

    fn modify(mut proof: Self::Proof) -> Self::Proof {
        proof.opening_at_z_omega_proof.x =
            "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into();
        proof
    }
}

impl<T: SolidityCompatibleField> ToToken<T> for GM17 {
    fn to_token(proof: Self::Proof) -> Token {
        let a = encode_g1_element(&proof.a);

        let b = encode_g2_element(&proof.b);

        let c = encode_g1_element(&proof.c);

        let proof_tokens = vec![a, b, c];

        Token::Tuple(proof_tokens)
    }

    fn modify(mut proof: Self::Proof) -> Self::Proof {
        proof.a.x = "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into();
        proof
    }
}

impl<T: SolidityCompatibleField> ToToken<T> for Marlin {
    fn to_token(proof: Self::Proof) -> Token {
        let comms_1_token = Token::Array(proof.comms_1.iter().map(encode_g1_element).collect());

        let comms_2_token = Token::Array(proof.comms_2.iter().map(encode_g1_element).collect());

        let degree_bound_comms_2_g1_token = encode_g1_element(&proof.degree_bound_comms_2_g1);

        let comms_3_token = Token::Array(proof.comms_3.iter().map(encode_g1_element).collect());

        let degree_bound_comms_3_g2_token = encode_g1_element(&proof.degree_bound_comms_3_g2);

        let evals_token = Token::Array(
            proof
                .evals
                .into_iter()
                .map(|f| encode_fr_element(&f))
                .collect::<Vec<_>>(),
        );

        let pc_lc_opening_1_token = encode_g1_element(&proof.batch_lc_proof_1);

        let degree_bound_pc_lc_opening_1_token = encode_fr_element(&proof.batch_lc_proof_1_r);

        let pc_lc_opening_2_token = encode_g1_element(&proof.batch_lc_proof_2);

        let proof_tokens = vec![
            comms_1_token,
            comms_2_token,
            degree_bound_comms_2_g1_token,
            comms_3_token,
            degree_bound_comms_3_g2_token,
            evals_token,
            pc_lc_opening_1_token,
            degree_bound_pc_lc_opening_1_token,
            pc_lc_opening_2_token,
        ];

        Token::Tuple(proof_tokens)
    }

    fn modify(mut proof: Self::Proof) -> Self::Proof {
        proof.degree_bound_comms_3_g2.x =
            "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into();
        proof
    }
}
