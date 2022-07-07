use ethabi::Token;
use primitive_types::U256;

use super::{
    Fr, G1Affine, G2Affine, Marlin, SolidityCompatibleField, SolidityCompatibleScheme, G16, GM17,
};

/// Helper methods for parsing group structure
pub fn encode_g1_element(g: &G1Affine) -> (U256, U256) {
    (
        U256::from(&hex::decode(&g.0.trim_start_matches("0x")).unwrap()[..]),
        U256::from(&hex::decode(&g.1.trim_start_matches("0x")).unwrap()[..]),
    )
}

pub fn encode_g2_element(g: &G2Affine) -> ((U256, U256), (U256, U256)) {
    match g {
        G2Affine::Fq2(g) => (
            (
                U256::from(&hex::decode(&g.0 .0.trim_start_matches("0x")).unwrap()[..]),
                U256::from(&hex::decode(&g.0 .1.trim_start_matches("0x")).unwrap()[..]),
            ),
            (
                U256::from(&hex::decode(&g.1 .0.trim_start_matches("0x")).unwrap()[..]),
                U256::from(&hex::decode(&g.1 .1.trim_start_matches("0x")).unwrap()[..]),
            ),
        ),
        _ => unreachable!(),
    }
}

pub fn encode_fr_element(f: &Fr) -> U256 {
    U256::from(&hex::decode(&f.trim_start_matches("0x")).unwrap()[..])
}

pub trait ToToken<T: SolidityCompatibleField>: SolidityCompatibleScheme<T> {
    fn to_token(proof: Self::Proof) -> ethabi::Token;

    fn modify(proof: Self::Proof) -> Self::Proof;
}

impl<T: SolidityCompatibleField> ToToken<T> for G16 {
    fn to_token(proof: Self::Proof) -> Token {
        let a = {
            let (x, y) = encode_g1_element(&proof.a);
            Token::Tuple(vec![Token::Uint(x), Token::Uint(y)])
        };

        let b = {
            let ((x0, y0), (x1, y1)) = encode_g2_element(&proof.b);
            Token::Tuple(vec![
                Token::FixedArray(vec![Token::Uint(x0), Token::Uint(y0)]),
                Token::FixedArray(vec![Token::Uint(x1), Token::Uint(y1)]),
            ])
        };

        let c = {
            let (x, y) = encode_g1_element(&proof.c);
            Token::Tuple(vec![Token::Uint(x), Token::Uint(y)])
        };

        let proof_tokens = vec![a, b, c];

        Token::Tuple(proof_tokens)
    }

    fn modify(mut proof: Self::Proof) -> Self::Proof {
        proof.a.0 = "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into();
        proof
    }
}

impl<T: SolidityCompatibleField> ToToken<T> for GM17 {
    fn to_token(proof: Self::Proof) -> Token {
        let a = {
            let (x, y) = encode_g1_element(&proof.a);
            Token::Tuple(vec![Token::Uint(x), Token::Uint(y)])
        };

        let b = {
            let ((x0, y0), (x1, y1)) = encode_g2_element(&proof.b);
            Token::Tuple(vec![
                Token::FixedArray(vec![Token::Uint(x0), Token::Uint(y0)]),
                Token::FixedArray(vec![Token::Uint(x1), Token::Uint(y1)]),
            ])
        };

        let c = {
            let (x, y) = encode_g1_element(&proof.c);
            Token::Tuple(vec![Token::Uint(x), Token::Uint(y)])
        };

        let proof_tokens = vec![a, b, c];

        Token::Tuple(proof_tokens)
    }

    fn modify(mut proof: Self::Proof) -> Self::Proof {
        proof.a.0 = "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into();
        proof
    }
}

impl<T: SolidityCompatibleField> ToToken<T> for Marlin {
    fn to_token(proof: Self::Proof) -> Token {
        let comms_1_token = Token::Array(
            proof
                .comms_1
                .iter()
                .map(encode_g1_element)
                .map(|(x, y)| Token::Tuple(vec![Token::Uint(x), Token::Uint(y)]))
                .collect(),
        );

        let comms_2_token = Token::Array(
            proof
                .comms_2
                .iter()
                .map(encode_g1_element)
                .map(|(x, y)| Token::Tuple(vec![Token::Uint(x), Token::Uint(y)]))
                .collect(),
        );

        let degree_bound_comms_2_g1_token = {
            let (x, y) = encode_g1_element(&proof.degree_bound_comms_2_g1);
            Token::Tuple(vec![Token::Uint(x), Token::Uint(y)])
        };

        let comms_3_token = Token::Array(
            proof
                .comms_3
                .iter()
                .map(encode_g1_element)
                .map(|(x, y)| Token::Tuple(vec![Token::Uint(x), Token::Uint(y)]))
                .collect(),
        );

        let degree_bound_comms_3_g2_token = {
            let (x, y) = encode_g1_element(&proof.degree_bound_comms_3_g2);
            Token::Tuple(vec![Token::Uint(x), Token::Uint(y)])
        };

        let evals_token = Token::Array(
            proof
                .evals
                .into_iter()
                .map(|f| encode_fr_element(&f))
                .map(Token::Uint)
                .collect::<Vec<_>>(),
        );

        let pc_lc_opening_1_token = {
            let (x, y) = encode_g1_element(&proof.batch_lc_proof_1);
            Token::Tuple(vec![Token::Uint(x), Token::Uint(y)])
        };

        let degree_bound_pc_lc_opening_1_token =
            Token::Uint(encode_fr_element(&proof.batch_lc_proof_1_r));

        let pc_lc_opening_2_token = {
            let (x, y) = encode_g1_element(&proof.batch_lc_proof_2);
            Token::Tuple(vec![Token::Uint(x), Token::Uint(y)])
        };

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
        proof.degree_bound_comms_3_g2.0 =
            "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into();
        proof
    }
}
