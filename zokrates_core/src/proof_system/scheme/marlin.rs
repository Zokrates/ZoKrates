use crate::proof_system::scheme::{Scheme, UniversalScheme};
use crate::proof_system::solidity::{
    solidity_pairing_lib, SolidityCompatibleField, SolidityCompatibleScheme,
};
use crate::proof_system::{Fr, G1Affine, G2Affine, NotBw6_761Field};
use serde::{Deserialize, Serialize};
use zokrates_field::Field;

#[allow(clippy::upper_case_acronyms)]
pub struct Marlin;

#[derive(Serialize, Deserialize)]
pub struct ProofPoints<Fr, G1> {
    pub commitments: Vec<Vec<(G1, Option<G1>)>>,
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
}

#[derive(Serialize, Deserialize)]
pub struct VerificationKey<Fr, G1, G2> {
    // Useful values to precompute for solidity contract
    pub fs_seed: Vec<u8>,
    pub x_root_of_unity: Fr,
    // index_info
    pub num_variables: usize,
    pub num_constraints: usize,
    pub num_non_zero: usize,
    pub num_instance_variables: usize,
    // index comms
    pub index_comms: Vec<(G1, Option<G1>)>,
    // verifier key
    pub vk: KZGVerifierKey<G1, G2>,
    pub max_degree: usize,
    pub supported_degree: usize,
    pub degree_bounds_and_shift_powers: Option<Vec<(usize, G1)>>,
}

impl<T: Field> Scheme<T> for Marlin {
    type VerificationKey = VerificationKey<Fr, G1Affine, G2Affine>;
    type ProofPoints = ProofPoints<T, G1Affine>;
}

impl<T: Field> UniversalScheme<T> for Marlin {}

impl<T: SolidityCompatibleField + NotBw6_761Field> SolidityCompatibleScheme<T> for Marlin {
    fn export_solidity_verifier(vk: <Marlin as Scheme<T>>::VerificationKey) -> String {
        let (template, solidity_pairing_lib) =
            (String::from(CONTRACT_TEMPLATE), solidity_pairing_lib(false));

        // Replace public parameters in template
        let src = template
            .replace(
                "<%vk_index_comms_length%>",
                &vk.index_comms.len().to_string(),
            )
            .replace("<%vk_populate_index_comms%>", &{
                let mut populate_index_comms = String::new();
                for (i, (g, _)) in vk.index_comms.iter().enumerate() {
                    populate_index_comms.push_str(&format!(
                        "vk.index_comms[{}] = Pairing.G1Point({});",
                        i,
                        &g.to_string()
                    ));
                    if i < vk.index_comms.len() - 1 {
                        populate_index_comms.push_str("\n        ");
                    }
                }
                populate_index_comms
            })
            .replace("<%vk_kzg_g%>", &vk.vk.g.to_string())
            .replace("<%vk_kzg_gamma_g%>", &vk.vk.gamma_g.to_string())
            .replace("<%vk_kzg_h%>", &vk.vk.h.to_string())
            .replace("<%vk_kzg_beta_h%>", &vk.vk.beta_h.to_string())
            .replace(
                "<%vk_degree_bounds_length%>",
                &vk.degree_bounds_and_shift_powers
                    .as_ref()
                    .unwrap()
                    .len()
                    .to_string(),
            )
            .replace("<%vk_g1_shift%>", &{
                let h_domain_size = if vk.num_constraints.is_power_of_two() {
                    vk.num_constraints
                } else {
                    vk.num_constraints.next_power_of_two()
                };
                vk.degree_bounds_and_shift_powers
                    .as_ref()
                    .unwrap()
                    .iter()
                    .filter(|(b, _)| *b == h_domain_size - 2)
                    .next()
                    .unwrap()
                    .1
                    .to_string()
            })
            .replace("<%vk_g2_shift%>", &{
                let k_domain_size = if vk.num_non_zero.is_power_of_two() {
                    vk.num_non_zero
                } else {
                    vk.num_non_zero.next_power_of_two()
                };
                vk.degree_bounds_and_shift_powers
                    .as_ref()
                    .unwrap()
                    .iter()
                    .filter(|(b, _)| *b == k_domain_size - 2)
                    .next()
                    .unwrap()
                    .1
                    .to_string()
            })
            .replace("<%fs_init_seed_len%>", &(vk.fs_seed.len() / 32).to_string())
            .replace("<%fs_init_seed_overflow_len%>", &{
                let seed_len_in_32_byte_words = vk.fs_seed.len() / 32;
                let seed_len_overflow_in_bytes =
                    vk.fs_seed.len() - (seed_len_in_32_byte_words * 32);
                seed_len_overflow_in_bytes.to_string()
            })
            .replace("<%fs_populate_init_seed%>", &{
                let mut populate_init_seed = String::new();
                for i in 0..vk.fs_seed.len() / 32 {
                    let word_32_bytes = hex::encode(&vk.fs_seed[i * 32..i * 32 + 32]);
                    populate_init_seed
                        .push_str(&format!("init_seed[{}] = 0x{};", i, &word_32_bytes));
                    if i < vk.fs_seed.len() / 32 - 1 {
                        populate_init_seed.push_str("\n            ");
                    }
                }
                populate_init_seed
            })
            .replace("<%fs_init_seed_overflow%>", &{
                let seed_len_in_32_byte_words = vk.fs_seed.len() / 32;
                format!(
                    "0x{}",
                    hex::encode(&vk.fs_seed[seed_len_in_32_byte_words * 32..])
                )
            })
            .replace("<%h_domain_size%>", &{
                let size = if vk.num_constraints.is_power_of_two() {
                    vk.num_constraints as u64
                } else {
                    vk.num_constraints.next_power_of_two() as u64
                };
                size.to_string()
            })
            .replace("<%k_domain_size%>", &{
                let size = if vk.num_non_zero.is_power_of_two() {
                    vk.num_non_zero as u64
                } else {
                    vk.num_non_zero.next_power_of_two() as u64
                };
                size.to_string()
            })
            .replace("<%x_domain_size%>", &{
                let x = vk.num_instance_variables;
                let size = if x.is_power_of_two() {
                    x as u64
                } else {
                    x.next_power_of_two() as u64
                };
                size.to_string()
            })
            .replace("<%x_root%>", &vk.x_root_of_unity.to_string())
            .replace(
                "<%f_mod%>",
                "0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001",
            )
            .replace(
                "<%f_r%>",
                "0x0e0a77c19a07df2f666ea36f7879462e36fc76959f60cd29ac96341c4ffffffb",
            )
            .replace("<%f_inv%>", "0xc2e1f593efffffff");

        format!("{}{}", solidity_pairing_lib, src)
    }
}

const CONTRACT_TEMPLATE: &str = r#"
contract Verifier {
    using Pairing for *;
    struct KZGVerifierKey {
        Pairing.G1Point g;
        Pairing.G1Point gamma_g;
        Pairing.G2Point h;
        Pairing.G2Point beta_h;
    }
    struct VerifierKey {
        // index commitments
        Pairing.G1Point[] index_comms;
        // verifier key
        KZGVerifierKey vk;
        Pairing.G1Point g1_shift;
        Pairing.G1Point g2_shift;
    }
    struct Proof {
        Pairing.G1Point[] comms_1;
        Pairing.G1Point[] comms_2;
        Pairing.G1Point degree_bound_comms_2_g1;
        Pairing.G1Point[] comms_3;
        Pairing.G1Point degree_bound_comms_3_g2;
        uint256[] evals;
        Pairing.G1Point batch_lc_proof_1;
        uint256 batch_lc_proof_1_r;
        Pairing.G1Point batch_lc_proof_2;
    }
    function verifierKey() internal pure returns (VerifierKey memory vk) {
        vk.index_comms = new Pairing.G1Point[](<%vk_index_comms_length%>);
        <%vk_populate_index_comms%>
        vk.vk.g = Pairing.G1Point(<%vk_kzg_g%>);
        vk.vk.gamma_g = Pairing.G1Point(<%vk_kzg_gamma_g%>);
        vk.vk.h = Pairing.G2Point(<%vk_kzg_h%>);
        vk.vk.beta_h = Pairing.G2Point(<%vk_kzg_beta_h%>);
        vk.g1_shift = Pairing.G1Point(<%vk_g1_shift%>);
        vk.g2_shift = Pairing.G1Point(<%vk_g2_shift%>);
    }
    function verify(uint256[] memory input, Proof memory proof) public view returns (bool) {
        VerifierKey memory vk = verifierKey();
        for (uint i = 0; i < input.length; i++) {
            require(input[i] < <%f_mod%>);
        }
        bytes32 fs_seed;
        uint32 ctr;
        {
            bytes32[<%fs_init_seed_len%>] memory init_seed;
            <%fs_populate_init_seed%>
            bytes<%fs_init_seed_overflow_len%> init_seed_overflow = <%fs_init_seed_overflow%>;
            uint256[] memory input_reverse = new uint256[](input.length);
            for (uint i = 0; i < input.length; i++) {
                input_reverse[i] = be_to_le(input[i]);
            }
            fs_seed = keccak256(abi.encodePacked(init_seed, init_seed_overflow, input_reverse));
        }
        {
            ctr = 0;
            uint8 one = 1;
            uint8 zero = 0;
            uint256[2] memory empty = [0, be_to_le(1)];
            fs_seed = keccak256(abi.encodePacked(
                    abi.encodePacked(
                        be_to_le(proof.comms_1[0].X), be_to_le(proof.comms_1[0].Y), zero,
                        zero,
                        empty, one
                    ),
                    abi.encodePacked(
                        be_to_le(proof.comms_1[1].X), be_to_le(proof.comms_1[1].Y), zero,
                        zero,
                        empty, one
                    ),
                    abi.encodePacked(
                        be_to_le(proof.comms_1[2].X), be_to_le(proof.comms_1[2].Y), zero,
                        zero,
                        empty, one
                    ),
                    abi.encodePacked(
                        be_to_le(proof.comms_1[3].X), be_to_le(proof.comms_1[3].Y), zero,
                        zero,
                        empty, one
                    ),
                    fs_seed
            ));
        }
        uint256[7] memory challenges;
        {
            uint256 f;
            (f, ctr) = sample_field(fs_seed, ctr);
            while (eval_vanishing_poly(f, <%h_domain_size%>) == 0) {
                (f, ctr) = sample_field(fs_seed, ctr);
            }
            challenges[0] = montgomery_reduction(f);
            (f, ctr) = sample_field(fs_seed, ctr);
            challenges[1] = montgomery_reduction(f);
            (f, ctr) = sample_field(fs_seed, ctr);
            challenges[2] = montgomery_reduction(f);
            (f, ctr) = sample_field(fs_seed, ctr);
            challenges[3] = montgomery_reduction(f);
        }
        {
            ctr = 0;
            uint8 one = 1;
            uint8 zero = 0;
            uint256[2] memory empty = [0, be_to_le(1)];
            fs_seed = keccak256(abi.encodePacked(
                    abi.encodePacked(
                        be_to_le(proof.comms_2[0].X), be_to_le(proof.comms_2[0].Y), zero,
                        zero,
                        empty, one
                    ),
                    abi.encodePacked(
                        be_to_le(proof.comms_2[1].X), be_to_le(proof.comms_2[1].Y), zero,
                        one,
                        be_to_le(proof.degree_bound_comms_2_g1.X), be_to_le(proof.degree_bound_comms_2_g1.Y), zero
                    ),
                    abi.encodePacked(
                        be_to_le(proof.comms_2[2].X), be_to_le(proof.comms_2[2].Y), zero,
                        zero,
                        empty, one
                    ),
                    fs_seed
            ));
        }
        {
            uint256 f;
            (f, ctr) = sample_field(fs_seed, ctr);
            while (eval_vanishing_poly(f, <%h_domain_size%>) == 0) {
                (f, ctr) = sample_field(fs_seed, ctr);
            }
            challenges[4] = montgomery_reduction(f);
        }
        {
            ctr = 0;
            uint8 one = 1;
            uint8 zero = 0;
            uint256[2] memory empty = [0, be_to_le(1)];
            fs_seed = keccak256(abi.encodePacked(
                    abi.encodePacked(
                        be_to_le(proof.comms_3[0].X), be_to_le(proof.comms_3[0].Y), zero,
                        one,
                        be_to_le(proof.degree_bound_comms_3_g2.X), be_to_le(proof.degree_bound_comms_3_g2.Y), zero
                    ),
                    abi.encodePacked(
                        be_to_le(proof.comms_3[1].X), be_to_le(proof.comms_3[1].Y), zero,
                        zero,
                        empty, one
                    ),
                    fs_seed
            ));
        }
        {
            uint256 f;
            (f, ctr) = sample_field(fs_seed, ctr);
            challenges[5] = montgomery_reduction(f);
        }
        {
            ctr = 0;
            uint256[] memory evals_reverse = new uint256[](proof.evals.length);
            for (uint i = 0; i < proof.evals.length; i++) {
                evals_reverse[i] = be_to_le(proof.evals[i]);
            }
            fs_seed = keccak256(abi.encodePacked(evals_reverse, fs_seed));
        }
        {
            uint256 f;
            (f, ctr) = sample_field_128(fs_seed, ctr);
            challenges[6] = f;
        }
        Pairing.G1Point[2] memory combined_comm;
        uint256[2] memory combined_eval;
        {
            uint256[6] memory intermediate_evals;

            intermediate_evals[0] = eval_unnormalized_bivariate_lagrange_poly(
                    challenges[0],
                    challenges[4],
                    <%h_domain_size%>
            );
            intermediate_evals[1] = eval_vanishing_poly(challenges[0], <%h_domain_size%>);
            intermediate_evals[2] = eval_vanishing_poly(challenges[4], <%h_domain_size%>);
            intermediate_evals[3] = eval_vanishing_poly(challenges[4], <%x_domain_size%>);

            {
                uint256[<%x_domain_size%>] memory lagrange_coeffs = eval_all_lagrange_coeffs_x_domain(challenges[4]);
                intermediate_evals[4] = lagrange_coeffs[0];
                for (uint i = 1; i < lagrange_coeffs.length; i++) {
                    intermediate_evals[4] = addmod(intermediate_evals[4], mulmod(lagrange_coeffs[i], input[i-1], <%f_mod%>), <%f_mod%>);
                }
            }
            intermediate_evals[5] = eval_vanishing_poly(challenges[5], <%k_domain_size%>);

            {
                // beta commitments: g_1, outer_sc, t, z_b
                uint256[4] memory beta_evals;
                Pairing.G1Point[4] memory beta_commitments;
                beta_evals[0] = proof.evals[0];
                beta_evals[2] = proof.evals[2];
                beta_evals[3] = proof.evals[3];
                beta_commitments[0] = proof.comms_2[1];
                beta_commitments[2] = proof.comms_2[0];
                beta_commitments[3] = proof.comms_1[2];
                {
                    // outer sum check: mask_poly, z_a, 1, w, 1, h_1, 1
                    uint256[7] memory outer_sc_coeffs;
                    outer_sc_coeffs[0] = 1;
                    outer_sc_coeffs[1] = mulmod(intermediate_evals[0], addmod(challenges[1], mulmod(challenges[3], proof.evals[3], <%f_mod%>), <%f_mod%>), <%f_mod%>);
                    outer_sc_coeffs[2] = mulmod(intermediate_evals[0], mulmod(challenges[2], proof.evals[3], <%f_mod%>), <%f_mod%>);
                    outer_sc_coeffs[3] = mulmod(intermediate_evals[3], submod(0, proof.evals[2], <%f_mod%>), <%f_mod%>);
                    outer_sc_coeffs[4] = mulmod(intermediate_evals[4], submod(0, proof.evals[2], <%f_mod%>), <%f_mod%>);
                    outer_sc_coeffs[5] = submod(0, intermediate_evals[2], <%f_mod%>);
                    outer_sc_coeffs[6] = mulmod(proof.evals[0], submod(0, challenges[4], <%f_mod%>), <%f_mod%>);

                    beta_commitments[1] = proof.comms_1[3];
                    beta_commitments[1] = beta_commitments[1].addition(proof.comms_1[1].scalar_mul(outer_sc_coeffs[1]));
                    beta_commitments[1] = beta_commitments[1].addition(proof.comms_1[0].scalar_mul(outer_sc_coeffs[3]));
                    beta_commitments[1] = beta_commitments[1].addition(proof.comms_2[2].scalar_mul(outer_sc_coeffs[5]));
                    beta_evals[1] = submod(beta_evals[1], outer_sc_coeffs[2], <%f_mod%>);
                    beta_evals[1] = submod(beta_evals[1], outer_sc_coeffs[4], <%f_mod%>);
                    beta_evals[1] = submod(beta_evals[1], outer_sc_coeffs[6], <%f_mod%>);
                }
                {
                    combined_comm[0] = beta_commitments[0];
                    combined_eval[0] = beta_evals[0];
                    uint256 beta_opening_challenge = challenges[6];
                    {
                        Pairing.G1Point memory tmp = proof.degree_bound_comms_2_g1.addition(vk.g1_shift.scalar_mul(beta_evals[0]).negate());
                        tmp = tmp.scalar_mul(beta_opening_challenge);
                        combined_comm[0] = combined_comm[0].addition(tmp);
                    }
                    beta_opening_challenge = mulmod(beta_opening_challenge, challenges[6], <%f_mod%>);
                    combined_comm[0] = combined_comm[0].addition(beta_commitments[1].scalar_mul(beta_opening_challenge));
                    combined_eval[0] = addmod(combined_eval[0], mulmod(beta_evals[1], beta_opening_challenge, <%f_mod%>), <%f_mod%>);
                    beta_opening_challenge = mulmod(beta_opening_challenge, challenges[6], <%f_mod%>);
                    combined_comm[0] = combined_comm[0].addition(beta_commitments[2].scalar_mul(beta_opening_challenge));
                    combined_eval[0] = addmod(combined_eval[0], mulmod(beta_evals[2], beta_opening_challenge, <%f_mod%>), <%f_mod%>);
                    beta_opening_challenge = mulmod(beta_opening_challenge, challenges[6], <%f_mod%>);
                    combined_comm[0] = combined_comm[0].addition(beta_commitments[3].scalar_mul(beta_opening_challenge));
                    combined_eval[0] = addmod(combined_eval[0], mulmod(beta_evals[3], beta_opening_challenge, <%f_mod%>), <%f_mod%>);
                }
            }
            {
                // gamma commitments: g_2, inner_sc
                uint256[2] memory gamma_evals;
                Pairing.G1Point[2] memory gamma_commitments;
                gamma_evals[0] = proof.evals[1];
                gamma_commitments[0] = proof.comms_3[0];
                {
                    // inner sum check: a_val, b_val, c_val, 1, row, col, row_col, h_2
                    uint256[8] memory inner_sc_coeffs;
                    {
                        uint256 a_poly_coeff = mulmod(intermediate_evals[1], intermediate_evals[2], <%f_mod%>);
                        inner_sc_coeffs[0] = mulmod(challenges[1], a_poly_coeff, <%f_mod%>);
                        inner_sc_coeffs[1] = mulmod(challenges[2], a_poly_coeff, <%f_mod%>);
                        inner_sc_coeffs[2] = mulmod(challenges[3], a_poly_coeff, <%f_mod%>);
                    }
                    {
                        uint256 b_poly_coeff = mulmod(challenges[5], proof.evals[1], <%f_mod%>);
                        b_poly_coeff = addmod(b_poly_coeff, mulmod(proof.evals[2], inverse(<%k_domain_size%>), <%f_mod%>), <%f_mod%>);
                        inner_sc_coeffs[3] = mulmod(b_poly_coeff, submod(0, mulmod(challenges[4], challenges[0], <%f_mod%>), <%f_mod%>), <%f_mod%>);
                        inner_sc_coeffs[4] = mulmod(b_poly_coeff, challenges[0], <%f_mod%>);
                        inner_sc_coeffs[5] = mulmod(b_poly_coeff, challenges[4], <%f_mod%>);
                        inner_sc_coeffs[6] = submod(0, b_poly_coeff, <%f_mod%>);
                    }
                    inner_sc_coeffs[7] = submod(0, intermediate_evals[5], <%f_mod%>);

                    gamma_commitments[1] = vk.index_comms[2].scalar_mul(inner_sc_coeffs[0]);
                    gamma_commitments[1] = gamma_commitments[1].addition(vk.index_comms[3].scalar_mul(inner_sc_coeffs[1]));
                    gamma_commitments[1] = gamma_commitments[1].addition(vk.index_comms[4].scalar_mul(inner_sc_coeffs[2]));
                    gamma_commitments[1] = gamma_commitments[1].addition(vk.index_comms[0].scalar_mul(inner_sc_coeffs[4]));
                    gamma_commitments[1] = gamma_commitments[1].addition(vk.index_comms[1].scalar_mul(inner_sc_coeffs[5]));
                    gamma_commitments[1] = gamma_commitments[1].addition(vk.index_comms[5].scalar_mul(inner_sc_coeffs[6]));
                    gamma_commitments[1] = gamma_commitments[1].addition(proof.comms_3[1].scalar_mul(inner_sc_coeffs[7]));
                    gamma_evals[1] = submod(0, inner_sc_coeffs[3], <%f_mod%>);
                }
                {
                    combined_comm[1] = gamma_commitments[0];
                    combined_eval[1] = gamma_evals[0];
                    uint256 gamma_opening_challenge = challenges[6];
                    {
                        Pairing.G1Point memory tmp = proof.degree_bound_comms_3_g2.addition(vk.g2_shift.scalar_mul(gamma_evals[0]).negate());
                        tmp = tmp.scalar_mul(gamma_opening_challenge);
                        combined_comm[1] = combined_comm[1].addition(tmp);
                    }
                    gamma_opening_challenge = mulmod(gamma_opening_challenge, challenges[6], <%f_mod%>);
                    combined_comm[1] = combined_comm[1].addition(gamma_commitments[1].scalar_mul(gamma_opening_challenge));
                    combined_eval[1] = addmod(combined_eval[1], mulmod(gamma_evals[1], gamma_opening_challenge, <%f_mod%>), <%f_mod%>);
                }
            }
        }
        // Final pairing check
        uint256 r = uint256(keccak256(abi.encodePacked(combined_comm[0].X, combined_comm[0].Y, combined_comm[1].X, combined_comm[1].Y, fs_seed)));

        Pairing.G1Point memory c_final;
        {
            Pairing.G1Point[2] memory c;
            c[0] = combined_comm[0].addition(proof.batch_lc_proof_1.scalar_mul(challenges[4]));
            c[1] = combined_comm[1].addition(proof.batch_lc_proof_2.scalar_mul(challenges[5]));
            c_final = c[0].addition(c[1].scalar_mul(r));
        }
        Pairing.G1Point memory w_final = proof.batch_lc_proof_1.addition(proof.batch_lc_proof_2.scalar_mul(r));
        uint256 g_mul_final = addmod(combined_eval[0], mulmod(combined_eval[1], r, <%f_mod%>), <%f_mod%>);

        c_final = c_final.addition(vk.vk.g.scalar_mul(g_mul_final).negate());
        c_final = c_final.addition(vk.vk.gamma_g.scalar_mul(proof.batch_lc_proof_1_r).negate());
        bool valid = Pairing.pairingProd2(w_final.negate(), vk.vk.beta_h, c_final, vk.vk.h);
        return valid;
    }
    function be_to_le(uint256 input) internal pure returns (uint256 v) {
        v = input;
        // swap bytes
        v = ((v & 0xFF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00) >> 8) |
            ((v & 0x00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF) << 8);
        // swap 2-byte long pairs
        v = ((v & 0xFFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000) >> 16) |
            ((v & 0x0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF) << 16);
        // swap 4-byte long pairs
        v = ((v & 0xFFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000) >> 32) |
            ((v & 0x00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF) << 32);
        // swap 8-byte long pairs
        v = ((v & 0xFFFFFFFFFFFFFFFF0000000000000000FFFFFFFFFFFFFFFF0000000000000000) >> 64) |
            ((v & 0x0000000000000000FFFFFFFFFFFFFFFF0000000000000000FFFFFFFFFFFFFFFF) << 64);
        // swap 16-byte long pairs
        v = (v >> 128) | (v << 128);
    }
    function sample_field(bytes32 fs_seed, uint32 ctr) internal pure returns (uint256, uint32) {
        // https://github.com/arkworks-rs/algebra/blob/master/ff/src/fields/models/fp/mod.rs#L561
        while (true) {
            uint256 v;
            for (uint i = 0; i < 4; i++) {
                v |= (uint256(keccak256(abi.encodePacked(fs_seed, ctr))) & uint256(0xFFFFFFFFFFFFFFFF)) << ((3-i) * 64);
                ctr += 1;
            }
            v = be_to_le(v);
            v &= (1 << 254) - 1;
            if (v < <%f_mod%>) {
                return (v, ctr);
            }
        }
    }
    function sample_field_128(bytes32 fs_seed, uint32 ctr) internal pure returns (uint256, uint32) {
        // https://github.com/arkworks-rs/algebra/blob/master/ff/src/fields/models/fp/mod.rs#L561
        uint256 v;
        for (uint i = 0; i < 2; i++) {
            v |= (uint256(keccak256(abi.encodePacked(fs_seed, ctr))) & uint256(0xFFFFFFFFFFFFFFFF)) << ((3-i) * 64);
            ctr += 1;
        }
        v = be_to_le(v);
        return (v, ctr);
    }
    function montgomery_reduction(uint256 r) internal pure returns (uint256 v) {
        uint256[4] memory limbs;
        uint256[4] memory mod_limbs;
        for (uint i = 0; i < 4; i++) {
            limbs[i] = (r >> (i * 64)) & uint256(0xFFFFFFFFFFFFFFFF);
            mod_limbs[i] = (<%f_mod%> >> (i * 64)) & uint256(0xFFFFFFFFFFFFFFFF);
        }
        // Montgomery Reduction
        for (uint i = 0; i < 4; i++) {
            uint256 k = mulmod(limbs[i], <%f_inv%>, 1 << 64);
            uint256 carry = 0;
            carry = (limbs[i] + (k * mod_limbs[0]) + carry) >> 64;

            for (uint j = 0; j < 4; j++) {
                uint256 tmp = limbs[(i + j) % 4] + (k * mod_limbs[j]) + carry;
                limbs[(i + j) % 4] = tmp & uint256(0xFFFFFFFFFFFFFFFF);
                carry = tmp >> 64;
            }
            limbs[i % 4] = carry;
        }
        for (uint i = 0; i < 4; i++) {
            v |= (limbs[i] & uint256(0xFFFFFFFFFFFFFFFF)) << (i * 64);
        }
    }
    function submod(uint256 a, uint256 b, uint256 n) internal pure returns (uint256) {
        return addmod(a, n - b, n);
    }
    function expmod(uint256 _base, uint256 _exponent, uint256 _modulus) internal view returns (uint256 retval){
        bool success;
        uint256[1] memory output;
        uint[6] memory input;
        input[0] = 0x20;        // baseLen = new(big.Int).SetBytes(getData(input, 0, 32))
        input[1] = 0x20;        // expLen  = new(big.Int).SetBytes(getData(input, 32, 32))
        input[2] = 0x20;        // modLen  = new(big.Int).SetBytes(getData(input, 64, 32))
        input[3] = _base;
        input[4] = _exponent;
        input[5] = _modulus;
        assembly {
            success := staticcall(sub(gas(), 2000), 5, input, 0xc0, output, 0x20)
        // Use "invalid" to make gas estimation work
            switch success case 0 { invalid() }
        }
        require(success);
        return output[0];
    }
    function inverse(uint256 a) internal view returns (uint256){
        return expmod(a, <%f_mod%> - 2, <%f_mod%>);
    }
    function eval_vanishing_poly(uint256 x, uint256 domain_size) internal view returns (uint256){
        return submod(expmod(x, domain_size, <%f_mod%>), 1, <%f_mod%>);
    }
    function eval_unnormalized_bivariate_lagrange_poly(uint256 x, uint256 y, uint256 domain_size) internal view returns (uint256){
        require(x != y);
        uint256 tmp = submod(eval_vanishing_poly(x, domain_size), eval_vanishing_poly(y, domain_size), <%f_mod%>);
        return mulmod(tmp, inverse(submod(x, y, <%f_mod%>)), <%f_mod%>);
    }
    function eval_all_lagrange_coeffs_x_domain(uint256 x) internal view returns (uint256[<%x_domain_size%>] memory){
        uint256[<%x_domain_size%>] memory coeffs;
        uint256 domain_size = <%x_domain_size%>;
        uint256 root = <%x_root%>;
        uint256 v_at_x = eval_vanishing_poly(x, domain_size);
        uint256 root_inv = inverse(root);
        if (v_at_x == 0) {
            uint256 omega_i = 1;
            for (uint i = 0; i < domain_size; i++) {
                if (omega_i == x) {
                    coeffs[i] = 1;
                    return coeffs;
                }
                omega_i = mulmod(omega_i, root, <%f_mod%>);
            }
        } else {
            uint256 l_i = mulmod(inverse(v_at_x), domain_size, <%f_mod%>);
            uint256 neg_elem = 1;
            for (uint i = 0; i < domain_size; i++) {
                coeffs[i] = mulmod(submod(x, neg_elem, <%f_mod%>), l_i, <%f_mod%>);
                coeffs[i] = inverse(coeffs[i]);
                l_i = mulmod(l_i, root_inv, <%f_mod%>);
                neg_elem = mulmod(neg_elem, root, <%f_mod%>);
            }
            return coeffs;
        }
    }
}
"#;

#[cfg(test)]
mod tests {
    use crate::flat_absy::{FlatParameter, FlatVariable};
    use crate::ir::{Interpreter, Prog, QuadComb, Statement};
    use crate::proof_system::ark::{parse_fr, Ark};
    use crate::proof_system::{Backend, Fr, Proof, UniversalBackend};
    use zokrates_field::ArkFieldExtensions;

    use super::*;
    use ethabi::Token;
    use primitive_types::U256;
    use rand_0_8::{rngs::StdRng, SeedableRng};
    use zokrates_field::Bn128Field;
    use zokrates_solidity_test::{address::Address, contract::Contract, evm::Evm, to_be_bytes};

    /// Helper methods for parsing group structure
    pub fn encode_g1_element(g: &G1Affine) -> Token {
        Token::Tuple(vec![
            Token::Uint(U256::from(
                &hex::decode(&g.0.trim_start_matches("0x")).unwrap()[..],
            )),
            Token::Uint(U256::from(
                &hex::decode(&g.1.trim_start_matches("0x")).unwrap()[..],
            )),
        ])
    }

    //pub fn encode_g2_element(g: &G2Affine) -> Token {
    //    Token::Tuple(vec![
    //        Token::FixedArray(vec![
    //            Token::Uint(U256::from(&hex::decode(&g.0.0.trim_start_matches("0x")).unwrap()[..])),
    //            Token::Uint(U256::from(&hex::decode(&g.0.1.trim_start_matches("0x")).unwrap()[..])),
    //        ]),
    //        Token::FixedArray(vec![
    //            Token::Uint(U256::from(&hex::decode(&g.1.0.trim_start_matches("0x")).unwrap()[..])),
    //            Token::Uint(U256::from(&hex::decode(&g.1.1.trim_start_matches("0x")).unwrap()[..])),
    //        ]),
    //    ])
    //}

    pub fn encode_fr_element(f: &Fr) -> Token {
        Token::Uint(U256::from(
            &hex::decode(&f.trim_start_matches("0x")).unwrap()[..],
        ))
    }

    fn encode_verify_input(
        proof: Proof<<Marlin as Scheme<Bn128Field>>::ProofPoints>,
    ) -> Vec<Token> {
        let input = Token::Array(
            proof
                .inputs
                .iter()
                .map(|s| {
                    let bytes = hex::decode(s.trim_start_matches("0x")).unwrap();
                    debug_assert_eq!(bytes.len(), 32);
                    Token::Uint(U256::from(&bytes[..]))
                })
                .collect::<Vec<_>>(),
        );

        let comms_1_token = Token::Array(
            proof.proof.commitments[0]
                .iter()
                .map(|(c, _)| encode_g1_element(c))
                .collect::<Vec<_>>(),
        );

        let comms_2_token = Token::Array(
            proof.proof.commitments[1]
                .iter()
                .map(|(c, _)| encode_g1_element(c))
                .collect::<Vec<_>>(),
        );

        let degree_bound_comms_2_g1_token =
            encode_g1_element(proof.proof.commitments[1][1].1.as_ref().unwrap());

        let comms_3_token = Token::Array(
            proof.proof.commitments[2]
                .iter()
                .map(|(c, _)| encode_g1_element(c))
                .collect::<Vec<_>>(),
        );

        let degree_bound_comms_3_g2_token =
            encode_g1_element(proof.proof.commitments[2][0].1.as_ref().unwrap());

        let evals_token = Token::Array(
            proof
                .proof
                .evaluations
                .into_iter()
                .map(|f| encode_fr_element(&parse_fr::<Bn128Field>(&Bn128Field::into_ark(f))))
                .collect::<Vec<_>>(),
        );

        let pc_lc_opening_1_token = encode_g1_element(&proof.proof.pc_proof_proof[0].0);
        let degree_bound_pc_lc_opening_1_token = encode_fr_element(&parse_fr::<Bn128Field>(
            &Bn128Field::into_ark(proof.proof.pc_proof_proof[0].1.clone().unwrap()),
        ));
        let pc_lc_opening_2_token = encode_g1_element(&proof.proof.pc_proof_proof[1].0);

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

        vec![input, Token::Tuple(proof_tokens)]
    }

    #[test]
    fn verify_solidity_bn128() {
        let program: Prog<Bn128Field> = Prog {
            arguments: vec![FlatParameter::private(FlatVariable::new(0))],
            return_count: 1,
            statements: vec![
                Statement::constraint(
                    QuadComb::from_linear_combinations(
                        FlatVariable::new(0).into(),
                        FlatVariable::new(0).into(),
                    ),
                    FlatVariable::new(1),
                ),
                Statement::constraint(FlatVariable::new(1), FlatVariable::public(0)),
            ],
        };

        let srs = <Ark as UniversalBackend<Bn128Field, Marlin>>::universal_setup(5);
        let keypair =
            <Ark as UniversalBackend<Bn128Field, Marlin>>::setup(srs, program.clone().into())
                .unwrap();
        let interpreter = Interpreter::default();

        let witness = interpreter
            .execute(program.clone(), &[Bn128Field::from(42)])
            .unwrap();

        let proof = <Ark as Backend<Bn128Field, Marlin>>::generate_proof(
            program.clone(),
            witness,
            keypair.pk,
        );

        //let ans = <Ark as Backend<Bn128Field, Marlin>>::verify(keypair.vk, proof);
        //assert!(ans);

        let mut src =
            <Marlin as SolidityCompatibleScheme<Bn128Field>>::export_solidity_verifier(keypair.vk);
        src = src.replace("\"", "\\\"");

        let solc_config = r#"
            {
                "language": "Solidity",
                "sources": {
                    "input.sol": { "content": "<%src%>" }
                },
                "settings": {
                    "optimizer": { "enabled": <%opt%> },
                    "outputSelection": {
                        "*": {
                            "*": [
                                "evm.bytecode.object", "abi"
                            ],
                        "": [ "*" ] } }
                }
            }"#
        .replace("<%opt%>", &true.to_string())
        .replace("<%src%>", &src);

        let contract = Contract::compile_from_config(&solc_config, "Verifier").unwrap();

        // Setup EVM
        let mut rng = StdRng::seed_from_u64(0u64);
        let mut evm = Evm::new();
        let deployer = Address::random(&mut rng);
        evm.create_account(&deployer, 0);

        // Deploy contract
        let create_result = evm
            .deploy(
                contract.encode_create_contract_bytes(&[]).unwrap(),
                &deployer,
            )
            .unwrap();
        let contract_addr = create_result.addr.clone();
        //println!("Contract deploy gas cost: {}", create_result.gas);

        // Call verify function on contract
        let result = evm
            .call(
                contract
                    .encode_call_contract_bytes("verify", &encode_verify_input(proof))
                    .unwrap(),
                &contract_addr,
                &deployer,
            )
            .unwrap();
        assert_eq!(&result.out, &to_be_bytes(&U256::from(1)));
        //println!("{:?}", result);
    }
}
