use crate::proof_system::scheme::{Scheme, UniversalScheme};
use crate::proof_system::{G1Affine, G2Affine, NotBw6_761Field};
use crate::proof_system::solidity::{SolidityCompatibleScheme, SolidityCompatibleField, solidity_pairing_lib};
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
pub struct VerificationKey<G1, G2> {
    // Fiat-Shamir initial seed
    pub fs_seed: Vec<u8>,
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
    type VerificationKey = VerificationKey<G1Affine, G2Affine>;
    type ProofPoints = ProofPoints<T, G1Affine>;
}

impl<T: Field> UniversalScheme<T> for Marlin {}

impl<T: SolidityCompatibleField + NotBw6_761Field> SolidityCompatibleScheme<T> for Marlin {
    fn export_solidity_verifier(vk: <Marlin as Scheme<T>>::VerificationKey) -> String {
        let (template, solidity_pairing_lib) =
            (String::from(CONTRACT_TEMPLATE), solidity_pairing_lib(false));

        // Replace public parameters in template
        let src = template
            .replace("<%vk_num_variables%>", &vk.num_variables.to_string())
            .replace("<%vk_num_constraints%>", &vk.num_constraints.to_string())
            .replace("<%vk_num_non_zero%>", &vk.num_non_zero.to_string())
            .replace("<%vk_num_instance_variables%>", &vk.num_instance_variables.to_string())
            .replace("<%vk_index_comms_length%>", &vk.index_comms.len().to_string())
            .replace("<%vk_populate_index_comms%>", &{
                let mut populate_index_comms = String::new();
                for (i, (g, _)) in vk.index_comms.iter().enumerate() {
                    populate_index_comms.push_str(&format!("vk.index_comms[{}] = Pairing.G1Point({});", i, &g.to_string()));
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
            .replace("<%vk_max_degree%>", &vk.max_degree.to_string())
            .replace("<%vk_supported_degree%>", &vk.supported_degree.to_string())
            .replace("<%vk_degree_bounds_length%>", &vk.degree_bounds_and_shift_powers.as_ref().unwrap().len().to_string())
            .replace("<%vk_populate_degree_bounds%>", &{
                let mut populate_degree_bounds = String::new();
                for (i, (b, g)) in vk.degree_bounds_and_shift_powers.as_ref().unwrap().iter().enumerate() {
                    populate_degree_bounds.push_str(&format!("vk.degree_bounds[{}] = {};", i, &b.to_string()));
                    populate_degree_bounds.push_str("\n        ");
                    populate_degree_bounds.push_str(&format!("vk.degree_shifted_powers[{}] = Pairing.G1Point({});", i, &g.to_string()));
                    if i < vk.degree_bounds_and_shift_powers.as_ref().unwrap().len() - 1 {
                        populate_degree_bounds.push_str("\n        ");
                    }
                }
                populate_degree_bounds
            })
            .replace("<%fs_init_seed_len%>", &(vk.fs_seed.len() / 32).to_string())
            .replace("<%fs_init_seed_overflow_len%>", &{
                let seed_len_in_32_byte_words = vk.fs_seed.len() / 32;
                let seed_len_overflow_in_bytes = vk.fs_seed.len() - (seed_len_in_32_byte_words * 32);
                seed_len_overflow_in_bytes.to_string()
            })
            .replace("<%fs_populate_init_seed%>", &{
                let mut populate_init_seed = String::new();
                for i in 0..vk.fs_seed.len() / 32 {
                    let word_32_bytes = hex::encode(&vk.fs_seed[i*32..i*32 + 32]);
                    populate_init_seed.push_str(&format!("init_seed[{}] = 0x{};", i, &word_32_bytes));
                    if i < vk.fs_seed.len() / 32 - 1 {
                        populate_init_seed.push_str("\n            ");
                    }
                }
                populate_init_seed
            })
            .replace("<%fs_init_seed_overflow%>", &{
                let seed_len_in_32_byte_words = vk.fs_seed.len() / 32;
                format!("0x{}", hex::encode(&vk.fs_seed[seed_len_in_32_byte_words * 32..]))
            });


        format!(
            "{}{}",
            solidity_pairing_lib, src
        )
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
        // index_info
        uint64 num_variables;
        uint64 num_constraints;
        uint64 num_non_zero;
        uint64 num_instance_variables;
        // index commitments
        Pairing.G1Point[] index_comms;
        // verifier key
        KZGVerifierKey vk;
        uint64 max_degree;
        uint64 supported_degree;
        uint64[] degree_bounds;
        Pairing.G1Point[] degree_shifted_powers;
    }
    struct Proof {
        Pairing.G1Point[] comms_1;
        Pairing.G1Point[] comms_2;
        Pairing.G1Point degree_bound_comms_2_g1;
        Pairing.G1Point[] comms_3;
        Pairing.G1Point degree_bound_comms_3_g2;
        uint256[] evals;
        Pairing.G1Point batch_lc_proof_1;
        uint256 degree_bound_batch_lc_proof_1;
        Pairing.G1Point batch_lc_proof_2;
    }
    function verifierKey() internal pure returns (VerifierKey memory vk) {
        vk.num_variables = <%vk_num_variables%>;
        vk.num_constraints = <%vk_num_constraints%>;
        vk.num_non_zero = <%vk_num_non_zero%>;
        vk.num_instance_variables = <%vk_num_instance_variables%>;
        vk.index_comms = new Pairing.G1Point[](<%vk_index_comms_length%>);
        <%vk_populate_index_comms%>
        vk.vk.g = Pairing.G1Point(<%vk_kzg_g%>);
        vk.vk.gamma_g = Pairing.G1Point(<%vk_kzg_gamma_g%>);
        vk.vk.h = Pairing.G2Point(<%vk_kzg_h%>);
        vk.vk.beta_h = Pairing.G2Point(<%vk_kzg_beta_h%>);
        vk.max_degree = <%vk_max_degree%>;
        vk.supported_degree = <%vk_supported_degree%>;
        vk.degree_bounds = new uint64[](<%vk_degree_bounds_length%>);
        vk.degree_shifted_powers = new Pairing.G1Point[](<%vk_degree_bounds_length%>);
        <%vk_populate_degree_bounds%>
    }
    function verify(uint256[] memory input, Proof memory proof) public view returns (bytes32) {
        uint256 snark_scalar_field = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
        VerifierKey memory vk = verifierKey();
        for (uint i = 0; i < input.length; i++) {
            require(input[i] < snark_scalar_field);
        }
        bytes32 fs_seed;
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
        return fs_seed;
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
}
"#;

#[cfg(test)]
mod tests {
    use crate::flat_absy::{FlatParameter, FlatVariable};
    use crate::ir::{Interpreter, Prog, QuadComb, Statement};
    use crate::proof_system::{UniversalBackend, Backend, Proof, Fr};
    use crate::proof_system::ark::{Ark, parse_fr};
    use zokrates_field::ArkFieldExtensions;

    use super::*;
    use zokrates_field::{Bn128Field};
    use zokrates_solidity_test::{
        contract::Contract,
        evm::Evm,
        address::Address,
        to_be_bytes,
    };
    use rand_0_8::{rngs::StdRng, SeedableRng};
    use ethabi::{Token};
    use primitive_types::U256;


    /// Helper methods for parsing group structure
    pub fn encode_g1_element(g: &G1Affine) -> Token {
        Token::Tuple(vec![
            Token::Uint(U256::from(&hex::decode(&g.0.trim_start_matches("0x")).unwrap()[..])),
            Token::Uint(U256::from(&hex::decode(&g.1.trim_start_matches("0x")).unwrap()[..])),
        ])
    }

    pub fn encode_g2_element(g: &G2Affine) -> Token {

        Token::Tuple(vec![
            Token::FixedArray(vec![
                Token::Uint(U256::from(&hex::decode(&g.0.0.trim_start_matches("0x")).unwrap()[..])),
                Token::Uint(U256::from(&hex::decode(&g.0.1.trim_start_matches("0x")).unwrap()[..])),
            ]),
            Token::FixedArray(vec![
                Token::Uint(U256::from(&hex::decode(&g.1.0.trim_start_matches("0x")).unwrap()[..])),
                Token::Uint(U256::from(&hex::decode(&g.1.1.trim_start_matches("0x")).unwrap()[..])),
            ]),
        ])
    }

    pub fn encode_fr_element(f: &Fr) -> Token {
        Token::Uint(U256::from(&hex::decode(&f.trim_start_matches("0x")).unwrap()[..]))
    }

    fn encode_verify_input(proof: Proof<<Marlin as Scheme<Bn128Field>>::ProofPoints>,) -> Vec<Token> {
        let input = Token::Array(proof.inputs.iter().map(|s| {
            let bytes = hex::decode(s.trim_start_matches("0x")).unwrap();
            debug_assert_eq!(bytes.len(), 32);
            Token::Uint(U256::from(&bytes[..]))
        }).collect::<Vec<_>>());

        let comms_1_token = Token::Array(proof.proof.commitments[0].iter().map(|(c, _)|{
            encode_g1_element(c)
        }).collect::<Vec<_>>());

        let comms_2_token = Token::Array(proof.proof.commitments[1].iter().map(|(c, _)|{
            encode_g1_element(c)
        }).collect::<Vec<_>>());

        let degree_bound_comms_2_g1_token = encode_g1_element(proof.proof.commitments[1][1].1.as_ref().unwrap());

        let comms_3_token = Token::Array(proof.proof.commitments[2].iter().map(|(c, _)|{
            encode_g1_element(c)
        }).collect::<Vec<_>>());

        let degree_bound_comms_3_g2_token = encode_g1_element(proof.proof.commitments[2][0].1.as_ref().unwrap());

        let evals_token = Token::Array(proof.proof.evaluations.into_iter().map(|f| {
            encode_fr_element(&parse_fr::<Bn128Field>(&Bn128Field::into_ark(f)))
        }).collect::<Vec<_>>());

        let pc_lc_opening_1_token = encode_g1_element(&proof.proof.pc_proof_proof[0].0);
        let degree_bound_pc_lc_opening_1_token = encode_fr_element(&parse_fr::<Bn128Field>(&Bn128Field::into_ark(proof.proof.pc_proof_proof[0].1.clone().unwrap())));
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

        let mut src = <Marlin as SolidityCompatibleScheme<Bn128Field>>::export_solidity_verifier(keypair.vk);
        //println!("{}", &src);
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
        let create_result = evm.deploy(contract.encode_create_contract_bytes(&[]).unwrap(), &deployer).unwrap();
        let contract_addr = create_result.addr.clone();
        println!("Contract deploy gas cost: {}", create_result.gas);

        // Call verify function on contract
        let result = evm.call(contract.encode_call_contract_bytes("verify", &encode_verify_input(proof)).unwrap(), &contract_addr, &deployer).unwrap();
        //assert_eq!(&result.out, &to_be_bytes(&U256::from(1)));
        println!("{:?}", result);

    }
}
