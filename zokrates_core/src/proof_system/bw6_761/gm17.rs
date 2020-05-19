use zexe::gm17::{
    prepare_verifying_key, verify_proof, Parameters, PreparedVerifyingKey, Proof as ZexeProof,
    VerifyingKey,
};

use regex::Regex;

use zokrates_field::Field;

use crate::ir;
use crate::proof_system::bn128::utils::zexe::Computation; //curve
use crate::proof_system::bn128::utils::zexe::{
    parse_fr, parse_g1, parse_g1_hex, parse_g2, parse_g2_hex,
};
use crate::proof_system::bn128::utils::parser::parse_vk;
use crate::proof_system::bn128::utils::solidity::{
    SOLIDITY_G2_ADDITION_LIB, SOLIDITY_PAIRING_LIB, SOLIDITY_PAIRING_LIB_V2,
};
use crate::proof_system::{ProofSystem, SetupKeypair}; // SolidityAbi line 21
use proof_system::bn128::{G1PairingPoint, G2PairingPoint, Proof};
use proof_system::SolidityAbi;

pub struct GM17 {}

#[derive(Serialize, Deserialize)]
struct GM17ProofPoints {
    a: G1PairingPoint,
    b: G2PairingPoint,
    c: G1PairingPoint,
}

impl ProofSystem<T> for GM17 {
    fn setup(program: ir::Prog<T>) -> SetupKeypair {
        #[cfg(not(target_arch = "wasm32"))]
        // std::env::set_var("BELLMAN_VERBOSE", "0");

        let parameters = Computation::without_witness(program).setup();
        let vk = serialize_vk::<T>(&parameters.vk);

        let mut pk: Vec<u8> = Vec::new();
        parameters.write(&mut pk).unwrap();

        SetupKeypair::from(vk, pk)
    }

    fn generate_proof(
        program: ir::Prog<T>,
        witness: ir::Witness<T>,
        proving_key: Vec<u8>,
    ) -> String {
        #[cfg(not(target_arch = "wasm32"))]
        // std::env::set_var("BELLMAN_VERBOSE", "0");

        let computation = Computation::with_witness(program, witness);
        let params = Parameters::read(proving_key.as_slice(), true).unwrap();

        let proof = computation.clone().prove(&params);
        let proof_points = GM17ProofPoints::new(
            parse_g1::<T>(&proof.a),
            parse_g2::<T>(&proof.b),
            parse_g1::<T>(&proof.c),
        );

        let inputs = computation
            .public_inputs_values()
            .iter()
            .map(parse_fr::<T>)
            .collect::<Vec<_>>();

        let mut raw: Vec<u8> = Vec::new();
        proof.write(&mut raw).unwrap();

        Proof::<GM17ProofPoints>::new(proof_points, inputs, hex::encode(&raw)).to_json_pretty()
    }

    fn export_solidity_verifier(vk: String, abi: SolidityAbi) -> String {
        let vk_map = parse_vk(vk).unwrap();
        let (mut template_text, solidity_pairing_lib) = match abi {
            SolidityAbi::V1 => (
                String::from(CONTRACT_TEMPLATE),
                String::from(SOLIDITY_PAIRING_LIB),
            ),
            SolidityAbi::V2 => (
                String::from(CONTRACT_TEMPLATE_V2),
                String::from(SOLIDITY_PAIRING_LIB_V2),
            ),
        };

        // replace things in template
        let vk_regex = Regex::new(r#"(<%vk_[^i%]*%>)"#).unwrap();
        let vk_query_len_regex = Regex::new(r#"(<%vk_query_length%>)"#).unwrap();
        let vk_query_repeat_regex = Regex::new(r#"(<%vk_query_pts%>)"#).unwrap();
        let vk_input_len_regex = Regex::new(r#"(<%vk_input_length%>)"#).unwrap();

        let keys = vec![
            "vk.h",
            "vk.g_alpha",
            "vk.h_beta",
            "vk.g_gamma",
            "vk.h_gamma",
        ];

        for key in keys.iter() {
            template_text = vk_regex
                .replace(template_text.as_str(), vk_map.get(*key).unwrap().as_str())
                .into_owned();
        }

        let query_count: usize = vk_map.get("vk.query.len()").unwrap().parse().unwrap();
        template_text = vk_query_len_regex
            .replace(template_text.as_str(), format!("{}", query_count).as_str())
            .into_owned();

        template_text = vk_input_len_regex
            .replace(
                template_text.as_str(),
                format!("{}", query_count - 1).as_str(),
            )
            .into_owned();

        let mut query_repeat_text = String::new();
        for x in 0..query_count {
            query_repeat_text.push_str(
                format!(
                    "vk.query[{}] = Pairing.G1Point({});",
                    x,
                    vk_map
                        .get(format!("vk.query[{}]", x).as_str())
                        .unwrap()
                        .as_str()
                )
                .as_str(),
            );
            if x < query_count - 1 {
                query_repeat_text.push_str("\n        ");
            }
        }

        template_text = vk_query_repeat_regex
            .replace(template_text.as_str(), query_repeat_text.as_str())
            .into_owned();

        let re = Regex::new(r"(?P<v>0[xX][0-9a-fA-F]{64})").unwrap();
        template_text = re.replace_all(&template_text, "uint256($v)").to_string();

        format!(
            "{}{}{}",
            SOLIDITY_G2_ADDITION_LIB, solidity_pairing_lib, template_text
        )
    }

    fn verify(vk: String, proof: String) -> bool {
        let map = parse_vk(vk).unwrap();
        let vk_raw = hex::decode(map.get("vk.raw").unwrap()).unwrap();

        let vk: VerifyingKey<T::BellmanEngine> = VerifyingKey::read(vk_raw.as_slice()).unwrap();
        let pvk: PreparedVerifyingKey<T::BellmanEngine> = prepare_verifying_key(&vk);

        let gm17_proof = Proof::<GM17ProofPoints>::from_str(proof.as_str());

        let raw_proof = hex::decode(gm17_proof.raw).unwrap();
        let proof: BellmanProof<T::BellmanEngine> =
            BellmanProof::read(raw_proof.as_slice()).unwrap();

        let public_inputs: Vec<_> = gm17_proof
            .inputs
            .iter()
            .map(|s| {
                T::try_from_str(s.trim_start_matches("0x"), 16)
                    .expect(format!("Invalid {} value: {}", T::name(), s).as_str())
                    .into_bellman()
            })
            .collect::<Vec<_>>();

        verify_proof(&pvk, &proof, &public_inputs).unwrap()
    }
}

const CONTRACT_TEMPLATE_V2: &str = r#"
contract Verifier {
    using Pairing for *;
    struct VerifyingKey {
        Pairing.G2Point h;
        Pairing.G1Point g_alpha;
        Pairing.G2Point h_beta;
        Pairing.G1Point g_gamma;
        Pairing.G2Point h_gamma;
        Pairing.G1Point[] query;
    }
    struct Proof {
        Pairing.G1Point a;
        Pairing.G2Point b;
        Pairing.G1Point c;
    }
    function verifyingKey() pure internal returns (VerifyingKey memory vk) {
        vk.h= Pairing.G2Point(<%vk_h%>);
        vk.g_alpha = Pairing.G1Point(<%vk_g_alpha%>);
        vk.h_beta = Pairing.G2Point(<%vk_h_beta%>);
        vk.g_gamma = Pairing.G1Point(<%vk_g_gamma%>);
        vk.h_gamma = Pairing.G2Point(<%vk_h_gamma%>);
        vk.query = new Pairing.G1Point[](<%vk_query_length%>);
        <%vk_query_pts%>
    }
    function verify(uint[] memory input, Proof memory proof) internal returns (uint) {
        uint256 snark_scalar_field = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
        VerifyingKey memory vk = verifyingKey();
        require(input.length + 1 == vk.query.length);
        // Compute the linear combination vk_x
        Pairing.G1Point memory vk_x = Pairing.G1Point(0, 0);
        for (uint i = 0; i < input.length; i++) {
            require(input[i] < snark_scalar_field);
            vk_x = Pairing.addition(vk_x, Pairing.scalar_mul(vk.query[i + 1], input[i]));
        }
        vk_x = Pairing.addition(vk_x, vk.query[0]);
        /**
         * e(A*G^{alpha}, B*H^{beta}) = e(G^{alpha}, H^{beta}) * e(G^{psi}, H^{gamma})
         *                              * e(C, H)
         * where psi = \sum_{i=0}^l input_i pvk.query[i]
         */
        if (!Pairing.pairingProd4(vk.g_alpha, vk.h_beta, vk_x, vk.h_gamma, proof.c, vk.h, Pairing.negate(Pairing.addition(proof.a, vk.g_alpha)), Pairing.addition(proof.b, vk.h_beta))) return 1;
        /**
         * e(A, H^{gamma}) = e(G^{gamma}, B)
         */
        if (!Pairing.pairingProd2(proof.a, vk.h_gamma, Pairing.negate(vk.g_gamma), proof.b)) return 2;
        return 0;
    }
    event Verified(string s);
    function verifyTx(
            Proof memory proof,
            uint[<%vk_input_length%>] memory input
        ) public returns (bool r) {
        uint[] memory inputValues = new uint[](input.length);
        for(uint i = 0; i < input.length; i++){
            inputValues[i] = input[i];
        }
        if (verify(inputValues, proof) == 0) {
            emit Verified("Transaction successfully verified.");
            return true;
        } else {
            return false;
        }
    }
}
"#;

const CONTRACT_TEMPLATE: &str = r#"
contract Verifier {
    using Pairing for *;
    struct VerifyingKey {
        Pairing.G2Point h;
        Pairing.G1Point g_alpha;
        Pairing.G2Point h_beta;
        Pairing.G1Point g_gamma;
        Pairing.G2Point h_gamma;
        Pairing.G1Point[] query;
    }
    struct Proof {
        Pairing.G1Point a;
        Pairing.G2Point b;
        Pairing.G1Point c;
    }
    function verifyingKey() pure internal returns (VerifyingKey memory vk) {
        vk.h = Pairing.G2Point(<%vk_h%>);
        vk.g_alpha = Pairing.G1Point(<%vk_g_alpha%>);
        vk.h_beta = Pairing.G2Point(<%vk_h_beta%>);
        vk.g_gamma = Pairing.G1Point(<%vk_g_gamma%>);
        vk.h_gamma = Pairing.G2Point(<%vk_h_gamma%>);
        vk.query = new Pairing.G1Point[](<%vk_query_length%>);
        <%vk_query_pts%>
    }
    function verify(uint[] memory input, Proof memory proof) internal returns (uint) {
        uint256 snark_scalar_field = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
        VerifyingKey memory vk = verifyingKey();
        require(input.length + 1 == vk.query.length);
        // Compute the linear combination vk_x
        Pairing.G1Point memory vk_x = Pairing.G1Point(0, 0);
        for (uint i = 0; i < input.length; i++) {
            require(input[i] < snark_scalar_field);
            vk_x = Pairing.addition(vk_x, Pairing.scalar_mul(vk.query[i + 1], input[i]));
        }
        vk_x = Pairing.addition(vk_x, vk.query[0]);
        /**
         * e(A*G^{alpha}, B*H^{beta}) = e(G^{alpha}, H^{beta}) * e(G^{psi}, H^{gamma})
         *                              * e(C, H)
         * where psi = \sum_{i=0}^l input_i pvk.query[i]
         */
        if (!Pairing.pairingProd4(vk.g_alpha, vk.h_beta, vk_x, vk.h_gamma, proof.c, vk.h, Pairing.negate(Pairing.addition(proof.a, vk.g_alpha)), Pairing.addition(proof.b, vk.h_beta))) return 1;
        /**
         * e(A, H^{gamma}) = e(G^{gamma}, b)
         */
        if (!Pairing.pairingProd2(proof.a, vk.h_gamma, Pairing.negate(vk.g_gamma), proof.b)) return 2;
        return 0;
    }
    event Verified(string s);
    function verifyTx(
            uint[2] memory a,
            uint[2][2] memory b,
            uint[2] memory c,
            uint[<%vk_input_length%>] memory input
        ) public returns (bool r) {
        Proof memory proof;
        proof.a = Pairing.G1Point(a[0], a[1]);
        proof.b = Pairing.G2Point([b[0][0], b[0][1]], [b[1][0], b[1][1]]);
        proof.c = Pairing.G1Point(c[0], c[1]);
        uint[] memory inputValues = new uint[](input.length);
        for(uint i = 0; i < input.length; i++){
            inputValues[i] = input[i];
        }
        if (verify(inputValues, proof) == 0) {
            emit Verified("Transaction successfully verified.");
            return true;
        } else {
            return false;
        }
    }
}
"#;
