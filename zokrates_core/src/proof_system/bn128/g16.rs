use bellman::groth16::{
    prepare_verifying_key, verify_proof, Parameters, PreparedVerifyingKey, Proof as BellmanProof,
    VerifyingKey,
};
use bellman::pairing::bn256::{Bn256, Fr};
use regex::Regex;

use zokrates_field::field::{Field, FieldPrime};

use crate::ir;
use crate::proof_system::bn128::utils::bellman::Computation;
use crate::proof_system::bn128::utils::bellman::{
    parse_fr, parse_g1, parse_g1_hex, parse_g2, parse_g2_hex,
};
use crate::proof_system::bn128::utils::parser::parse_vk;
use crate::proof_system::bn128::utils::solidity::{
    SOLIDITY_G2_ADDITION_LIB, SOLIDITY_PAIRING_LIB, SOLIDITY_PAIRING_LIB_V2,
};
use crate::proof_system::{ProofSystem, SetupKeypair};
use proof_system::bn128::{G1PairingPoint, G2PairingPoint, Proof};
use proof_system::{SolidityAbi};

const G16_WARNING: &str = "WARNING: You are using the G16 scheme which is subject to malleability. See zokrates.github.io/reference/proving_schemes.html#g16-malleability for implications.";

pub struct G16 {}

impl G16 {
    pub fn new() -> G16 {
        G16 {}
    }
}

#[derive(Serialize, Deserialize)]
struct G16ProofPoints {
    a: G1PairingPoint,
    b: G2PairingPoint,
    c: G1PairingPoint,
}

impl G16ProofPoints {
    fn new(a: G1PairingPoint, b: G2PairingPoint, c: G1PairingPoint) -> Self {
        G16ProofPoints { a, b, c }
    }
}

impl ProofSystem for G16 {
    fn setup(&self, program: ir::Prog<FieldPrime>) -> SetupKeypair {
        #[cfg(not(target_arch = "wasm32"))]
        std::env::set_var("BELLMAN_VERBOSE", "0");
        println!("{}", G16_WARNING);

        let parameters = Computation::without_witness(program).setup();

        let mut pk: Vec<u8> = Vec::new();
        parameters.write(&mut pk).unwrap();

        SetupKeypair::from(serialize_vk(parameters.vk), pk)
    }

    fn generate_proof(
        &self,
        program: ir::Prog<FieldPrime>,
        witness: ir::Witness<FieldPrime>,
        proving_key: Vec<u8>,
    ) -> String {
        #[cfg(not(target_arch = "wasm32"))]
        std::env::set_var("BELLMAN_VERBOSE", "0");

        println!("{}", G16_WARNING);

        let computation = Computation::with_witness(program, witness);
        let params = Parameters::read(proving_key.as_slice(), true).unwrap();

        let proof = computation.clone().prove(&params);
        let proof_points =
            G16ProofPoints::new(parse_g1(&proof.a), parse_g2(&proof.b), parse_g1(&proof.c));

        let inputs = computation
            .public_inputs_values()
            .iter()
            .map(parse_fr)
            .collect::<Vec<_>>();

        let mut raw: Vec<u8> = Vec::new();
        proof.write(&mut raw).unwrap();

        Proof::<G16ProofPoints>::new(proof_points, inputs, hex::encode(&raw)).to_json_pretty()
    }

    fn export_solidity_verifier(&self, vk: String, abi: SolidityAbi) -> String {
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

        let vk_regex = Regex::new(r#"(<%vk_[^i%]*%>)"#).unwrap();
        let vk_gamma_abc_len_regex = Regex::new(r#"(<%vk_gamma_abc_length%>)"#).unwrap();
        let vk_gamma_abc_repeat_regex = Regex::new(r#"(<%vk_gamma_abc_pts%>)"#).unwrap();
        let vk_input_len_regex = Regex::new(r#"(<%vk_input_length%>)"#).unwrap();

        let keys = vec!["vk.alpha", "vk.beta", "vk.gamma", "vk.delta"];
        for key in keys.iter() {
            template_text = vk_regex
                .replace(template_text.as_str(), vk_map.get(*key).unwrap().as_str())
                .into_owned();
        }

        let gamma_abc_count: usize = vk_map.get("vk.gamma_abc.len()").unwrap().parse().unwrap();
        template_text = vk_gamma_abc_len_regex
            .replace(
                template_text.as_str(),
                format!("{}", gamma_abc_count).as_str(),
            )
            .into_owned();

        template_text = vk_input_len_regex
            .replace(
                template_text.as_str(),
                format!("{}", gamma_abc_count - 1).as_str(),
            )
            .into_owned();

        let mut gamma_abc_repeat_text = String::new();
        for x in 0..gamma_abc_count {
            gamma_abc_repeat_text.push_str(
                format!(
                    "vk.gamma_abc[{}] = Pairing.G1Point({});",
                    x,
                    vk_map
                        .get(format!("vk.gamma_abc[{}]", x).as_str())
                        .unwrap()
                        .as_str()
                )
                .as_str(),
            );
            if x < gamma_abc_count - 1 {
                gamma_abc_repeat_text.push_str("\n        ");
            }
        }

        template_text = vk_gamma_abc_repeat_regex
            .replace(template_text.as_str(), gamma_abc_repeat_text.as_str())
            .into_owned();

        let re = Regex::new(r"(?P<v>0[xX][0-9a-fA-F]{64})").unwrap();
        template_text = re.replace_all(&template_text, "uint256($v)").to_string();

        format!(
            "{}{}{}",
            SOLIDITY_G2_ADDITION_LIB, solidity_pairing_lib, template_text
        )
    }

    fn verify(&self, vk: String, proof: String) -> bool {
        let map = parse_vk(vk).unwrap();
        let vk_raw = hex::decode(map.get("vk.raw").unwrap()).unwrap();

        let vk: VerifyingKey<Bn256> = VerifyingKey::read(vk_raw.as_slice()).unwrap();
        let pvk: PreparedVerifyingKey<Bn256> = prepare_verifying_key(&vk);

        let g16_proof = Proof::<G16ProofPoints>::from_str(proof.as_str());

        let raw_proof = hex::decode(g16_proof.raw).unwrap();
        let proof: BellmanProof<Bn256> = BellmanProof::read(raw_proof.as_slice()).unwrap();

        let public_inputs: Vec<Fr> = g16_proof
            .inputs
            .iter()
            .map(|s| {
                FieldPrime::try_from_str(s.trim_start_matches("0x"), 16)
                    .expect(format!("Invalid field value: {}", s).as_str())
                    .into_bellman()
            })
            .collect::<Vec<_>>();

        verify_proof(&pvk, &proof, &public_inputs).unwrap()
    }
}

fn serialize_vk(vk: VerifyingKey<Bn256>) -> String {
    let mut writer = csv::WriterBuilder::new()
        .delimiter(b'=')
        .from_writer(vec![]);

    writer
        .write_record(&["vk.alpha", parse_g1_hex(&vk.alpha_g1).as_str()])
        .unwrap();
    writer
        .write_record(&["vk.beta", parse_g2_hex(&vk.beta_g2).as_str()])
        .unwrap();
    writer
        .write_record(&["vk.gamma", parse_g2_hex(&vk.gamma_g2).as_str()])
        .unwrap();
    writer
        .write_record(&["vk.delta", parse_g2_hex(&vk.delta_g2).as_str()])
        .unwrap();
    writer
        .write_record(&["vk.gamma_abc.len()", vk.ic.len().to_string().as_str()])
        .unwrap();

    let mut e = vk.ic.iter().enumerate();
    while let Some((i, x)) = e.next() {
        writer
            .write_record(&[
                format!("vk.gamma_abc[{}]", i).as_str(),
                parse_g1_hex(x).as_str(),
            ])
            .unwrap()
    }

    let mut raw: Vec<u8> = Vec::new();
    vk.write(&mut raw).unwrap();

    writer
        .write_record(&["vk.raw", hex::encode(&raw).as_str()])
        .unwrap();

    String::from_utf8(writer.into_inner().unwrap()).unwrap()
}

const CONTRACT_TEMPLATE_V2: &str = r#"
contract Verifier {
    using Pairing for *;
    struct VerifyingKey {
        Pairing.G1Point alpha;
        Pairing.G2Point beta;
        Pairing.G2Point gamma;
        Pairing.G2Point delta;
        Pairing.G1Point[] gamma_abc;
    }
    struct Proof {
        Pairing.G1Point a;
        Pairing.G2Point b;
        Pairing.G1Point c;
    }
    function verifyingKey() pure internal returns (VerifyingKey memory vk) {
        vk.alpha = Pairing.G1Point(<%vk_alpha%>);
        vk.beta = Pairing.G2Point(<%vk_beta%>);
        vk.gamma = Pairing.G2Point(<%vk_gamma%>);
        vk.delta = Pairing.G2Point(<%vk_delta%>);
        vk.gamma_abc = new Pairing.G1Point[](<%vk_gamma_abc_length%>);
        <%vk_gamma_abc_pts%>
    }
    function verify(uint[] memory input, Proof memory proof) internal returns (uint) {
        uint256 snark_scalar_field = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
        VerifyingKey memory vk = verifyingKey();
        require(input.length + 1 == vk.gamma_abc.length);
        // Compute the linear combination vk_x
        Pairing.G1Point memory vk_x = Pairing.G1Point(0, 0);
        for (uint i = 0; i < input.length; i++) {
            require(input[i] < snark_scalar_field);
            vk_x = Pairing.addition(vk_x, Pairing.scalar_mul(vk.gamma_abc[i + 1], input[i]));
        }
        vk_x = Pairing.addition(vk_x, vk.gamma_abc[0]);
        if(!Pairing.pairingProd4(
             proof.a, proof.b,
             Pairing.negate(vk_x), vk.gamma,
             Pairing.negate(proof.c), vk.delta,
             Pairing.negate(vk.alpha), vk.beta)) return 1;
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
        Pairing.G1Point alpha;
        Pairing.G2Point beta;
        Pairing.G2Point gamma;
        Pairing.G2Point delta;
        Pairing.G1Point[] gamma_abc;
    }
    struct Proof {
        Pairing.G1Point a;
        Pairing.G2Point b;
        Pairing.G1Point c;
    }
    function verifyingKey() pure internal returns (VerifyingKey memory vk) {
        vk.alpha = Pairing.G1Point(<%vk_alpha%>);
        vk.beta = Pairing.G2Point(<%vk_beta%>);
        vk.gamma = Pairing.G2Point(<%vk_gamma%>);
        vk.delta = Pairing.G2Point(<%vk_delta%>);
        vk.gamma_abc = new Pairing.G1Point[](<%vk_gamma_abc_length%>);
        <%vk_gamma_abc_pts%>
    }
    function verify(uint[] memory input, Proof memory proof) internal returns (uint) {
        uint256 snark_scalar_field = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
        VerifyingKey memory vk = verifyingKey();
        require(input.length + 1 == vk.gamma_abc.length);
        // Compute the linear combination vk_x
        Pairing.G1Point memory vk_x = Pairing.G1Point(0, 0);
        for (uint i = 0; i < input.length; i++) {
            require(input[i] < snark_scalar_field);
            vk_x = Pairing.addition(vk_x, Pairing.scalar_mul(vk.gamma_abc[i + 1], input[i]));
        }
        vk_x = Pairing.addition(vk_x, vk.gamma_abc[0]);
        if(!Pairing.pairingProd4(
             proof.a, proof.b,
             Pairing.negate(vk_x), vk.gamma,
             Pairing.negate(proof.c), vk.delta,
             Pairing.negate(vk.alpha), vk.beta)) return 1;
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

#[cfg(test)]
mod tests {
    use crate::flat_absy::FlatVariable;
    use crate::ir::{Function, Prog, Statement};

    use super::*;

    #[test]
    fn verify() {
        let program: Prog<FieldPrime> = Prog {
            main: Function {
                id: String::from("main"),
                arguments: vec![FlatVariable::new(0)],
                returns: vec![FlatVariable::public(0)],
                statements: vec![Statement::Constraint(
                    FlatVariable::new(0).into(),
                    FlatVariable::public(0).into(),
                )],
            },
            private: vec![false],
        };

        let g16 = G16 {};
        let keypair = g16.setup(program.clone());

        let witness = program
            .clone()
            .execute(&vec![FieldPrime::from(42)])
            .unwrap();

        let proof = g16.generate_proof(program.clone(), witness, keypair.pk);
        assert!(g16.verify(keypair.vk, proof))
    }
}
