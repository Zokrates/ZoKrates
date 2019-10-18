use crate::ir;
use crate::proof_system::bn128::utils::bellman::Computation;
use crate::proof_system::bn128::utils::solidity::{
    SOLIDITY_G2_ADDITION_LIB, SOLIDITY_PAIRING_LIB, SOLIDITY_PAIRING_LIB_V2,
};
use crate::proof_system::ProofSystem;
use bellman::groth16::Parameters;
use regex::Regex;
use std::fs::File;
use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use zokrates_field::Field;

const G16_WARNING: &str = "WARNING: You are using the G16 scheme which is subject to malleability. See zokrates.github.io/reference/proving_schemes.html#g16-malleability for implications.";

pub struct G16 {}
impl<T: Field> ProofSystem<T> for G16 {
    fn setup(program: ir::Prog<T>, pk_path: &str, vk_path: &str) {
        std::env::set_var("BELLMAN_VERBOSE", "0");

        println!("{}", G16_WARNING);

        let parameters = Computation::without_witness(program).setup();
        let parameters_file = File::create(PathBuf::from(pk_path)).unwrap();
        parameters.write(parameters_file).unwrap();
        let mut vk_file = File::create(PathBuf::from(vk_path)).unwrap();
        vk_file
            .write(serialize::serialize_vk::<T>(parameters.vk).as_ref())
            .unwrap();
    }

    fn generate_proof(
        program: ir::Prog<T>,
        witness: ir::Witness<T>,
        pk_path: &str,
        proof_path: &str,
    ) -> bool {
        std::env::set_var("BELLMAN_VERBOSE", "0");

        println!("{}", G16_WARNING);

        let computation = Computation::with_witness(program, witness);
        let parameters_file = File::open(PathBuf::from(pk_path)).unwrap();

        let params = Parameters::read(parameters_file, true).unwrap();

        let proof = computation.clone().prove(&params);

        let mut proof_file = File::create(PathBuf::from(proof_path)).unwrap();
        write!(
            proof_file,
            "{}",
            serialize::serialize_proof::<T>(&proof, &computation.public_inputs_values())
        )
        .unwrap();
        true
    }

    fn export_solidity_verifier(reader: BufReader<File>, is_abiv2: bool) -> String {
        let mut lines = reader.lines();

        let (mut template_text, solidity_pairing_lib) = if is_abiv2 {
            (
                String::from(CONTRACT_TEMPLATE_V2),
                String::from(SOLIDITY_PAIRING_LIB_V2),
            )
        } else {
            (
                String::from(CONTRACT_TEMPLATE),
                String::from(SOLIDITY_PAIRING_LIB),
            )
        };

        let gamma_abc_template = String::from("vk.gamma_abc[index] = Pairing.G1Point(points);"); //copy this for each entry

        //replace things in template
        let vk_regex = Regex::new(r#"(<%vk_[^i%]*%>)"#).unwrap();
        let vk_gamma_abc_len_regex = Regex::new(r#"(<%vk_gamma_abc_length%>)"#).unwrap();
        let vk_gamma_abc_index_regex = Regex::new(r#"index"#).unwrap();
        let vk_gamma_abc_points_regex = Regex::new(r#"points"#).unwrap();
        let vk_gamma_abc_repeat_regex = Regex::new(r#"(<%vk_gamma_abc_pts%>)"#).unwrap();
        let vk_input_len_regex = Regex::new(r#"(<%vk_input_length%>)"#).unwrap();

        for _ in 0..4 {
            let current_line: String = lines
                .next()
                .expect("Unexpected end of file in verification key!")
                .unwrap();
            let current_line_split: Vec<&str> = current_line.split("=").collect();
            assert_eq!(current_line_split.len(), 2);
            template_text = vk_regex
                .replace(template_text.as_str(), current_line_split[1].trim())
                .into_owned();
        }

        let current_line: String = lines
            .next()
            .expect("Unexpected end of file in verification key!")
            .unwrap();
        let current_line_split: Vec<&str> = current_line.split("=").collect();
        assert_eq!(current_line_split.len(), 2);
        let gamma_abc_count: i32 = current_line_split[1].trim().parse().unwrap();

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
            let mut curr_template = gamma_abc_template.clone();
            let current_line: String = lines
                .next()
                .expect("Unexpected end of file in verification key!")
                .unwrap();
            let current_line_split: Vec<&str> = current_line.split("=").collect();
            assert_eq!(current_line_split.len(), 2);
            curr_template = vk_gamma_abc_index_regex
                .replace(curr_template.as_str(), format!("{}", x).as_str())
                .into_owned();
            curr_template = vk_gamma_abc_points_regex
                .replace(curr_template.as_str(), current_line_split[1].trim())
                .into_owned();
            gamma_abc_repeat_text.push_str(curr_template.as_str());
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
}

mod serialize {

    use crate::proof_system::bn128::utils::bellman::{
        parse_fr_json, parse_g1_hex, parse_g1_json, parse_g2_hex, parse_g2_json,
    };
    use bellman::groth16::{Proof, VerifyingKey};
    use bellman::pairing::ff::ScalarEngine;
    use zokrates_field::Field;

    pub fn serialize_vk<T: Field>(vk: VerifyingKey<T::BellmanEngine>) -> String {
        format!(
            "vk.alpha = {}
    vk.beta = {}
    vk.gamma = {}
    vk.delta = {}
    vk.gamma_abc.len() = {}
    {}",
            parse_g1_hex::<T>(&vk.alpha_g1),
            parse_g2_hex::<T>(&vk.beta_g2),
            parse_g2_hex::<T>(&vk.gamma_g2),
            parse_g2_hex::<T>(&vk.delta_g2),
            vk.ic.len(),
            vk.ic
                .iter()
                .enumerate()
                .map(|(i, x)| format!("vk.gamma_abc[{}] = {}", i, parse_g1_hex::<T>(x)))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }

    pub fn serialize_proof<T: Field>(
        p: &Proof<T::BellmanEngine>,
        inputs: &Vec<<T::BellmanEngine as ScalarEngine>::Fr>,
    ) -> String {
        format!(
            "{{
        \"proof\": {{
            \"a\": {},
            \"b\": {},
            \"c\": {}
        }},
        \"inputs\": [{}]
    }}",
            parse_g1_json::<T>(&p.a),
            parse_g2_json::<T>(&p.b),
            parse_g1_json::<T>(&p.c),
            inputs
                .iter()
                .map(parse_fr_json::<T>)
                .collect::<Vec<_>>()
                .join(", "),
        )
    }
}

const CONTRACT_TEMPLATE_V2: &str = r#"
contract Verifier {
    using Pairing for *;
    struct VerifyingKey {
        Pairing.G1Point a;
        Pairing.G2Point b;
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
        vk.a = Pairing.G1Point(<%vk_a%>);
        vk.b = Pairing.G2Point(<%vk_b%>);
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
             Pairing.negate(vk.a), vk.b)) return 1;
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
        Pairing.G1Point a;
        Pairing.G2Point b;
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
        vk.a = Pairing.G1Point(<%vk_a%>);
        vk.b = Pairing.G2Point(<%vk_b%>);
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
             Pairing.negate(vk.a), vk.b)) return 1;
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
    use super::*;
    mod serialize {
        use super::*;

        mod proof {
            use super::*;
            use crate::flat_absy::FlatVariable;
            use crate::ir::*;
            use crate::proof_system::bn128::g16::serialize::serialize_proof;
            use typed_absy::types::{Signature, Type};

            #[allow(dead_code)]
            #[derive(Deserialize)]
            struct G16ProofPoints {
                a: [String; 2],
                b: [[String; 2]; 2],
                c: [String; 2],
            }

            #[allow(dead_code)]
            #[derive(Deserialize)]
            struct G16Proof {
                proof: G16ProofPoints,
                inputs: Vec<String>,
            }

            #[test]
            fn serialize() {
                let program: Prog<Bn128Field> = Prog {
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
                    signature: Signature::new()
                        .inputs(vec![Type::FieldElement])
                        .outputs(vec![Type::FieldElement]),
                };

                let witness = program
                    .clone()
                    .execute(&vec![Bn128Field::from(42)])
                    .unwrap();
                let computation = Computation::with_witness(program, witness);

                let public_inputs_values = computation.public_inputs_values();

                let params = computation.clone().setup();
                let proof = computation.prove(&params);

                let serialized_proof = serialize_proof(&proof, &public_inputs_values);
                serde_json::from_str::<G16Proof>(&serialized_proof).unwrap();
            }
        }
    }
}
