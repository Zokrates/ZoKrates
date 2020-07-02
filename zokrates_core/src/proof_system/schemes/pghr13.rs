use proof_system::schemes::Scheme;
use proof_system::solidity::{
    SolidityAbi, SOLIDITY_G2_ADDITION_LIB, SOLIDITY_PAIRING_LIB, SOLIDITY_PAIRING_LIB_V2,
};
use proof_system::{G1Affine, G2Affine};
use regex::Regex;
use zokrates_field::Field;

pub struct PGHR13;

#[derive(Serialize, Deserialize)]
pub struct ProofPoints {
    pub a: G1Affine,
    pub a_p: G1Affine,
    pub b: G2Affine,
    pub b_p: G1Affine,
    pub c: G1Affine,
    pub c_p: G1Affine,
    pub h: G1Affine,
    pub k: G1Affine,
}

#[derive(Serialize, Deserialize)]
pub struct VerificationKey {
    pub a: G2Affine,
    pub b: G1Affine,
    pub c: G2Affine,
    pub gamma: G2Affine,
    pub gamma_beta_1: G1Affine,
    pub gamma_beta_2: G2Affine,
    pub z: G2Affine,
    pub ic: Vec<G1Affine>,
    pub raw: String,
}

impl<T: Field> Scheme<T> for PGHR13 {
    type ProvingKey = Vec<u8>;
    type VerificationKey = VerificationKey;
    type ProofPoints = ProofPoints;

    fn export_solidity_verifier(vk: Self::VerificationKey, abi: SolidityAbi) -> String {
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
        let vk_ic_len_regex = Regex::new(r#"(<%vk_ic_length%>)"#).unwrap();
        let vk_ic_repeat_regex = Regex::new(r#"(<%vk_ic_pts%>)"#).unwrap();
        let vk_input_len_regex = Regex::new(r#"(<%vk_input_length%>)"#).unwrap();

        template_text = vk_regex
            .replace(template_text.as_str(), vk.a.to_string().as_str())
            .into_owned();

        template_text = vk_regex
            .replace(template_text.as_str(), vk.b.to_string().as_str())
            .into_owned();

        template_text = vk_regex
            .replace(template_text.as_str(), vk.c.to_string().as_str())
            .into_owned();

        template_text = vk_regex
            .replace(template_text.as_str(), vk.gamma.to_string().as_str())
            .into_owned();

        template_text = vk_regex
            .replace(template_text.as_str(), vk.gamma_beta_1.to_string().as_str())
            .into_owned();

        template_text = vk_regex
            .replace(template_text.as_str(), vk.gamma_beta_2.to_string().as_str())
            .into_owned();

        template_text = vk_regex
            .replace(template_text.as_str(), vk.z.to_string().as_str())
            .into_owned();

        let ic_count: usize = vk.ic.len();
        template_text = vk_ic_len_regex
            .replace(template_text.as_str(), format!("{}", ic_count).as_str())
            .into_owned();

        template_text = vk_input_len_regex
            .replace(template_text.as_str(), format!("{}", ic_count - 1).as_str())
            .into_owned();

        let mut ic_repeat_text = String::new();
        for (i, g1) in vk.ic.iter().enumerate() {
            ic_repeat_text.push_str(
                format!(
                    "vk.ic[{}] = Pairing.G1Point({});",
                    i,
                    g1.to_string().as_str()
                )
                .as_str(),
            );
            if i < ic_count - 1 {
                ic_repeat_text.push_str("\n        ");
            }
        }

        template_text = vk_ic_repeat_regex
            .replace(template_text.as_str(), ic_repeat_text.as_str())
            .into_owned();

        let re = Regex::new(r"(?P<v>0[xX][0-9a-fA-F]{64})").unwrap();
        template_text = re.replace_all(&template_text, "uint256($v)").to_string();

        format!(
            "{}{}{}",
            SOLIDITY_G2_ADDITION_LIB, solidity_pairing_lib, template_text
        )
    }
}

const CONTRACT_TEMPLATE_V2: &str = r#"contract Verifier {
    using Pairing for *;
    struct VerifyingKey {
        Pairing.G2Point a;
        Pairing.G1Point b;
        Pairing.G2Point c;
        Pairing.G2Point gamma;
        Pairing.G1Point gamma_beta_1;
        Pairing.G2Point gamma_beta_2;
        Pairing.G2Point z;
        Pairing.G1Point[] ic;
    }
    struct Proof {
        Pairing.G1Point a;
        Pairing.G1Point a_p;
        Pairing.G2Point b;
        Pairing.G1Point b_p;
        Pairing.G1Point c;
        Pairing.G1Point c_p;
        Pairing.G1Point k;
        Pairing.G1Point h;
    }
    function verifyingKey() pure internal returns (VerifyingKey memory vk) {
        vk.a = Pairing.G2Point(<%vk_a%>);
        vk.b = Pairing.G1Point(<%vk_b%>);
        vk.c = Pairing.G2Point(<%vk_c%>);
        vk.gamma = Pairing.G2Point(<%vk_g%>);
        vk.gamma_beta_1 = Pairing.G1Point(<%vk_gb1%>);
        vk.gamma_beta_2 = Pairing.G2Point(<%vk_gb2%>);
        vk.z = Pairing.G2Point(<%vk_z%>);
        vk.ic = new Pairing.G1Point[](<%vk_ic_length%>);
        <%vk_ic_pts%>
    }
    function verify(uint[] memory input, Proof memory proof) internal view returns (uint) {
        uint256 snark_scalar_field = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
        VerifyingKey memory vk = verifyingKey();
        require(input.length + 1 == vk.ic.length);
        // Compute the linear combination vk_x
        Pairing.G1Point memory vk_x = Pairing.G1Point(0, 0);
        for (uint i = 0; i < input.length; i++) {
            require(input[i] < snark_scalar_field);
            vk_x = Pairing.addition(vk_x, Pairing.scalar_mul(vk.ic[i + 1], input[i]));
        }
        vk_x = Pairing.addition(vk_x, vk.ic[0]);
        if (!Pairing.pairingProd2(proof.a, vk.a, Pairing.negate(proof.a_p), Pairing.P2())) return 1;
        if (!Pairing.pairingProd2(vk.b, proof.b, Pairing.negate(proof.b_p), Pairing.P2())) return 2;
        if (!Pairing.pairingProd2(proof.c, vk.c, Pairing.negate(proof.c_p), Pairing.P2())) return 3;
        if (!Pairing.pairingProd3(
            proof.k, vk.gamma,
            Pairing.negate(Pairing.addition(vk_x, Pairing.addition(proof.a, proof.c))), vk.gamma_beta_2,
            Pairing.negate(vk.gamma_beta_1), proof.b
        )) return 4;
        if (!Pairing.pairingProd3(
                Pairing.addition(vk_x, proof.a), proof.b,
                Pairing.negate(proof.h), vk.z,
                Pairing.negate(proof.c), Pairing.P2()
        )) return 5;
        return 0;
    }
    function verifyTx(
            Proof memory proof,
            uint[<%vk_input_length%>] memory input
        ) public view returns (bool r) {
        uint[] memory inputValues = new uint[](input.length);
        for(uint i = 0; i < input.length; i++){
            inputValues[i] = input[i];
        }
        if (verify(inputValues, proof) == 0) {
            return true;
        } else {
            return false;
        }
    }
}
"#;

const CONTRACT_TEMPLATE: &str = r#"contract Verifier {
    using Pairing for *;
    struct VerifyingKey {
        Pairing.G2Point a;
        Pairing.G1Point b;
        Pairing.G2Point c;
        Pairing.G2Point gamma;
        Pairing.G1Point gamma_beta_1;
        Pairing.G2Point gamma_beta_2;
        Pairing.G2Point z;
        Pairing.G1Point[] ic;
    }
    struct Proof {
        Pairing.G1Point a;
        Pairing.G1Point a_p;
        Pairing.G2Point b;
        Pairing.G1Point b_p;
        Pairing.G1Point c;
        Pairing.G1Point c_p;
        Pairing.G1Point k;
        Pairing.G1Point h;
    }
    function verifyingKey() pure internal returns (VerifyingKey memory vk) {
        vk.a = Pairing.G2Point(<%vk_a%>);
        vk.b = Pairing.G1Point(<%vk_b%>);
        vk.c = Pairing.G2Point(<%vk_c%>);
        vk.gamma = Pairing.G2Point(<%vk_g%>);
        vk.gamma_beta_1 = Pairing.G1Point(<%vk_gb1%>);
        vk.gamma_beta_2 = Pairing.G2Point(<%vk_gb2%>);
        vk.z = Pairing.G2Point(<%vk_z%>);
        vk.ic = new Pairing.G1Point[](<%vk_ic_length%>);
        <%vk_ic_pts%>
    }
    function verify(uint[] memory input, Proof memory proof) internal view returns (uint) {
        uint256 snark_scalar_field = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
        VerifyingKey memory vk = verifyingKey();
        require(input.length + 1 == vk.ic.length);
        // Compute the linear combination vk_x
        Pairing.G1Point memory vk_x = Pairing.G1Point(0, 0);
        for (uint i = 0; i < input.length; i++) {
            require(input[i] < snark_scalar_field);
            vk_x = Pairing.addition(vk_x, Pairing.scalar_mul(vk.ic[i + 1], input[i]));
        }
        vk_x = Pairing.addition(vk_x, vk.ic[0]);
        if (!Pairing.pairingProd2(proof.a, vk.a, Pairing.negate(proof.a_p), Pairing.P2())) return 1;
        if (!Pairing.pairingProd2(vk.b, proof.b, Pairing.negate(proof.b_p), Pairing.P2())) return 2;
        if (!Pairing.pairingProd2(proof.c, vk.c, Pairing.negate(proof.c_p), Pairing.P2())) return 3;
        if (!Pairing.pairingProd3(
            proof.k, vk.gamma,
            Pairing.negate(Pairing.addition(vk_x, Pairing.addition(proof.a, proof.c))), vk.gamma_beta_2,
            Pairing.negate(vk.gamma_beta_1), proof.b
        )) return 4;
        if (!Pairing.pairingProd3(
                Pairing.addition(vk_x, proof.a), proof.b,
                Pairing.negate(proof.h), vk.z,
                Pairing.negate(proof.c), Pairing.P2()
        )) return 5;
        return 0;
    }
    function verifyTx(
            uint[2] memory a,
            uint[2] memory a_p,
            uint[2][2] memory b,
            uint[2] memory b_p,
            uint[2] memory c,
            uint[2] memory c_p,
            uint[2] memory h,
            uint[2] memory k,
            uint[<%vk_input_length%>] memory input
        ) public view returns (bool r) {
        Proof memory proof;
        proof.a = Pairing.G1Point(a[0], a[1]);
        proof.a_p = Pairing.G1Point(a_p[0], a_p[1]);
        proof.b = Pairing.G2Point([b[0][0], b[0][1]], [b[1][0], b[1][1]]);
        proof.b_p = Pairing.G1Point(b_p[0], b_p[1]);
        proof.c = Pairing.G1Point(c[0], c[1]);
        proof.c_p = Pairing.G1Point(c_p[0], c_p[1]);
        proof.h = Pairing.G1Point(h[0], h[1]);
        proof.k = Pairing.G1Point(k[0], k[1]);
        uint[] memory inputValues = new uint[](input.length);
        for(uint i = 0; i < input.length; i++){
            inputValues[i] = input[i];
        }
        if (verify(inputValues, proof) == 0) {
            return true;
        } else {
            return false;
        }
    }
}
"#;
