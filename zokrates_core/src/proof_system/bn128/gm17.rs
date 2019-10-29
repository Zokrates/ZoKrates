extern crate libc;

use self::libc::{c_char, c_int, size_t};
use std::{mem};
use ir;
use proof_system::bn128::utils::libsnark::{prepare_generate_proof, prepare_setup};
use proof_system::bn128::utils::solidity::{
    SOLIDITY_G2_ADDITION_LIB, SOLIDITY_PAIRING_LIB, SOLIDITY_PAIRING_LIB_V2,
};
use proof_system::ProofSystem;
use regex::Regex;
use zokrates_field::field::FieldPrime;

pub struct GM17 {}

impl GM17 {
    pub fn new() -> GM17 {
        GM17 {}
    }
}

#[repr(C)]
struct Buffer {
    data: *mut u8,
    size: size_t
}

impl Buffer {
    fn alloc(size: usize) -> Buffer {
        unsafe {
            let mut buf: Vec<u8> = Vec::with_capacity(size);
            let ptr = buf.as_mut_ptr();
            mem::forget(buf);
            Buffer { 
                data: ptr,
                size: size as size_t
            }
        }
    }

    fn from_vec(v: &Vec<u8>) -> Buffer {
        Buffer {
            data: v.as_ptr() as *mut u8,
            size: v.len(),
        }
    }

    fn from_raw_vec(v: &[u8]) -> Buffer {
        Buffer {
            data: v.as_ptr() as *mut u8,
            size: v.len(),
        }
    }

    fn into_vec(self) -> Vec<u8> {
        unsafe { 
            Vec::from_raw_parts(self.data, self.size, self.size)
        }
    }
}

extern "C" {
    fn _gm17_setup(
        A: *const u8,
        B: *const u8,
        C: *const u8,
        A_len: c_int,
        B_len: c_int,
        C_len: c_int,
        constraints: c_int,
        variables: c_int,
        inputs: c_int,
        pk_buf: *mut Buffer,
        vk_buf: *mut Buffer,
    );

    fn _gm17_generate_proof(
        pk_buf: *const Buffer,
        publquery_inputs: *const u8,
        publquery_inputs_length: c_int,
        private_inputs: *const u8,
        private_inputs_length: c_int,
        proof_buf: *mut Buffer
    );
}

impl ProofSystem for GM17 {
    fn setup(&self, program: ir::Prog<FieldPrime>) -> (String, Vec<u8>) {
        let (
            a_arr,
            b_arr,
            c_arr,
            a_vec,
            b_vec,
            c_vec,
            num_constraints,
            num_variables,
            num_inputs
        ) = prepare_setup(program);

        let mut pk_buffer = Buffer::alloc(2048);
        let mut vk_buffer = Buffer::alloc(2048);

        unsafe {
            _gm17_setup(
                a_arr.as_ptr(),
                b_arr.as_ptr(),
                c_arr.as_ptr(),
                a_vec.len() as i32,
                b_vec.len() as i32,
                c_vec.len() as i32,
                num_constraints as i32,
                num_variables as i32,
                num_inputs as i32,
                &mut pk_buffer as *mut _,
                &mut vk_buffer as *mut _
            )
        };

        let vk = unsafe { String::from_raw_parts(vk_buffer.data, vk_buffer.size, vk_buffer.size) };
        let pk = pk_buffer.into_vec();

        (vk, pk)
    }

    fn generate_proof(
        &self,
        program: ir::Prog<FieldPrime>,
        witness: ir::Witness<FieldPrime>,
        proving_key: &[u8],
    ) -> String {
        String::new()
        // let (
        //     public_inputs_arr,
        //     public_inputs_length,
        //     private_inputs_arr,
        //     private_inputs_length,
        // ) = prepare_generate_proof(program, witness);

        // let pk_vec: Vec<u8> = Vec::from(proving_key);
        // let pk_buf = Buffer::from_vec(&pk_vec);

        // let mut proof_buf = Buffer::alloc(4096);
        // unsafe {
        //     _gm17_generate_proof(
        //         &pk_buf as *const _,
        //         public_inputs_arr[0].as_ptr(),
        //         public_inputs_length as c_int,
        //         private_inputs_arr[0].as_ptr(),
        //         private_inputs_length as c_int,
        //         &mut proof_buf as *mut _
        //     );
        //     String::from_raw_parts(proof_buf.data, proof_buf.size, proof_buf.size)
        // }
    }

    fn export_solidity_verifier(&self, vk: String, is_abiv2: bool) -> String {
        let mut lines = vk.lines();

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

        let query_template = String::from("vk.query[index] = Pairing.G1Point(points);"); //copy this for each entry

        //replace things in template
        let vk_regex = Regex::new(r#"(<%vk_[^i%]*%>)"#).unwrap();
        let vk_query_len_regex = Regex::new(r#"(<%vk_query_length%>)"#).unwrap();
        let vk_query_index_regex = Regex::new(r#"index"#).unwrap();
        let vk_query_points_regex = Regex::new(r#"points"#).unwrap();
        let vk_query_repeat_regex = Regex::new(r#"(<%vk_query_pts%>)"#).unwrap();
        let vk_input_len_regex = Regex::new(r#"(<%vk_input_length%>)"#).unwrap();

        for _ in 0..5 {
            let current_line: &str = lines
                .next()
                .expect("Unexpected end of file in verification key!");
            let current_line_split: Vec<&str> = current_line.split("=").collect();
            assert_eq!(current_line_split.len(), 2);
            template_text = vk_regex
                .replace(template_text.as_str(), current_line_split[1].trim())
                .into_owned();
        }

        let current_line: &str = lines
            .next()
            .expect("Unexpected end of file in verification key!");
        let current_line_split: Vec<&str> = current_line.split("=").collect();
        assert_eq!(current_line_split.len(), 2);
        let query_count: i32 = current_line_split[1].trim().parse().unwrap();

        template_text = vk_query_len_regex
            .replace(
                template_text.as_str(), 
                format!("{}", query_count).as_str()
            )
            .into_owned();
        template_text = vk_input_len_regex
            .replace(
                template_text.as_str(),
                format!("{}", query_count - 1).as_str(),
            )
            .into_owned();

        let mut query_repeat_text = String::new();
        for x in 0..query_count {
            let mut curr_template = query_template.clone();
            let current_line: &str = lines
                .next()
                .expect("Unexpected end of file in verification key!");
            let current_line_split: Vec<&str> = current_line.split("=").collect();
            assert_eq!(current_line_split.len(), 2);
            curr_template = vk_query_index_regex
                .replace(curr_template.as_str(), format!("{}", x).as_str())
                .into_owned();
            curr_template = vk_query_points_regex
                .replace(curr_template.as_str(), current_line_split[1].trim())
                .into_owned();
            query_repeat_text.push_str(curr_template.as_str());
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