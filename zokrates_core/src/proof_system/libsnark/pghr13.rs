use proof_system::libsnark::ffi::{Buffer, ProofResult, SetupResult};
use proof_system::libsnark::{
    prepare_generate_proof, prepare_public_inputs, prepare_setup, Libsnark,
};
use proof_system::{Backend, Proof, SetupKeypair};

use ir::{Prog, Witness};
use proof_system::scheme::pghr13::PGHR13;
use proof_system::scheme::Scheme;
use zokrates_field::Bn128Field;
use zokrates_field::Field;

extern "C" {
    fn pghr13_bn128_setup(
        a: *const u8,
        b: *const u8,
        c: *const u8,
        a_len: i32,
        b_len: i32,
        c_len: i32,
        constraints: i32,
        variables: i32,
        inputs: i32,
    ) -> SetupResult;

    fn pghr13_bn128_generate_proof(
        pk_buf: *mut Buffer,
        public_query_inputs: *const u8,
        public_query_inputs_length: i32,
        private_inputs: *const u8,
        private_inputs_length: i32,
    ) -> ProofResult;

    fn pghr13_bn128_verify(
        vk_buf: *mut Buffer,
        proof_buf: *mut Buffer,
        public_inputs: *const u8,
        public_inputs_length: i32,
    ) -> bool;
}

impl Backend<Bn128Field, PGHR13> for Libsnark {
    fn setup(
        program: Prog<Bn128Field>,
    ) -> SetupKeypair<<PGHR13 as Scheme<Bn128Field>>::VerificationKey> {
        let (a_arr, b_arr, c_arr, a_vec, b_vec, c_vec, num_constraints, num_variables, num_inputs) =
            prepare_setup(program);

        let (vk, pk) = unsafe {
            let result: SetupResult = pghr13_bn128_setup(
                a_arr.as_ptr(),
                b_arr.as_ptr(),
                c_arr.as_ptr(),
                a_vec.len() as i32,
                b_vec.len() as i32,
                c_vec.len() as i32,
                num_constraints as i32,
                num_variables as i32,
                num_inputs as i32,
            );

            let vk: Vec<u8> =
                std::slice::from_raw_parts(result.vk.data, result.vk.length as usize).to_vec();
            let pk: Vec<u8> =
                std::slice::from_raw_parts(result.pk.data, result.pk.length as usize).to_vec();

            // free c allocated buffers
            result.vk.free();
            result.pk.free();

            (vk, pk)
        };

        let vk = serde_json::from_str(String::from_utf8(vk).unwrap().as_str()).unwrap();
        SetupKeypair::new(vk, pk)
    }

    fn generate_proof(
        program: Prog<Bn128Field>,
        witness: Witness<Bn128Field>,
        proving_key: Vec<u8>,
    ) -> Proof<<PGHR13 as Scheme<Bn128Field>>::ProofPoints> {
        let (public_inputs_arr, public_inputs_length, private_inputs_arr, private_inputs_length) =
            prepare_generate_proof(program, witness);

        let proof = unsafe {
            let mut pk_buffer = Buffer::from_vec(&proving_key);

            let result = pghr13_bn128_generate_proof(
                &mut pk_buffer as *mut _,
                public_inputs_arr[0].as_ptr(),
                public_inputs_length as i32,
                private_inputs_arr[0].as_ptr(),
                private_inputs_length as i32,
            );

            pk_buffer.drop(); // drop the buffer manually

            let proof: Vec<u8> =
                std::slice::from_raw_parts(result.proof.data, result.proof.length as usize)
                    .to_vec();

            // free c allocated buffer
            result.proof.free();

            proof
        };

        serde_json::from_str(String::from_utf8(proof).unwrap().as_str()).unwrap()
    }

    fn verify(
        vk: <PGHR13 as Scheme<Bn128Field>>::VerificationKey,
        proof: Proof<<PGHR13 as Scheme<Bn128Field>>::ProofPoints>,
    ) -> bool {
        let vk_raw = hex::decode(vk.raw.unwrap().clone()).unwrap();
        let proof_raw = hex::decode(proof.raw.unwrap().clone()).unwrap();

        let public_inputs: Vec<_> = proof
            .inputs
            .iter()
            .map(|v| Bn128Field::try_from_str(v.as_str().trim_start_matches("0x"), 16).unwrap())
            .collect();

        let (public_inputs_arr, public_inputs_length) = prepare_public_inputs(public_inputs);

        unsafe {
            let mut vk_buffer = Buffer::from_vec(&vk_raw);
            let mut proof_buffer = Buffer::from_vec(&proof_raw);

            let ans = pghr13_bn128_verify(
                &mut vk_buffer as *mut _,
                &mut proof_buffer as *mut _,
                public_inputs_arr[0].as_ptr(),
                public_inputs_length as i32,
            );

            vk_buffer.drop();
            proof_buffer.drop();

            ans
        }
    }
}
