use crate::ir::{Prog, Witness};
use crate::proof_system::gm17::{ProofPoints, VerificationKey, GM17};
use crate::proof_system::libsnark::ffi::{Buffer, ProofResult, SetupResult};
use crate::proof_system::libsnark::{
    prepare_generate_proof, prepare_public_inputs, prepare_setup, serialization::*, Libsnark,
};
use crate::proof_system::Scheme;
use crate::proof_system::{Backend, G1Affine, G2Affine, Proof, SetupKeypair};
use std::io::{BufReader, BufWriter, Write};
use zokrates_field::{Bn128Field, Field};

extern "C" {
    fn gm17_bn128_setup(
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

    fn gm17_bn128_generate_proof(
        pk_buf: *mut Buffer,
        public_query_inputs: *const u8,
        public_query_inputs_length: i32,
        private_inputs: *const u8,
        private_inputs_length: i32,
    ) -> ProofResult;

    fn gm17_bn128_verify(
        vk_buf: *mut Buffer,
        proof_buf: *mut Buffer,
        public_inputs: *const u8,
        public_inputs_length: i32,
    ) -> bool;
}

impl Backend<Bn128Field, GM17> for Libsnark {
    fn setup(
        program: Prog<Bn128Field>,
    ) -> SetupKeypair<<GM17 as Scheme<Bn128Field>>::VerificationKey> {
        let (a_arr, b_arr, c_arr, a_vec, b_vec, c_vec, num_constraints, num_variables, num_inputs) =
            prepare_setup(program);

        let (vk, pk) = unsafe {
            let result: SetupResult = gm17_bn128_setup(
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

        let vk_slice = vk.as_slice();
        let mut reader = BufReader::new(vk_slice);

        let h = read_g2(&mut reader).unwrap();
        let g_alpha = read_g1(&mut reader).unwrap();
        let h_beta = read_g2(&mut reader).unwrap();
        let g_gamma = read_g1(&mut reader).unwrap();
        let h_gamma = read_g2(&mut reader).unwrap();

        let mut query = vec![];
        while let Ok(q) = read_g1(&mut reader) {
            query.push(q);
        }

        let vk = VerificationKey::<G1Affine, G2Affine> {
            h,
            g_alpha,
            h_beta,
            g_gamma,
            h_gamma,
            query,
        };

        SetupKeypair::new(vk, pk)
    }

    fn generate_proof(
        program: Prog<Bn128Field>,
        witness: Witness<Bn128Field>,
        proving_key: Vec<u8>,
    ) -> Proof<<GM17 as Scheme<Bn128Field>>::ProofPoints> {
        let (public_inputs_arr, public_inputs_length, private_inputs_arr, private_inputs_length) =
            prepare_generate_proof(program.clone(), witness.clone());

        let proof = unsafe {
            let mut pk_buffer = Buffer::from_vec(&proving_key);

            let result = gm17_bn128_generate_proof(
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

        let mut reader = BufReader::new(proof.as_slice());
        let a = read_g1(&mut reader).unwrap();
        let b = read_g2(&mut reader).unwrap();
        let c = read_g1(&mut reader).unwrap();

        let points = ProofPoints::<G1Affine, G2Affine> { a, b, c };
        let public_inputs: Vec<String> = program
            .public_inputs(&witness)
            .iter()
            .map(|f| format!("0x{:064x}", f.to_biguint()))
            .collect();

        Proof::new(points, public_inputs)
    }

    fn verify(
        vk: <GM17 as Scheme<Bn128Field>>::VerificationKey,
        proof: Proof<<GM17 as Scheme<Bn128Field>>::ProofPoints>,
    ) -> bool {
        let vk_buffer = vec![];
        let mut vk_writer = BufWriter::new(vk_buffer);

        write_g2(&mut vk_writer, &vk.h);
        write_g1(&mut vk_writer, &vk.g_alpha);
        write_g2(&mut vk_writer, &vk.h_beta);
        write_g1(&mut vk_writer, &vk.g_gamma);
        write_g2(&mut vk_writer, &vk.h_gamma);

        vk.query.iter().for_each(|q| write_g1(&mut vk_writer, q));

        vk_writer.flush().unwrap();

        let proof_buffer = vec![];
        let mut proof_writer = BufWriter::new(proof_buffer);

        write_g1(&mut proof_writer, &proof.proof.a);
        write_g2(&mut proof_writer, &proof.proof.b);
        write_g1(&mut proof_writer, &proof.proof.c);
        proof_writer.flush().unwrap();

        let public_inputs: Vec<_> = proof
            .inputs
            .iter()
            .map(|v| Bn128Field::try_from_str(v.as_str().trim_start_matches("0x"), 16).unwrap())
            .collect();

        let (public_inputs_arr, public_inputs_length) = prepare_public_inputs(public_inputs);

        unsafe {
            let mut vk_buffer = Buffer::from_vec(vk_writer.get_ref());
            let mut proof_buffer = Buffer::from_vec(proof_writer.get_ref());

            let ans = gm17_bn128_verify(
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

#[cfg(feature = "libsnark")]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::flat_absy::FlatVariable;
    use crate::ir::{Function, Interpreter, Prog, Statement};
    use zokrates_field::Bn128Field;

    #[test]
    fn verify() {
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
            private: vec![true],
        };

        let keypair = <Libsnark as Backend<Bn128Field, GM17>>::setup(program.clone());
        let interpreter = Interpreter::default();

        let witness = interpreter
            .execute(&program, &vec![Bn128Field::from(42)])
            .unwrap();

        let proof =
            <Libsnark as Backend<Bn128Field, GM17>>::generate_proof(program, witness, keypair.pk);

        let ans = <Libsnark as Backend<Bn128Field, GM17>>::verify(keypair.vk, proof);
        assert!(ans);
    }
}
