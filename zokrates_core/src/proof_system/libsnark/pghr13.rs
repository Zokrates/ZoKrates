use crate::proof_system::libsnark::ffi::{c_free, Buffer, ProofResult, SetupResult};
use crate::proof_system::libsnark::{
    prepare_generate_proof, prepare_public_inputs, prepare_setup, Libsnark,
};
use crate::proof_system::{Backend, G1Affine, G2Affine, NonUniversalBackend, Proof, SetupKeypair};

use crate::ir::{ProgIterator, Statement, Witness};
use crate::proof_system::libsnark::serialization::{read_g1, read_g2, write_g1, write_g2};
use crate::proof_system::pghr13::{ProofPoints, VerificationKey, PGHR13};
use crate::proof_system::Scheme;
use std::io::{BufReader, BufWriter, Write};
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
    fn generate_proof<I: IntoIterator<Item = Statement<Bn128Field>>>(
        program: ProgIterator<Bn128Field, I>,
        witness: Witness<Bn128Field>,
        proving_key: Vec<u8>,
    ) -> Proof<Bn128Field, PGHR13> {
        let program = program.collect();

        let (public_inputs_arr, public_inputs_length, private_inputs_arr, private_inputs_length) =
            prepare_generate_proof(program.clone(), witness.clone());

        let mut pk_buffer = Buffer::from_vec(&proving_key);

        let proof = unsafe {
            let result = pghr13_bn128_generate_proof(
                &mut pk_buffer as *mut _,
                public_inputs_arr[0].as_ptr(),
                public_inputs_length as i32,
                private_inputs_arr[0].as_ptr(),
                private_inputs_length as i32,
            );

            let proof = std::slice::from_raw_parts(result.proof.data, result.proof.length as usize)
                .to_vec();

            // free c allocated buffer
            c_free(result.proof.data);

            proof
        };

        let mut reader = BufReader::new(proof.as_slice());
        let a = read_g1(&mut reader).unwrap();
        let a_p = read_g1(&mut reader).unwrap();
        let b = read_g2(&mut reader).unwrap();
        let b_p = read_g1(&mut reader).unwrap();
        let c = read_g1(&mut reader).unwrap();
        let c_p = read_g1(&mut reader).unwrap();
        let h = read_g1(&mut reader).unwrap();
        let k = read_g1(&mut reader).unwrap();

        let points = ProofPoints::<G1Affine, G2Affine> {
            a,
            a_p,
            b,
            b_p,
            c,
            c_p,
            h,
            k,
        };

        let public_inputs: Vec<String> = program
            .public_inputs(&witness)
            .iter()
            .map(|f| format!("0x{:064x}", f.to_biguint()))
            .collect();

        Proof::new(points, public_inputs)
    }

    fn verify(
        vk: <PGHR13 as Scheme<Bn128Field>>::VerificationKey,
        proof: Proof<Bn128Field, PGHR13>,
    ) -> bool {
        let vk_buffer = vec![];
        let mut vk_writer = BufWriter::new(vk_buffer);

        write_g2(&mut vk_writer, &vk.a);
        write_g1(&mut vk_writer, &vk.b);
        write_g2(&mut vk_writer, &vk.c);
        write_g2(&mut vk_writer, &vk.gamma);
        write_g1(&mut vk_writer, &vk.gamma_beta_1);
        write_g2(&mut vk_writer, &vk.gamma_beta_2);
        write_g2(&mut vk_writer, &vk.z);

        vk.ic
            .iter()
            .for_each(|ic_query| write_g1(&mut vk_writer, ic_query));
        vk_writer.flush().unwrap();

        let proof_buffer = vec![];
        let mut proof_writer = BufWriter::new(proof_buffer);

        write_g1(&mut proof_writer, &proof.proof.a);
        write_g1(&mut proof_writer, &proof.proof.a_p);
        write_g2(&mut proof_writer, &proof.proof.b);
        write_g1(&mut proof_writer, &proof.proof.b_p);
        write_g1(&mut proof_writer, &proof.proof.c);
        write_g1(&mut proof_writer, &proof.proof.c_p);
        write_g1(&mut proof_writer, &proof.proof.h);
        write_g1(&mut proof_writer, &proof.proof.k);
        proof_writer.flush().unwrap();

        let public_inputs: Vec<_> = proof
            .inputs
            .iter()
            .map(|v| Bn128Field::try_from_str(v.as_str().trim_start_matches("0x"), 16).unwrap())
            .collect();

        let (public_inputs_arr, public_inputs_length) = prepare_public_inputs(public_inputs);

        let mut vk_buffer = Buffer::from_vec(vk_writer.get_ref());
        let mut proof_buffer = Buffer::from_vec(proof_writer.get_ref());

        unsafe {
            pghr13_bn128_verify(
                &mut vk_buffer as *mut _,
                &mut proof_buffer as *mut _,
                public_inputs_arr[0].as_ptr(),
                public_inputs_length as i32,
            )
        }
    }
}

impl NonUniversalBackend<Bn128Field, PGHR13> for Libsnark {
    fn setup<I: IntoIterator<Item = Statement<Bn128Field>>>(
        program: ProgIterator<Bn128Field, I>,
    ) -> SetupKeypair<Bn128Field, PGHR13> {
        let program = program.collect();

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
            c_free(result.vk.data);
            c_free(result.pk.data);

            (vk, pk)
        };

        let vk_slice = vk.as_slice();
        let mut reader = BufReader::new(vk_slice);

        let a = read_g2(&mut reader).unwrap();
        let b = read_g1(&mut reader).unwrap();
        let c = read_g2(&mut reader).unwrap();
        let gamma = read_g2(&mut reader).unwrap();
        let gamma_beta_1 = read_g1(&mut reader).unwrap();
        let gamma_beta_2 = read_g2(&mut reader).unwrap();
        let z = read_g2(&mut reader).unwrap();

        let mut ic = vec![];
        while let Ok(q) = read_g1(&mut reader) {
            ic.push(q);
        }

        let vk = VerificationKey::<G1Affine, G2Affine> {
            a,
            b,
            c,
            gamma,
            gamma_beta_1,
            gamma_beta_2,
            z,
            ic,
        };

        SetupKeypair::new(vk, pk)
    }
}

#[cfg(feature = "libsnark")]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::flat_absy::{FlatParameter, FlatVariable};
    use crate::ir::{Interpreter, Prog, Statement};
    use zokrates_field::Bn128Field;

    #[test]
    fn verify() {
        let program: Prog<Bn128Field> = Prog {
            arguments: vec![FlatParameter::private(FlatVariable::new(0))],
            return_count: 1,
            statements: vec![Statement::constraint(
                FlatVariable::new(0),
                FlatVariable::public(0),
            )],
        };

        let keypair = <Libsnark as NonUniversalBackend<Bn128Field, PGHR13>>::setup(program.clone());
        let interpreter = Interpreter::default();

        let witness = interpreter
            .execute(program.clone(), &vec![Bn128Field::from(42)])
            .unwrap();

        let proof =
            <Libsnark as Backend<Bn128Field, PGHR13>>::generate_proof(program, witness, keypair.pk);

        let ans = <Libsnark as Backend<Bn128Field, PGHR13>>::verify(keypair.vk, proof);
        assert!(ans);
    }
}
