use algebra_core::{CanonicalDeserialize, CanonicalSerialize};
use ir::{Prog, Witness};
use proof_system::schemes::gm17::{NotBw6_761Field, ProofPoints, VerificationKey, GM17};
use proof_system::schemes::Scheme;
use proof_system::zexe::{parse_fr, parse_g1, parse_g2, parse_g2_fq, Computation, Zexe};
use proof_system::{Backend, G1Affine, G2Affine, G2AffineFq, Proof};
use zexe_gm17::{
    prepare_verifying_key, verify_proof, Parameters, PreparedVerifyingKey, Proof as ZexeProof,
    VerifyingKey,
};
use zokrates_field::{Bw6_761Field, Field, ZexeFieldExtensions};

impl<T: Field + ZexeFieldExtensions + NotBw6_761Field> Backend<T, GM17> for Zexe {
    fn setup(
        prog: Prog<T>,
    ) -> (
        <GM17 as Scheme<T>>::ProvingKey,
        <GM17 as Scheme<T>>::VerificationKey,
    ) {
        let parameters = Computation::without_witness(prog).setup();

        let mut pk: Vec<u8> = Vec::new();
        let mut vk_raw: Vec<u8> = Vec::new();

        parameters.serialize_uncompressed(&mut pk).unwrap();
        parameters.vk.serialize_uncompressed(&mut vk_raw).unwrap();

        let vk = VerificationKey::<G1Affine, G2Affine> {
            h: parse_g2::<T>(&parameters.vk.h_g2),
            g_alpha: parse_g1::<T>(&parameters.vk.g_alpha_g1),
            h_beta: parse_g2::<T>(&parameters.vk.h_beta_g2),
            g_gamma: parse_g1::<T>(&parameters.vk.g_gamma_g1),
            h_gamma: parse_g2::<T>(&parameters.vk.h_gamma_g2),
            query: parameters
                .vk
                .query
                .iter()
                .map(|g1| parse_g1::<T>(g1))
                .collect(),
            raw: hex::encode(vk_raw),
        };

        (pk, vk)
    }

    fn generate_proof(
        program: Prog<T>,
        witness: Witness<T>,
        proving_key: <GM17 as Scheme<T>>::ProvingKey,
    ) -> Proof<<GM17 as Scheme<T>>::ProofPoints> {
        let computation = Computation::with_witness(program, witness);
        let params =
            Parameters::<<T as ZexeFieldExtensions>::ZexeEngine>::deserialize_uncompressed(
                &mut proving_key.as_slice(),
            )
            .unwrap();

        let proof = computation.clone().prove(&params);
        let proof_points = ProofPoints::<G1Affine, G2Affine> {
            a: parse_g1::<T>(&proof.a),
            b: parse_g2::<T>(&proof.b),
            c: parse_g1::<T>(&proof.c),
        };

        let inputs = computation
            .public_inputs_values()
            .iter()
            .map(parse_fr::<T>)
            .collect::<Vec<_>>();

        let mut raw: Vec<u8> = Vec::new();
        proof.serialize_uncompressed(&mut raw).unwrap();

        Proof::new(proof_points, inputs, hex::encode(&raw))
    }

    fn verify(
        vk: <GM17 as Scheme<T>>::VerificationKey,
        proof: Proof<<GM17 as Scheme<T>>::ProofPoints>,
    ) -> bool {
        let vk_raw = hex::decode(vk.raw.clone()).unwrap();
        let proof_raw = hex::decode(proof.raw.clone()).unwrap();

        let vk: VerifyingKey<<T as ZexeFieldExtensions>::ZexeEngine> =
            VerifyingKey::deserialize_uncompressed(&mut vk_raw.as_slice()).unwrap();

        let pvk: PreparedVerifyingKey<<T as ZexeFieldExtensions>::ZexeEngine> =
            prepare_verifying_key(&vk);

        let zexe_proof: ZexeProof<<T as ZexeFieldExtensions>::ZexeEngine> =
            ZexeProof::deserialize_uncompressed(&mut proof_raw.as_slice()).unwrap();

        let public_inputs: Vec<_> = proof
            .inputs
            .iter()
            .map(|s| {
                T::try_from_str(s.trim_start_matches("0x"), 16)
                    .expect(format!("Invalid {} value: {}", T::name(), s).as_str())
                    .into_zexe()
            })
            .collect::<Vec<_>>();

        verify_proof(&pvk, &zexe_proof, &public_inputs).unwrap_or(false)
    }
}

impl Backend<Bw6_761Field, GM17> for Zexe {
    fn setup(
        prog: Prog<Bw6_761Field>,
    ) -> (
        <GM17 as Scheme<Bw6_761Field>>::ProvingKey,
        <GM17 as Scheme<Bw6_761Field>>::VerificationKey,
    ) {
        let parameters = Computation::without_witness(prog).setup();

        let mut pk: Vec<u8> = Vec::new();
        let mut vk_raw: Vec<u8> = Vec::new();

        parameters.serialize_uncompressed(&mut pk).unwrap();
        parameters.vk.serialize_uncompressed(&mut vk_raw).unwrap();

        let vk = VerificationKey::<G1Affine, G2AffineFq> {
            h: parse_g2_fq::<Bw6_761Field>(&parameters.vk.h_g2),
            g_alpha: parse_g1::<Bw6_761Field>(&parameters.vk.g_alpha_g1),
            h_beta: parse_g2_fq::<Bw6_761Field>(&parameters.vk.h_beta_g2),
            g_gamma: parse_g1::<Bw6_761Field>(&parameters.vk.g_gamma_g1),
            h_gamma: parse_g2_fq::<Bw6_761Field>(&parameters.vk.h_gamma_g2),
            query: parameters
                .vk
                .query
                .iter()
                .map(|g1| parse_g1::<Bw6_761Field>(g1))
                .collect(),
            raw: hex::encode(vk_raw),
        };

        (pk, vk)
    }

    fn generate_proof(
        program: Prog<Bw6_761Field>,
        witness: Witness<Bw6_761Field>,
        proving_key: <GM17 as Scheme<Bw6_761Field>>::ProvingKey,
    ) -> Proof<<GM17 as Scheme<Bw6_761Field>>::ProofPoints> {
        let computation = Computation::with_witness(program, witness);
        let params =
            Parameters::<<Bw6_761Field as ZexeFieldExtensions>::ZexeEngine>::deserialize_uncompressed(
                &mut proving_key.as_slice(),
            ).unwrap();

        let proof = computation.clone().prove(&params);
        let proof_points = ProofPoints::<G1Affine, G2AffineFq> {
            a: parse_g1::<Bw6_761Field>(&proof.a),
            b: parse_g2_fq::<Bw6_761Field>(&proof.b),
            c: parse_g1::<Bw6_761Field>(&proof.c),
        };

        let inputs = computation
            .public_inputs_values()
            .iter()
            .map(parse_fr::<Bw6_761Field>)
            .collect::<Vec<_>>();

        let mut raw: Vec<u8> = Vec::new();
        proof.serialize_uncompressed(&mut raw).unwrap();

        Proof::new(proof_points, inputs, hex::encode(&raw))
    }

    fn verify(
        vk: <GM17 as Scheme<Bw6_761Field>>::VerificationKey,
        proof: Proof<<GM17 as Scheme<Bw6_761Field>>::ProofPoints>,
    ) -> bool {
        let vk_raw = hex::decode(vk.raw.clone()).unwrap();
        let proof_raw = hex::decode(proof.raw.clone()).unwrap();

        let vk: VerifyingKey<<Bw6_761Field as ZexeFieldExtensions>::ZexeEngine> =
            VerifyingKey::deserialize_uncompressed(&mut vk_raw.as_slice()).unwrap();

        let pvk: PreparedVerifyingKey<<Bw6_761Field as ZexeFieldExtensions>::ZexeEngine> =
            prepare_verifying_key(&vk);

        let zexe_proof: ZexeProof<<Bw6_761Field as ZexeFieldExtensions>::ZexeEngine> =
            ZexeProof::deserialize_uncompressed(&mut proof_raw.as_slice()).unwrap();

        let public_inputs: Vec<_> = proof
            .inputs
            .iter()
            .map(|s| {
                Bw6_761Field::try_from_str(s.trim_start_matches("0x"), 16)
                    .expect(format!("Invalid bw6_761 value: {}", s).as_str())
                    .into_zexe()
            })
            .collect::<Vec<_>>();

        verify_proof(&pvk, &zexe_proof, &public_inputs).unwrap_or(false)
    }
}

#[cfg(test)]
mod tests {
    use crate::flat_absy::FlatVariable;
    use crate::ir::{Function, Prog, Statement};

    use super::*;
    use ir::Interpreter;
    use proof_system::schemes::gm17::GM17;
    use zokrates_field::{Bls12_377Field, Bw6_761Field};

    #[test]
    fn verify_bls12_377_field() {
        let program: Prog<Bls12_377Field> = Prog {
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

        let keypair = Zexe::setup(program.clone());
        let interpreter = Interpreter::default();

        let witness = interpreter
            .execute(&program, &vec![Bls12_377Field::from(42)])
            .unwrap();

        let proof = Zexe::generate_proof(program.clone(), witness, keypair.0);
        let ans = <Zexe as Backend<Bls12_377Field, GM17>>::verify(keypair.1, proof);

        assert!(ans);
    }

    #[test]
    fn verify_bw6_761_field() {
        let program: Prog<Bw6_761Field> = Prog {
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

        let keypair = Zexe::setup(program.clone());
        let interpreter = Interpreter::default();

        let witness = interpreter
            .execute(&program, &vec![Bw6_761Field::from(42)])
            .unwrap();

        let proof = Zexe::generate_proof(program.clone(), witness, keypair.0);
        let ans = <Zexe as Backend<Bw6_761Field, GM17>>::verify(keypair.1, proof);

        assert!(ans);
    }
}
