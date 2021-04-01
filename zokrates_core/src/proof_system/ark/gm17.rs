use ark_gm17::{
    prepare_verifying_key, verify_proof, PreparedVerifyingKey, Proof as ArkProof, ProvingKey,
    VerifyingKey,
};

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use zokrates_field::{ArkFieldExtensions, Bw6_761Field, Field};

use crate::ir::{Prog, Witness};
use crate::proof_system::ark::Ark;
use crate::proof_system::ark::Computation;
use crate::proof_system::ark::{parse_fr, parse_g1, parse_g2, parse_g2_fq};
use crate::proof_system::gm17::{NotBw6_761Field, ProofPoints, VerificationKey, GM17};
use crate::proof_system::Scheme;
use crate::proof_system::{Backend, Proof, SetupKeypair};

impl<T: Field + ArkFieldExtensions + NotBw6_761Field> Backend<T, GM17> for Ark {
    fn setup(program: Prog<T>) -> SetupKeypair<<GM17 as Scheme<T>>::VerificationKey> {
        let parameters = Computation::without_witness(program).setup();

        let mut pk: Vec<u8> = Vec::new();
        parameters.serialize_uncompressed(&mut pk).unwrap();

        let vk = VerificationKey {
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
        };

        SetupKeypair::new(vk, pk)
    }

    fn generate_proof(
        program: Prog<T>,
        witness: Witness<T>,
        proving_key: Vec<u8>,
    ) -> Proof<<GM17 as Scheme<T>>::ProofPoints> {
        let computation = Computation::with_witness(program, witness);
        let params = ProvingKey::<<T as ArkFieldExtensions>::ArkEngine>::deserialize_uncompressed(
            &mut proving_key.as_slice(),
        )
        .unwrap();

        let proof = computation.clone().prove(&params);
        let proof_points = ProofPoints {
            a: parse_g1::<T>(&proof.a),
            b: parse_g2::<T>(&proof.b),
            c: parse_g1::<T>(&proof.c),
        };

        let inputs = computation
            .public_inputs_values()
            .iter()
            .map(parse_fr::<T>)
            .collect::<Vec<_>>();

        Proof::new(proof_points, inputs)
    }

    fn verify(
        vk: <GM17 as Scheme<T>>::VerificationKey,
        proof: Proof<<GM17 as Scheme<T>>::ProofPoints>,
    ) -> bool {
        let vk = VerifyingKey {
            h_g2: serialization::to_g2::<T>(vk.h),
            g_alpha_g1: serialization::to_g1::<T>(vk.g_alpha),
            h_beta_g2: serialization::to_g2::<T>(vk.h_beta),
            g_gamma_g1: serialization::to_g1::<T>(vk.g_gamma),
            h_gamma_g2: serialization::to_g2::<T>(vk.h_gamma),
            query: vk
                .query
                .into_iter()
                .map(serialization::to_g1::<T>)
                .collect(),
        };

        let ark_proof = ArkProof {
            a: serialization::to_g1::<T>(proof.proof.a),
            b: serialization::to_g2::<T>(proof.proof.b),
            c: serialization::to_g1::<T>(proof.proof.c),
        };

        let pvk: PreparedVerifyingKey<<T as ArkFieldExtensions>::ArkEngine> =
            prepare_verifying_key(&vk);

        let public_inputs: Vec<_> = proof
            .inputs
            .iter()
            .map(|s| {
                T::try_from_str(s.trim_start_matches("0x"), 16)
                    .unwrap()
                    .into_ark()
            })
            .collect::<Vec<_>>();

        verify_proof(&pvk, &ark_proof, &public_inputs).unwrap()
    }
}

impl Backend<Bw6_761Field, GM17> for Ark {
    fn setup(
        program: Prog<Bw6_761Field>,
    ) -> SetupKeypair<<GM17 as Scheme<Bw6_761Field>>::VerificationKey> {
        let parameters = Computation::without_witness(program).setup();

        let mut pk: Vec<u8> = Vec::new();
        parameters.serialize_uncompressed(&mut pk).unwrap();

        let vk = VerificationKey {
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
        };

        SetupKeypair::new(vk, pk)
    }

    fn generate_proof(
        program: Prog<Bw6_761Field>,
        witness: Witness<Bw6_761Field>,
        proving_key: Vec<u8>,
    ) -> Proof<<GM17 as Scheme<Bw6_761Field>>::ProofPoints> {
        let computation = Computation::with_witness(program, witness);
        let params =
            ProvingKey::<<Bw6_761Field as ArkFieldExtensions>::ArkEngine>::deserialize_uncompressed(
                &mut proving_key.as_slice(),
            )
                .unwrap();

        let proof = computation.clone().prove(&params);
        let proof_points = ProofPoints {
            a: parse_g1::<Bw6_761Field>(&proof.a),
            b: parse_g2_fq::<Bw6_761Field>(&proof.b),
            c: parse_g1::<Bw6_761Field>(&proof.c),
        };

        let inputs = computation
            .public_inputs_values()
            .iter()
            .map(parse_fr::<Bw6_761Field>)
            .collect::<Vec<_>>();

        Proof::new(proof_points, inputs)
    }

    fn verify(
        vk: <GM17 as Scheme<Bw6_761Field>>::VerificationKey,
        proof: Proof<<GM17 as Scheme<Bw6_761Field>>::ProofPoints>,
    ) -> bool {
        let vk = VerifyingKey {
            h_g2: serialization::to_g2_fq::<Bw6_761Field>(vk.h),
            g_alpha_g1: serialization::to_g1::<Bw6_761Field>(vk.g_alpha),
            h_beta_g2: serialization::to_g2_fq::<Bw6_761Field>(vk.h_beta),
            g_gamma_g1: serialization::to_g1::<Bw6_761Field>(vk.g_gamma),
            h_gamma_g2: serialization::to_g2_fq::<Bw6_761Field>(vk.h_gamma),
            query: vk
                .query
                .into_iter()
                .map(serialization::to_g1::<Bw6_761Field>)
                .collect(),
        };

        let ark_proof = ArkProof {
            a: serialization::to_g1::<Bw6_761Field>(proof.proof.a),
            b: serialization::to_g2_fq::<Bw6_761Field>(proof.proof.b),
            c: serialization::to_g1::<Bw6_761Field>(proof.proof.c),
        };

        let pvk: PreparedVerifyingKey<<Bw6_761Field as ArkFieldExtensions>::ArkEngine> =
            prepare_verifying_key(&vk);

        let public_inputs: Vec<_> = proof
            .inputs
            .iter()
            .map(|s| {
                Bw6_761Field::try_from_str(s.trim_start_matches("0x"), 16)
                    .unwrap()
                    .into_ark()
            })
            .collect::<Vec<_>>();

        verify_proof(&pvk, &ark_proof, &public_inputs).unwrap()
    }
}

pub mod serialization {
    use crate::proof_system::{G1Affine, G2Affine, G2AffineFq};
    use ark_ec::PairingEngine;
    use ark_ff::FromBytes;
    use zokrates_field::ArkFieldExtensions;

    #[inline]
    fn decode_hex(value: String) -> Vec<u8> {
        let mut bytes = hex::decode(value.strip_prefix("0x").unwrap()).unwrap();
        bytes.reverse();
        bytes
    }

    pub fn to_g1<T: ArkFieldExtensions>(g1: G1Affine) -> <T::ArkEngine as PairingEngine>::G1Affine {
        let mut bytes = vec![];
        bytes.append(&mut decode_hex(g1.0));
        bytes.append(&mut decode_hex(g1.1));
        bytes.push(0u8); // infinity flag

        <T::ArkEngine as PairingEngine>::G1Affine::read(&*bytes).unwrap()
    }

    pub fn to_g2<T: ArkFieldExtensions>(g2: G2Affine) -> <T::ArkEngine as PairingEngine>::G2Affine {
        let mut bytes = vec![];
        bytes.append(&mut decode_hex((g2.0).0));
        bytes.append(&mut decode_hex((g2.0).1));
        bytes.append(&mut decode_hex((g2.1).0));
        bytes.append(&mut decode_hex((g2.1).1));
        bytes.push(0u8); // infinity flag

        <T::ArkEngine as PairingEngine>::G2Affine::read(&*bytes).unwrap()
    }

    pub fn to_g2_fq<T: ArkFieldExtensions>(
        g2: G2AffineFq,
    ) -> <T::ArkEngine as PairingEngine>::G2Affine {
        let mut bytes = vec![];
        bytes.append(&mut decode_hex(g2.0));
        bytes.append(&mut decode_hex(g2.1));
        bytes.push(0u8); // infinity flag

        <T::ArkEngine as PairingEngine>::G2Affine::read(&*bytes).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use crate::flat_absy::FlatVariable;
    use crate::ir::{Function, Interpreter, Prog, Statement};

    use super::*;
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

        let keypair = <Ark as Backend<Bls12_377Field, GM17>>::setup(program.clone());
        let interpreter = Interpreter::default();

        let witness = interpreter
            .execute(&program, &[Bls12_377Field::from(42)])
            .unwrap();

        let proof =
            <Ark as Backend<Bls12_377Field, GM17>>::generate_proof(program, witness, keypair.pk);
        let ans = <Ark as Backend<Bls12_377Field, GM17>>::verify(keypair.vk, proof);

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

        let keypair = <Ark as Backend<Bw6_761Field, GM17>>::setup(program.clone());
        let interpreter = Interpreter::default();

        let witness = interpreter
            .execute(&program, &[Bw6_761Field::from(42)])
            .unwrap();

        let proof =
            <Ark as Backend<Bw6_761Field, GM17>>::generate_proof(program, witness, keypair.pk);
        let ans = <Ark as Backend<Bw6_761Field, GM17>>::verify(keypair.vk, proof);

        assert!(ans);
    }
}
