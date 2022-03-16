use ark_crypto_primitives::SNARK;
use ark_gm17::{
    prepare_verifying_key, verify_proof, PreparedVerifyingKey, Proof as ArkProof, ProvingKey,
    VerifyingKey, GM17 as ArkGM17,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use zokrates_field::{ArkFieldExtensions, Bw6_761Field, Field};

use crate::ir::{ProgIterator, Statement, Witness};
use crate::proof_system::ark::Computation;
use crate::proof_system::ark::{parse_fr, parse_g1, parse_g2, parse_g2_fq};
use crate::proof_system::ark::{serialization, Ark};
use crate::proof_system::gm17::{ProofPoints, VerificationKey, GM17};
use crate::proof_system::{Backend, NonUniversalBackend, Proof, SetupKeypair};
use crate::proof_system::{NotBw6_761Field, Scheme};
use ark_bw6_761::BW6_761;
use rand_0_7::SeedableRng;

impl<T: Field + ArkFieldExtensions + NotBw6_761Field> NonUniversalBackend<T, GM17> for Ark {
    fn setup<I: IntoIterator<Item = Statement<T>>>(
        program: ProgIterator<T, I>,
    ) -> SetupKeypair<<GM17 as Scheme<T>>::VerificationKey> {
        let computation = Computation::without_witness(program);

        let rng = &mut rand_0_7::rngs::StdRng::from_entropy();
        let (pk, vk) = ArkGM17::<T::ArkEngine>::circuit_specific_setup(computation, rng).unwrap();

        let mut pk_vec: Vec<u8> = Vec::new();
        pk.serialize_uncompressed(&mut pk_vec).unwrap();

        let vk = VerificationKey {
            h: parse_g2::<T>(&vk.h_g2),
            g_alpha: parse_g1::<T>(&vk.g_alpha_g1),
            h_beta: parse_g2::<T>(&vk.h_beta_g2),
            g_gamma: parse_g1::<T>(&vk.g_gamma_g1),
            h_gamma: parse_g2::<T>(&vk.h_gamma_g2),
            query: vk.query.iter().map(|g1| parse_g1::<T>(g1)).collect(),
        };

        SetupKeypair::new(vk, pk_vec)
    }
}

impl<T: Field + ArkFieldExtensions + NotBw6_761Field> Backend<T, GM17> for Ark {
    fn generate_proof<I: IntoIterator<Item = Statement<T>>>(
        program: ProgIterator<T, I>,
        witness: Witness<T>,
        proving_key: Vec<u8>,
    ) -> Proof<<GM17 as Scheme<T>>::ProofPoints> {
        let computation = Computation::with_witness(program, witness);

        let inputs = computation
            .public_inputs_values()
            .iter()
            .map(parse_fr::<T>)
            .collect::<Vec<_>>();

        let pk = ProvingKey::<<T as ArkFieldExtensions>::ArkEngine>::deserialize_uncompressed(
            &mut proving_key.as_slice(),
        )
        .unwrap();

        let rng = &mut rand_0_7::rngs::StdRng::from_entropy();
        let proof = ArkGM17::<T::ArkEngine>::prove(&pk, computation, rng).unwrap();

        let proof_points = ProofPoints {
            a: parse_g1::<T>(&proof.a),
            b: parse_g2::<T>(&proof.b),
            c: parse_g1::<T>(&proof.c),
        };

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

impl NonUniversalBackend<Bw6_761Field, GM17> for Ark {
    fn setup<I: IntoIterator<Item = Statement<Bw6_761Field>>>(
        program: ProgIterator<Bw6_761Field, I>,
    ) -> SetupKeypair<<GM17 as Scheme<Bw6_761Field>>::VerificationKey> {
        let computation = Computation::without_witness(program);

        let rng = &mut rand_0_7::rngs::StdRng::from_entropy();
        let (pk, vk) = ArkGM17::<BW6_761>::circuit_specific_setup(computation, rng).unwrap();

        let mut pk_vec: Vec<u8> = Vec::new();
        pk.serialize_uncompressed(&mut pk_vec).unwrap();

        let vk = VerificationKey {
            h: parse_g2_fq::<Bw6_761Field>(&vk.h_g2),
            g_alpha: parse_g1::<Bw6_761Field>(&vk.g_alpha_g1),
            h_beta: parse_g2_fq::<Bw6_761Field>(&vk.h_beta_g2),
            g_gamma: parse_g1::<Bw6_761Field>(&vk.g_gamma_g1),
            h_gamma: parse_g2_fq::<Bw6_761Field>(&vk.h_gamma_g2),
            query: vk.query.iter().map(parse_g1::<Bw6_761Field>).collect(),
        };

        SetupKeypair::new(vk, pk_vec)
    }
}

impl Backend<Bw6_761Field, GM17> for Ark {
    fn generate_proof<I: IntoIterator<Item = Statement<Bw6_761Field>>>(
        program: ProgIterator<Bw6_761Field, I>,
        witness: Witness<Bw6_761Field>,
        proving_key: Vec<u8>,
    ) -> Proof<<GM17 as Scheme<Bw6_761Field>>::ProofPoints> {
        let computation = Computation::with_witness(program, witness);

        let inputs = computation
            .public_inputs_values()
            .iter()
            .map(parse_fr::<Bw6_761Field>)
            .collect::<Vec<_>>();

        let pk =
            ProvingKey::<<Bw6_761Field as ArkFieldExtensions>::ArkEngine>::deserialize_uncompressed(
                &mut proving_key.as_slice(),
            )
                .unwrap();

        let rng = &mut rand_0_7::rngs::StdRng::from_entropy();
        let proof = ArkGM17::<BW6_761>::prove(&pk, computation, rng).unwrap();

        let proof_points = ProofPoints {
            a: parse_g1::<Bw6_761Field>(&proof.a),
            b: parse_g2_fq::<Bw6_761Field>(&proof.b),
            c: parse_g1::<Bw6_761Field>(&proof.c),
        };

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

#[cfg(test)]
mod tests {
    use crate::flat_absy::{FlatParameter, FlatVariable};
    use crate::ir::{Interpreter, Prog, Statement};

    use super::*;
    use zokrates_field::{Bls12_377Field, Bw6_761Field};

    #[test]
    fn verify_bls12_377_field() {
        let program: Prog<Bls12_377Field> = Prog {
            arguments: vec![FlatParameter::public(FlatVariable::new(0))],
            return_count: 1,
            statements: vec![Statement::constraint(
                FlatVariable::new(0),
                FlatVariable::public(0),
            )],
        };

        let keypair = <Ark as NonUniversalBackend<Bls12_377Field, GM17>>::setup(program.clone());
        let interpreter = Interpreter::default();

        let witness = interpreter
            .execute(program.clone(), &[Bls12_377Field::from(42)])
            .unwrap();

        let proof =
            <Ark as Backend<Bls12_377Field, GM17>>::generate_proof(program, witness, keypair.pk);
        let ans = <Ark as Backend<Bls12_377Field, GM17>>::verify(keypair.vk, proof);

        assert!(ans);
    }

    #[test]
    fn verify_bw6_761_field() {
        let program: Prog<Bw6_761Field> = Prog {
            arguments: vec![FlatParameter::public(FlatVariable::new(0))],
            return_count: 1,
            statements: vec![Statement::constraint(
                FlatVariable::new(0),
                FlatVariable::public(0),
            )],
        };

        let keypair = <Ark as NonUniversalBackend<Bw6_761Field, GM17>>::setup(program.clone());
        let interpreter = Interpreter::default();

        let witness = interpreter
            .execute(program.clone(), &[Bw6_761Field::from(42)])
            .unwrap();

        let proof =
            <Ark as Backend<Bw6_761Field, GM17>>::generate_proof(program, witness, keypair.pk);
        let ans = <Ark as Backend<Bw6_761Field, GM17>>::verify(keypair.vk, proof);

        assert!(ans);
    }
}
