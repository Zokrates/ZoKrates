use ark_crypto_primitives::SNARK;
use ark_groth16::{
    prepare_verifying_key, verify_proof, Groth16, PreparedVerifyingKey, Proof as ArkProof,
    ProvingKey, VerifyingKey,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use std::io::Read;
use zokrates_field::ArkFieldExtensions;
use zokrates_field::Field;
use zokrates_proof_systems::{Backend, NonUniversalBackend, Proof, SetupKeypair};

use crate::Computation;
use crate::{parse_fr, serialization, Ark};
use crate::{parse_g1, parse_g2};
use rand_0_8::{CryptoRng, RngCore};
use zokrates_ast::ir::{ProgIterator, Statement, Witness};
use zokrates_proof_systems::groth16::{ProofPoints, VerificationKey, G16};
use zokrates_proof_systems::Scheme;

impl<T: Field + ArkFieldExtensions> Backend<T, G16> for Ark {
    fn generate_proof<
        'a,
        I: IntoIterator<Item = Statement<'a, T>>,
        R: Read,
        G: RngCore + CryptoRng,
    >(
        program: ProgIterator<'a, T, I>,
        witness: Witness<T>,
        proving_key: R,
        rng: &mut G,
    ) -> Proof<T, G16> {
        let computation = Computation::with_witness(program, witness);

        let inputs = computation
            .public_inputs_values()
            .iter()
            .map(parse_fr::<T>)
            .collect::<Vec<_>>();

        let pk =
            ProvingKey::<<T as ArkFieldExtensions>::ArkEngine>::deserialize_unchecked(proving_key)
                .unwrap();

        let proof = Groth16::<T::ArkEngine>::prove(&pk, computation, rng).unwrap();

        let proof_points = ProofPoints {
            a: parse_g1::<T>(&proof.a),
            b: parse_g2::<T>(&proof.b),
            c: parse_g1::<T>(&proof.c),
        };

        Proof::new(proof_points, inputs)
    }

    fn verify(vk: <G16 as Scheme<T>>::VerificationKey, proof: Proof<T, G16>) -> bool {
        let vk = VerifyingKey {
            alpha_g1: serialization::to_g1::<T>(vk.alpha),
            beta_g2: serialization::to_g2::<T>(vk.beta),
            gamma_g2: serialization::to_g2::<T>(vk.gamma),
            delta_g2: serialization::to_g2::<T>(vk.delta),
            gamma_abc_g1: vk
                .gamma_abc
                .into_iter()
                .map(serialization::to_g1::<T>)
                .collect(),
        };

        let pvk: PreparedVerifyingKey<T::ArkEngine> = prepare_verifying_key(&vk);
        let ark_proof = ArkProof {
            a: serialization::to_g1::<T>(proof.proof.a),
            b: serialization::to_g2::<T>(proof.proof.b),
            c: serialization::to_g1::<T>(proof.proof.c),
        };

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

impl<T: Field + ArkFieldExtensions> NonUniversalBackend<T, G16> for Ark {
    fn setup<'a, I: IntoIterator<Item = Statement<'a, T>>, R: RngCore + CryptoRng>(
        program: ProgIterator<'a, T, I>,
        rng: &mut R,
    ) -> SetupKeypair<T, G16> {
        let computation = Computation::without_witness(program);
        let (pk, vk) = Groth16::<T::ArkEngine>::circuit_specific_setup(computation, rng).unwrap();

        let mut pk_vec: Vec<u8> = Vec::new();
        pk.serialize_unchecked(&mut pk_vec).unwrap();

        let vk = VerificationKey {
            alpha: parse_g1::<T>(&vk.alpha_g1),
            beta: parse_g2::<T>(&vk.beta_g2),
            gamma: parse_g2::<T>(&vk.gamma_g2),
            delta: parse_g2::<T>(&vk.delta_g2),
            gamma_abc: vk.gamma_abc_g1.iter().map(|g1| parse_g1::<T>(g1)).collect(),
        };

        SetupKeypair::new(vk, pk_vec)
    }
}

#[cfg(test)]
mod tests {
    use rand_0_8::rngs::StdRng;
    use rand_0_8::SeedableRng;
    use zokrates_ast::flat::{Parameter, Variable};
    use zokrates_ast::ir::{Prog, Statement};
    use zokrates_interpreter::Interpreter;

    use super::*;
    use zokrates_field::{Bls12_377Field, Bw6_761Field};

    #[test]
    fn verify_bls12_377_field() {
        let program: Prog<Bls12_377Field> = Prog {
            module_map: Default::default(),
            arguments: vec![Parameter::public(Variable::new(0))],
            return_count: 1,
            statements: vec![Statement::constraint(
                Variable::new(0),
                Variable::public(0),
                None,
            )],
            solvers: vec![],
        };

        let rng = &mut StdRng::from_entropy();
        let keypair =
            <Ark as NonUniversalBackend<Bls12_377Field, G16>>::setup(program.clone(), rng);
        let interpreter = Interpreter::default();

        let witness = interpreter
            .execute(
                &[Bls12_377Field::from(42)],
                program.statements.iter(),
                &program.arguments,
                &program.solvers,
            )
            .unwrap();

        let proof = <Ark as Backend<Bls12_377Field, G16>>::generate_proof(
            program,
            witness,
            keypair.pk.as_slice(),
            rng,
        );
        let ans = <Ark as Backend<Bls12_377Field, G16>>::verify(keypair.vk, proof);

        assert!(ans);
    }

    #[test]
    fn verify_bw6_761_field() {
        let program: Prog<Bw6_761Field> = Prog {
            module_map: Default::default(),
            arguments: vec![Parameter::public(Variable::new(0))],
            return_count: 1,
            statements: vec![Statement::constraint(
                Variable::new(0),
                Variable::public(0),
                None,
            )],
            solvers: vec![],
        };

        let rng = &mut StdRng::from_entropy();
        let keypair = <Ark as NonUniversalBackend<Bw6_761Field, G16>>::setup(program.clone(), rng);
        let interpreter = Interpreter::default();

        let witness = interpreter
            .execute(
                &[Bw6_761Field::from(42)],
                program.statements.iter(),
                &program.arguments,
                &program.solvers,
            )
            .unwrap();

        let proof = <Ark as Backend<Bw6_761Field, G16>>::generate_proof(
            program,
            witness,
            keypair.pk.as_slice(),
            rng,
        );
        let ans = <Ark as Backend<Bw6_761Field, G16>>::verify(keypair.vk, proof);

        assert!(ans);
    }
}
