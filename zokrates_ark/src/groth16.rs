use ark_crypto_primitives::SNARK;
use ark_groth16::{
    prepare_verifying_key, verify_proof, Groth16, PreparedVerifyingKey, Proof as ArkProof,
    ProvingKey, VerifyingKey,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use zokrates_field::ArkFieldExtensions;
use zokrates_field::Field;
use zokrates_proof_systems::{Backend, NonUniversalBackend, Proof, SetupKeypair};

use crate::Computation;
use crate::{parse_fr, serialization, Ark};
use crate::{parse_g1, parse_g2};
use rand_0_8::{rngs::StdRng, SeedableRng};
use zokrates_ast::ir::{ProgIterator, Statement, Witness};
use zokrates_proof_systems::groth16::{ProofPoints, VerificationKey, G16};
use zokrates_proof_systems::Scheme;

const G16_WARNING: &str = "WARNING: You are using the G16 scheme which is subject to malleability. See zokrates.github.io/toolbox/proving_schemes.html#g16-malleability for implications.";

impl<T: Field + ArkFieldExtensions> Backend<T, G16> for Ark {
    fn generate_proof<I: IntoIterator<Item = Statement<T>>>(
        program: ProgIterator<T, I>,
        witness: Witness<T>,
        proving_key: Vec<u8>,
    ) -> Proof<T, G16> {
        println!("{}", G16_WARNING);

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

        let rng = &mut StdRng::from_entropy();
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
    fn setup<I: IntoIterator<Item = Statement<T>>>(
        program: ProgIterator<T, I>,
    ) -> SetupKeypair<T, G16> {
        println!("{}", G16_WARNING);

        let computation = Computation::without_witness(program);

        let rng = &mut StdRng::from_entropy();
        let (pk, vk) = Groth16::<T::ArkEngine>::circuit_specific_setup(computation, rng).unwrap();

        let mut pk_vec: Vec<u8> = Vec::new();
        pk.serialize_uncompressed(&mut pk_vec).unwrap();

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
    use zokrates_ast::flat::{Parameter, Variable};
    use zokrates_ast::ir::{Prog, Statement};
    use zokrates_interpreter::Interpreter;

    use super::*;
    use zokrates_field::{Bls12_377Field, Bw6_761Field};

    #[test]
    fn verify_bls12_377_field() {
        let program: Prog<Bls12_377Field> = Prog {
            arguments: vec![Parameter::public(Variable::new(0))],
            return_count: 1,
            statements: vec![Statement::constraint(Variable::new(0), Variable::public(0))],
        };

        let keypair = <Ark as NonUniversalBackend<Bls12_377Field, G16>>::setup(program.clone());
        let interpreter = Interpreter::default();

        let witness = interpreter
            .execute(program.clone(), &[Bls12_377Field::from(42)])
            .unwrap();

        let proof =
            <Ark as Backend<Bls12_377Field, G16>>::generate_proof(program, witness, keypair.pk);
        let ans = <Ark as Backend<Bls12_377Field, G16>>::verify(keypair.vk, proof);

        assert!(ans);
    }

    #[test]
    fn verify_bw6_761_field() {
        let program: Prog<Bw6_761Field> = Prog {
            arguments: vec![Parameter::public(Variable::new(0))],
            return_count: 1,
            statements: vec![Statement::constraint(Variable::new(0), Variable::public(0))],
        };

        let keypair = <Ark as NonUniversalBackend<Bw6_761Field, G16>>::setup(program.clone());
        let interpreter = Interpreter::default();

        let witness = interpreter
            .execute(program.clone(), &[Bw6_761Field::from(42)])
            .unwrap();

        let proof =
            <Ark as Backend<Bw6_761Field, G16>>::generate_proof(program, witness, keypair.pk);
        let ans = <Ark as Backend<Bw6_761Field, G16>>::verify(keypair.vk, proof);

        assert!(ans);
    }
}
