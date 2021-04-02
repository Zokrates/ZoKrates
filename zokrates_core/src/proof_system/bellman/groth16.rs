use bellman::groth16::{
    prepare_verifying_key, verify_proof, Parameters, PreparedVerifyingKey, Proof as BellmanProof,
    VerifyingKey,
};
use pairing::{CurveAffine, Engine};

use crate::proof_system::{Backend, Proof, SetupKeypair};
use zokrates_field::BellmanFieldExtensions;
use zokrates_field::Field;

use crate::ir::{Prog, Witness};
use crate::proof_system::bellman::Bellman;
use crate::proof_system::bellman::Computation;
use crate::proof_system::bellman::{parse_fr, parse_g1, parse_g2};
use crate::proof_system::groth16::{ProofPoints, VerificationKey, G16};
use crate::proof_system::Scheme;

const G16_WARNING: &str = "WARNING: You are using the G16 scheme which is subject to malleability. See zokrates.github.io/toolbox/proving_schemes.html#g16-malleability for implications.";

impl<T: Field + BellmanFieldExtensions> Backend<T, G16> for Bellman {
    fn setup(program: Prog<T>) -> SetupKeypair<<G16 as Scheme<T>>::VerificationKey> {
        println!("{}", G16_WARNING);

        let parameters = Computation::without_witness(program).setup();
        let mut pk: Vec<u8> = Vec::new();
        parameters.write(&mut pk).unwrap();

        let vk = VerificationKey {
            alpha: parse_g1::<T>(&parameters.vk.alpha_g1),
            beta: parse_g2::<T>(&parameters.vk.beta_g2),
            gamma: parse_g2::<T>(&parameters.vk.gamma_g2),
            delta: parse_g2::<T>(&parameters.vk.delta_g2),
            gamma_abc: parameters
                .vk
                .ic
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
    ) -> Proof<<G16 as Scheme<T>>::ProofPoints> {
        println!("{}", G16_WARNING);

        let computation = Computation::with_witness(program, witness);
        let params = Parameters::read(proving_key.as_slice(), true).unwrap();

        let proof = computation.clone().prove(&params);
        let proof_points = ProofPoints {
            a: parse_g1::<T>(&proof.a),
            b: parse_g2::<T>(&proof.b),
            c: parse_g1::<T>(&proof.c),
        };

        let public_inputs: Vec<String> = computation
            .public_inputs_values()
            .iter()
            .map(parse_fr::<T>)
            .collect();

        Proof::new(proof_points, public_inputs)
    }

    fn verify(
        vk: <G16 as Scheme<T>>::VerificationKey,
        proof: Proof<<G16 as Scheme<T>>::ProofPoints>,
    ) -> bool {
        let vk = VerifyingKey {
            alpha_g1: serialization::to_g1::<T>(vk.alpha),
            beta_g1: <T::BellmanEngine as Engine>::G1Affine::one(), // not used during verification
            beta_g2: serialization::to_g2::<T>(vk.beta),
            gamma_g2: serialization::to_g2::<T>(vk.gamma),
            delta_g1: <T::BellmanEngine as Engine>::G1Affine::one(), // not used during verification
            delta_g2: serialization::to_g2::<T>(vk.delta),
            ic: vk
                .gamma_abc
                .into_iter()
                .map(serialization::to_g1::<T>)
                .collect(),
        };

        let pvk: PreparedVerifyingKey<T::BellmanEngine> = prepare_verifying_key(&vk);
        let bellman_proof = BellmanProof {
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
                    .into_bellman()
            })
            .collect::<Vec<_>>();

        verify_proof(&pvk, &bellman_proof, &public_inputs).unwrap()
    }
}

mod serialization {
    use pairing::{from_hex, CurveAffine, Engine};

    use crate::proof_system::{G1Affine, G2Affine};
    use zokrates_field::BellmanFieldExtensions;

    pub fn to_g1<T: BellmanFieldExtensions>(
        g1: G1Affine,
    ) -> <T::BellmanEngine as Engine>::G1Affine {
        <T::BellmanEngine as Engine>::G1Affine::from_xy_unchecked(
            from_hex(&g1.0).unwrap(),
            from_hex(&g1.1).unwrap(),
        )
    }
    pub fn to_g2<T: BellmanFieldExtensions>(
        g2: G2Affine,
    ) -> <T::BellmanEngine as Engine>::G2Affine {
        let x = T::new_fq2(&(g2.0).0, &(g2.0).1);
        let y = T::new_fq2(&(g2.1).0, &(g2.1).1);
        <T::BellmanEngine as Engine>::G2Affine::from_xy_unchecked(x, y)
    }
}

#[cfg(test)]
mod tests {
    use zokrates_field::Bn128Field;

    use super::*;
    use crate::flat_absy::FlatVariable;
    use crate::ir::{Function, Interpreter, Prog, Statement};

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
            private: vec![false],
        };

        let keypair = <Bellman as Backend<Bn128Field, G16>>::setup(program.clone());
        let interpreter = Interpreter::default();

        let witness = interpreter
            .execute(&program, &[Bn128Field::from(42)])
            .unwrap();

        let proof =
            <Bellman as Backend<Bn128Field, G16>>::generate_proof(program, witness, keypair.pk);
        let ans = <Bellman as Backend<Bn128Field, G16>>::verify(keypair.vk, proof);

        assert!(ans);
    }
}
