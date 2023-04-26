use bellman::groth16::{
    prepare_verifying_key, verify_proof, Parameters, PreparedVerifyingKey, Proof as BellmanProof,
    VerifyingKey,
};
use pairing::{ff::to_hex, CurveAffine, Engine};

use zokrates_field::BellmanFieldExtensions;
use zokrates_field::Field;
use zokrates_proof_systems::{Backend, MpcBackend, NonUniversalBackend, Proof, SetupKeypair};

use crate::Computation;
use crate::{get_random_seed, Bellman};
use crate::{parse_g1, parse_g2};
use phase2::MPCParameters;
use rand_0_4::{ChaChaRng, SeedableRng};
use rand_0_8::{CryptoRng, RngCore};
use std::io::{Read, Write};
use zokrates_ast::ir::{ProgIterator, Statement, Witness};
use zokrates_proof_systems::groth16::{ProofPoints, VerificationKey, G16};
use zokrates_proof_systems::Scheme;

impl<T: Field + BellmanFieldExtensions> Backend<T, G16> for Bellman {
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
        let params = Parameters::read(proving_key, true).unwrap();

        let public_inputs: Vec<String> = computation
            .public_inputs_values()
            .iter()
            .map(|e| format!("0x{}", to_hex(e)))
            .collect();

        let proof = computation.prove(&params, rng);
        let proof_points = ProofPoints {
            a: parse_g1::<T>(&proof.a),
            b: parse_g2::<T>(&proof.b),
            c: parse_g1::<T>(&proof.c),
        };

        Proof::new(proof_points, public_inputs)
    }

    fn verify(vk: <G16 as Scheme<T>>::VerificationKey, proof: Proof<T, G16>) -> bool {
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

impl<T: Field + BellmanFieldExtensions> NonUniversalBackend<T, G16> for Bellman {
    fn setup<'a, I: IntoIterator<Item = Statement<'a, T>>, R: RngCore + CryptoRng>(
        program: ProgIterator<'a, T, I>,
        rng: &mut R,
    ) -> SetupKeypair<T, G16> {
        let parameters = Computation::without_witness(program).setup(rng);
        let mut pk: Vec<u8> = Vec::new();
        parameters.write(&mut pk).unwrap();

        let vk = serialization::parameters_to_verification_key::<T>(&parameters);
        SetupKeypair::new(vk, pk)
    }
}

impl<T: Field + BellmanFieldExtensions> MpcBackend<T, G16> for Bellman {
    fn initialize<'a, R: Read, W: Write, I: IntoIterator<Item = Statement<'a, T>>>(
        program: ProgIterator<'a, T, I>,
        phase1_radix: &mut R,
        output: &mut W,
    ) -> Result<(), String> {
        let circuit = Computation::without_witness(program);
        let params = MPCParameters::new(circuit, phase1_radix).map_err(|e| e.to_string())?;
        params.write(output).map_err(|e| e.to_string())?;
        Ok(())
    }

    fn contribute<R: Read, W: Write, G: RngCore + CryptoRng>(
        params: R,
        rng: &mut G,
        output: &mut W,
    ) -> Result<[u8; 64], String> {
        let mut params =
            MPCParameters::<T::BellmanEngine>::read(params, true).map_err(|e| e.to_string())?;

        let seed = get_random_seed(rng);
        let rng = &mut ChaChaRng::from_seed(seed.as_ref());

        let hash = params.contribute(rng);
        params.write(output).map_err(|e| e.to_string())?;

        Ok(hash)
    }

    fn verify<'a, R: Read, I: IntoIterator<Item = Statement<'a, T>>>(
        params: R,
        program: ProgIterator<'a, T, I>,
        phase1_radix: &mut R,
    ) -> Result<Vec<[u8; 64]>, String> {
        let params =
            MPCParameters::<T::BellmanEngine>::read(params, true).map_err(|e| e.to_string())?;

        let circuit = Computation::without_witness(program);
        let hashes = params
            .verify(circuit, phase1_radix)
            .map_err(|_| "parameters malformed".to_string())?;

        Ok(hashes)
    }

    fn export_keypair<R: Read>(params: R) -> Result<SetupKeypair<T, G16>, String> {
        let params =
            MPCParameters::<T::BellmanEngine>::read(params, true).map_err(|e| e.to_string())?;

        let params = params.get_params();
        let mut pk: Vec<u8> = Vec::new();
        params.write(&mut pk).map_err(|e| e.to_string())?;

        let vk = serialization::parameters_to_verification_key::<T>(params);
        Ok(SetupKeypair::new(vk, pk))
    }
}

pub mod serialization {
    use super::*;
    use pairing::from_hex;
    use zokrates_proof_systems::{G1Affine, G2Affine};

    pub fn parameters_to_verification_key<T: Field + BellmanFieldExtensions>(
        parameters: &Parameters<T::BellmanEngine>,
    ) -> VerificationKey<G1Affine, G2Affine> {
        VerificationKey {
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
        }
    }

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
        match g2 {
            G2Affine::Fq2(g2) => {
                let x = T::new_fq2(&(g2.0).0, &(g2.0).1);
                let y = T::new_fq2(&(g2.1).0, &(g2.1).1);
                <T::BellmanEngine as Engine>::G2Affine::from_xy_unchecked(x, y)
            }
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use rand_0_8::rngs::StdRng;
    use rand_0_8::SeedableRng;
    use zokrates_field::Bn128Field;
    use zokrates_interpreter::Interpreter;

    use super::*;
    use zokrates_ast::common::flat::Parameter;
    use zokrates_ast::ir::{Prog, Statement, Variable};

    #[test]
    fn verify() {
        let program: Prog<Bn128Field> = Prog {
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
            <Bellman as NonUniversalBackend<Bn128Field, G16>>::setup(program.clone(), rng);
        let interpreter = Interpreter::default();

        let witness = interpreter
            .execute(
                &[Bn128Field::from(42)],
                program.statements.iter(),
                &program.arguments,
                &program.solvers,
            )
            .unwrap();

        let proof = <Bellman as Backend<Bn128Field, G16>>::generate_proof(
            program,
            witness,
            keypair.pk.as_slice(),
            rng,
        );
        let ans = <Bellman as Backend<Bn128Field, G16>>::verify(keypair.vk, proof);

        assert!(ans);
    }
}
