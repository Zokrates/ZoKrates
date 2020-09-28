use zexe_gm17::{
    prepare_verifying_key, verify_proof, Parameters, PreparedVerifyingKey, Proof as ZexeProof,
    VerifyingKey,
};

use algebra_core::serialize::{CanonicalDeserialize, CanonicalSerialize};
use zokrates_field::{
    Bls12_377Field, Bls12_381Field, Bn128Field, Bw6_761Field, Field, ZexeFieldExtensions,
};

use crate::ir;
use crate::proof_system::zexe::Computation;
use crate::proof_system::zexe::{parse_fr, parse_g1, parse_g2, parse_g2_fq};
use proof_system::solidity::SolidityAbi;
use proof_system::{G1Affine, G2Affine, G2AffineFq, Proof, ProofSystem, SetupKeypair, Fq2};

pub struct GM17 {}

pub trait NotBw6_761Field {}
impl NotBw6_761Field for Bls12_377Field {}
impl NotBw6_761Field for Bls12_381Field {}
impl NotBw6_761Field for Bn128Field {}

#[derive(Serialize, Deserialize)]
pub struct ProofPoints {
    a: G1Affine,
    b: G2Affine,
    c: G1Affine,
}

#[derive(Serialize, Deserialize)]
pub struct VerificationKey {
    h: G2Affine,
    g_alpha: G1Affine,
    h_beta: G2Affine,
    g_gamma: G1Affine,
    h_gamma: G2Affine,
    query: Vec<G1Affine>,
}

impl<T> ProofSystem<T> for GM17
where
    T: NotBw6_761Field + Field + ZexeFieldExtensions<FqeRepr = Fq2>,
{
    type VerificationKey = VerificationKey;
    type ProofPoints = ProofPoints;

    fn setup(program: ir::Prog<T>) -> SetupKeypair<Self::VerificationKey> {
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
        program: ir::Prog<T>,
        witness: ir::Witness<T>,
        proving_key: Vec<u8>,
    ) -> Proof<ProofPoints> {
        let computation = Computation::with_witness(program, witness);
        let params =
            Parameters::<<T as ZexeFieldExtensions>::ZexeEngine>::deserialize_uncompressed(
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

        Proof::<ProofPoints>::new(proof_points, inputs, None)
    }

    fn export_solidity_verifier(_vk: VerificationKey, _abi: SolidityAbi) -> String {
        unimplemented!()
    }

    fn verify(vk: VerificationKey, proof: Proof<ProofPoints>) -> bool {
        let vk = VerifyingKey {
            h_g2: serialization::to_g2::<T>(vk.h),
            g_alpha_g1: serialization::to_g1::<T>(vk.g_alpha),
            h_beta_g2: serialization::to_g2::<T>(vk.h_beta),
            g_gamma_g1: serialization::to_g1::<T>(vk.g_gamma),
            h_gamma_g2: serialization::to_g2::<T>(vk.h_gamma),
            query: vk
                .query
                .into_iter()
                .map(|g1| serialization::to_g1::<T>(g1))
                .collect(),
        };

        let zexe_proof = ZexeProof {
            a: serialization::to_g1::<T>(proof.proof.a),
            b: serialization::to_g2::<T>(proof.proof.b),
            c: serialization::to_g1::<T>(proof.proof.c),
        };

        let pvk: PreparedVerifyingKey<<T as ZexeFieldExtensions>::ZexeEngine> =
            prepare_verifying_key(&vk);

        let public_inputs: Vec<_> = proof
            .inputs
            .iter()
            .map(|s| {
                T::try_from_str(s.trim_start_matches("0x"), 16)
                    .unwrap()
                    .into_zexe()
            })
            .collect::<Vec<_>>();

        verify_proof(&pvk, &zexe_proof, &public_inputs).unwrap()
    }
}

#[derive(Serialize, Deserialize)]
pub struct ProofPointsG2Fq {
    a: G1Affine,
    b: G2AffineFq,
    c: G1Affine,
}

#[derive(Serialize, Deserialize)]
pub struct VerificationKeyG2Fq {
    h: G2AffineFq,
    g_alpha: G1Affine,
    h_beta: G2AffineFq,
    g_gamma: G1Affine,
    h_gamma: G2AffineFq,
    query: Vec<G1Affine>,
}

impl ProofSystem<Bw6_761Field> for GM17 {
    type VerificationKey = VerificationKeyG2Fq;
    type ProofPoints = ProofPointsG2Fq;

    fn setup(program: ir::Prog<Bw6_761Field>) -> SetupKeypair<VerificationKeyG2Fq> {
        let parameters = Computation::without_witness(program).setup();

        let mut pk: Vec<u8> = Vec::new();
        parameters.serialize_uncompressed(&mut pk).unwrap();

        let vk = VerificationKeyG2Fq {
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
        program: ir::Prog<Bw6_761Field>,
        witness: ir::Witness<Bw6_761Field>,
        proving_key: Vec<u8>,
    ) -> Proof<ProofPointsG2Fq> {
        let computation = Computation::with_witness(program, witness);
        let params = Parameters::<<Bw6_761Field as ZexeFieldExtensions>::ZexeEngine>::deserialize_uncompressed(
            &mut proving_key.as_slice(),
        )
        .unwrap();

        let proof = computation.clone().prove(&params);
        let proof_points = ProofPointsG2Fq {
            a: parse_g1::<Bw6_761Field>(&proof.a),
            b: parse_g2_fq::<Bw6_761Field>(&proof.b),
            c: parse_g1::<Bw6_761Field>(&proof.c),
        };

        let inputs = computation
            .public_inputs_values()
            .iter()
            .map(parse_fr::<Bw6_761Field>)
            .collect::<Vec<_>>();

        Proof::<ProofPointsG2Fq>::new(proof_points, inputs, None)
    }

    fn export_solidity_verifier(_vk: VerificationKeyG2Fq, _abi: SolidityAbi) -> String {
        unimplemented!()
    }

    fn verify(vk: VerificationKeyG2Fq, proof: Proof<ProofPointsG2Fq>) -> bool {
        let vk = VerifyingKey {
            h_g2: serialization::to_g2_fq::<Bw6_761Field>(vk.h),
            g_alpha_g1: serialization::to_g1::<Bw6_761Field>(vk.g_alpha),
            h_beta_g2: serialization::to_g2_fq::<Bw6_761Field>(vk.h_beta),
            g_gamma_g1: serialization::to_g1::<Bw6_761Field>(vk.g_gamma),
            h_gamma_g2: serialization::to_g2_fq::<Bw6_761Field>(vk.h_gamma),
            query: vk
                .query
                .into_iter()
                .map(|g1| serialization::to_g1::<Bw6_761Field>(g1))
                .collect(),
        };

        let zexe_proof = ZexeProof {
            a: serialization::to_g1::<Bw6_761Field>(proof.proof.a),
            b: serialization::to_g2_fq::<Bw6_761Field>(proof.proof.b),
            c: serialization::to_g1::<Bw6_761Field>(proof.proof.c),
        };

        let pvk: PreparedVerifyingKey<<Bw6_761Field as ZexeFieldExtensions>::ZexeEngine> =
            prepare_verifying_key(&vk);

        let public_inputs: Vec<_> = proof
            .inputs
            .iter()
            .map(|s| {
                Bw6_761Field::try_from_str(s.trim_start_matches("0x"), 16)
                    .expect(format!("Invalid {} value: {}", Bw6_761Field::name(), s).as_str())
                    .into_zexe()
            })
            .collect::<Vec<_>>();

        verify_proof(&pvk, &zexe_proof, &public_inputs).unwrap()
    }
}

pub mod serialization {
    use algebra_core::{AffineCurve, PairingEngine};
    use num_bigint::BigUint;
    use proof_system::{G1Affine, G2Affine, G2AffineFq, Fq2, Fq};
    use std::str::FromStr;
    use zokrates_field::ZexeFieldExtensions;

    fn to_dec_string(s: String) -> String {
        BigUint::from_bytes_be(
            hex::decode(s.strip_prefix("0x").unwrap())
                .unwrap()
                .as_slice(),
        )
        .to_str_radix(10)
    }

    pub fn to_g1<T: ZexeFieldExtensions>(
        g1: G1Affine,
    ) -> <T::ZexeEngine as PairingEngine>::G1Affine {
        let x = <T::ZexeEngine as PairingEngine>::Fq::from_str(to_dec_string(g1.0).as_str())
            .map_err(|_| ())
            .unwrap();

        let y = <T::ZexeEngine as PairingEngine>::Fq::from_str(to_dec_string(g1.1).as_str())
            .map_err(|_| ())
            .unwrap();

        <T::ZexeEngine as PairingEngine>::G1Affine::from_xy_checked(x, y).unwrap()
    }

    pub fn to_g2<T: ZexeFieldExtensions<FqeRepr = Fq2>>(
        g2: G2Affine,
    ) -> <T::ZexeEngine as PairingEngine>::G2Affine {
        let x = T::new_fqe((to_dec_string((g2.0).0), to_dec_string((g2.0).1)));
        let y = T::new_fqe((to_dec_string((g2.1).0), to_dec_string((g2.1).1)));
        <T::ZexeEngine as PairingEngine>::G2Affine::from_xy_checked(x, y).unwrap()
    }

    pub fn to_g2_fq<T: ZexeFieldExtensions<FqeRepr = Fq>>(
        g2: G2AffineFq,
    ) -> <T::ZexeEngine as PairingEngine>::G2Affine {
        let x = T::new_fqe(to_dec_string(g2.0));
        let y = T::new_fqe(to_dec_string(g2.1));
        <T::ZexeEngine as PairingEngine>::G2Affine::from_xy_checked(x, y).unwrap()
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

        let keypair = GM17::setup(program.clone());
        let interpreter = Interpreter::default();

        let witness = interpreter
            .execute(&program, &vec![Bls12_377Field::from(42)])
            .unwrap();

        let proof = GM17::generate_proof(program, witness, keypair.pk);
        let ans = <GM17 as ProofSystem<Bls12_377Field>>::verify(keypair.vk, proof);

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

        let keypair = GM17::setup(program.clone());
        let interpreter = Interpreter::default();

        let witness = interpreter
            .execute(&program, &vec![Bw6_761Field::from(42)])
            .unwrap();

        let proof = GM17::generate_proof(program, witness, keypair.pk);
        let ans = <GM17 as ProofSystem<Bw6_761Field>>::verify(keypair.vk, proof);

        assert!(ans);
    }
}
