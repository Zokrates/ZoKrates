use zexe_gm17::{
    prepare_verifying_key, verify_proof, Parameters, PreparedVerifyingKey, Proof as ZexeProof,
    VerifyingKey,
};

use zokrates_field::{Bls12_377Field, Bw6_761Field, Field, ZexeFieldExtensions};

use algebra_core::serialize::{CanonicalDeserialize, CanonicalSerialize};

use crate::ir;
use crate::proof_system::zexe::Computation;
use crate::proof_system::zexe::{parse_fr, parse_g1, parse_g2, parse_g2_fq};
use proof_system::{
    G1Affine, G2Affine, G2affineG2Fq, Proof, ProofSystem, SetupKeypair, SolidityAbi,
};

pub struct GM17 {}

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
    raw: String,
}

#[derive(Serialize, Deserialize)]
pub struct ProofPointsG2Fq {
    a: G1Affine,
    b: G2affineG2Fq,
    c: G1Affine,
}

#[derive(Serialize, Deserialize)]
pub struct VerificationKeyG2Fq {
    h: G2affineG2Fq,
    g_alpha: G1Affine,
    h_beta: G2affineG2Fq,
    g_gamma: G1Affine,
    h_gamma: G2affineG2Fq,
    query: Vec<G1Affine>,
    raw: String,
}

impl ProofSystem<Bw6_761Field> for GM17 {
    type VerificationKey = VerificationKeyG2Fq;
    type ProofPoints = ProofPointsG2Fq;

    fn setup(program: ir::Prog<Bw6_761Field>) -> SetupKeypair<VerificationKeyG2Fq> {
        let parameters = Computation::without_witness(program).setup();

        let mut pk: Vec<u8> = Vec::new();
        let mut vk_raw: Vec<u8> = Vec::new();

        // parameters.write(&mut pk).unwrap();
        parameters.serialize_uncompressed(&mut pk).unwrap();
        parameters.vk.serialize_uncompressed(&mut vk_raw).unwrap();

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
            raw: hex::encode(vk_raw),
        };

        SetupKeypair::new(vk, pk)
    }

    fn generate_proof(
        program: ir::Prog<Bw6_761Field>,
        witness: ir::Witness<Bw6_761Field>,
        proving_key: Vec<u8>,
    ) -> Proof<ProofPointsG2Fq> {
        let computation = Computation::with_witness(program, witness);
        // let params = Parameters::<Bw6_761Field::ZexeEngine>::deserialize_uncompressed(
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

        let mut raw: Vec<u8> = Vec::new();
        proof.serialize_uncompressed(&mut raw).unwrap();

        Proof::<ProofPointsG2Fq>::new(proof_points, inputs, hex::encode(&raw))
    }

    fn export_solidity_verifier(_vk: VerificationKeyG2Fq, _abi: SolidityAbi) -> String {
        unimplemented!()
    }

    fn verify(vk: VerificationKeyG2Fq, proof: Proof<ProofPointsG2Fq>) -> bool {
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
                    .expect(format!("Invalid {} value: {}", Bw6_761Field::name(), s).as_str())
                    .into_zexe()
            })
            .collect::<Vec<_>>();

        verify_proof(&pvk, &zexe_proof, &public_inputs).unwrap()
    }
}

impl ProofSystem<Bls12_377Field> for GM17 {
    type VerificationKey = VerificationKey;
    type ProofPoints = ProofPoints;

    fn setup(program: ir::Prog<Bls12_377Field>) -> SetupKeypair<VerificationKey> {
        let parameters = Computation::without_witness(program).setup();

        let mut pk: Vec<u8> = Vec::new();
        let mut vk_raw: Vec<u8> = Vec::new();

        // parameters.write(&mut pk).unwrap();
        parameters.serialize_uncompressed(&mut pk).unwrap();
        parameters.vk.serialize_uncompressed(&mut vk_raw).unwrap();

        let vk = VerificationKey {
            h: parse_g2::<Bls12_377Field>(&parameters.vk.h_g2),
            g_alpha: parse_g1::<Bls12_377Field>(&parameters.vk.g_alpha_g1),
            h_beta: parse_g2::<Bls12_377Field>(&parameters.vk.h_beta_g2),
            g_gamma: parse_g1::<Bls12_377Field>(&parameters.vk.g_gamma_g1),
            h_gamma: parse_g2::<Bls12_377Field>(&parameters.vk.h_gamma_g2),
            query: parameters
                .vk
                .query
                .iter()
                .map(|g1| parse_g1::<Bls12_377Field>(g1))
                .collect(),
            raw: hex::encode(vk_raw),
        };

        SetupKeypair::new(vk, pk)
    }

    fn generate_proof(
        program: ir::Prog<Bls12_377Field>,
        witness: ir::Witness<Bls12_377Field>,
        proving_key: Vec<u8>,
    ) -> Proof<ProofPoints> {
        let computation = Computation::with_witness(program, witness);
        let params = Parameters::<<Bls12_377Field as ZexeFieldExtensions>::ZexeEngine>::deserialize_uncompressed(
            &mut proving_key.as_slice(),
        )
        .unwrap();

        let proof = computation.clone().prove(&params);

        let proof_points = ProofPoints {
            a: parse_g1::<Bls12_377Field>(&proof.a),
            b: parse_g2::<Bls12_377Field>(&proof.b),
            c: parse_g1::<Bls12_377Field>(&proof.c),
        };

        let inputs = computation
            .public_inputs_values()
            .iter()
            .map(parse_fr::<Bls12_377Field>)
            .collect::<Vec<_>>();

        let mut raw: Vec<u8> = Vec::new();
        proof.serialize_uncompressed(&mut raw).unwrap();

        Proof::<ProofPoints>::new(proof_points, inputs, hex::encode(&raw))
    }

    fn export_solidity_verifier(_vk: VerificationKey, _abi: SolidityAbi) -> String {
        unimplemented!()
    }

    fn verify(vk: VerificationKey, proof: Proof<ProofPoints>) -> bool {
        let vk_raw = hex::decode(vk.raw.clone()).unwrap();
        let proof_raw = hex::decode(proof.raw.clone()).unwrap();

        let vk: VerifyingKey<<Bls12_377Field as ZexeFieldExtensions>::ZexeEngine> =
            VerifyingKey::deserialize_uncompressed(&mut vk_raw.as_slice()).unwrap();

        let pvk: PreparedVerifyingKey<<Bls12_377Field as ZexeFieldExtensions>::ZexeEngine> =
            prepare_verifying_key(&vk);

        let zexe_proof: ZexeProof<<Bls12_377Field as ZexeFieldExtensions>::ZexeEngine> =
            ZexeProof::deserialize_uncompressed(&mut proof_raw.as_slice()).unwrap();

        let public_inputs: Vec<_> = proof
            .inputs
            .iter()
            .map(|s| {
                Bls12_377Field::try_from_str(s.trim_start_matches("0x"), 16)
                    .expect(format!("Invalid {} value: {}", Bls12_377Field::name(), s).as_str())
                    .into_zexe()
            })
            .collect::<Vec<_>>();

        verify_proof(&pvk, &zexe_proof, &public_inputs).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use crate::flat_absy::FlatVariable;
    use crate::ir::{Function, Prog, Statement};

    use super::*;
    use zokrates_field::Bls12_377Field;

    #[test]
    fn verify() {
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
        let witness = program
            .clone()
            .execute(&vec![Bls12_377Field::from(42)])
            .unwrap();

        let proof = GM17::generate_proof(program.clone(), witness, keypair.pk);
        let ans = <GM17 as ProofSystem<Bls12_377Field>>::verify(keypair.vk, proof);

        assert!(ans);
    }
}
