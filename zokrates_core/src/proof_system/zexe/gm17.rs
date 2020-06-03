use zexe_gm17::{
    prepare_verifying_key, verify_proof, Parameters, PreparedVerifyingKey, Proof as ZexeProof,
    VerifyingKey,
};

use zokrates_field::{Field, ZexeFieldExtensions};

use crate::ir;
use crate::proof_system::zexe::Computation;
use crate::proof_system::zexe::{parse_fr, parse_g1, parse_g2};
use proof_system::{G1Affine, G2Affine, Proof, ProofSystem, SetupKeypair, SolidityAbi};

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

impl<T: Field + ZexeFieldExtensions> ProofSystem<T> for GM17 {
    type VerificationKey = VerificationKey;
    type ProofPoints = ProofPoints;

    fn setup(program: ir::Prog<T>) -> SetupKeypair<VerificationKey> {
        let parameters = Computation::without_witness(program).setup();

        let mut pk: Vec<u8> = Vec::new();
        let mut vk_raw: Vec<u8> = Vec::new();

        // TODO: implement parameters serialization, this will panic atm
        parameters.write(&mut pk).unwrap();

        // TODO: same here as above
        parameters.vk.write(&mut vk_raw).unwrap();

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
            raw: hex::encode(vk_raw),
        };

        SetupKeypair::new(vk, pk)
    }

    fn generate_proof(
        program: ir::Prog<T>,
        witness: ir::Witness<T>,
        proving_key: Vec<u8>,
    ) -> Proof<ProofPoints> {
        let computation = Computation::with_witness(program, witness);
        let params = Parameters::read(proving_key.as_slice(), true).unwrap();

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

        let mut raw: Vec<u8> = Vec::new();
        proof.write(&mut raw).unwrap();

        Proof::<ProofPoints>::new(proof_points, inputs, hex::encode(&raw))
    }

    fn export_solidity_verifier(_vk: VerificationKey, _abi: SolidityAbi) -> String {
        unimplemented!()
    }

    fn verify(vk: VerificationKey, proof: Proof<ProofPoints>) -> bool {
        let vk_raw = hex::decode(vk.raw.clone()).unwrap();
        let proof_raw = hex::decode(proof.raw.clone()).unwrap();

        let vk: VerifyingKey<T::ZexeEngine> = VerifyingKey::read(vk_raw.as_slice()).unwrap();
        let pvk: PreparedVerifyingKey<T::ZexeEngine> = prepare_verifying_key(&vk);

        let zexe_proof: ZexeProof<T::ZexeEngine> = ZexeProof::read(proof_raw.as_slice()).unwrap();

        let public_inputs: Vec<_> = proof
            .inputs
            .iter()
            .map(|s| {
                T::try_from_str(s.trim_start_matches("0x"), 16)
                    .expect(format!("Invalid {} value: {}", T::name(), s).as_str())
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
