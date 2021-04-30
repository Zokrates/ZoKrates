use ark_marlin::{IndexProverKey, IndexVerifierKey, Proof as ArkProof};

use ark_marlin::Marlin;

use ark_ec::PairingEngine;
use ark_ff::{PrimeField, UniformRand};
use ark_poly::univariate::DensePolynomial;
use ark_poly_commit::marlin_pc::MarlinKZG10;
use ark_relations::{
    lc,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError},
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use sha2::Sha256;

use zokrates_field::{ArkFieldExtensions, Bw6_761Field, Field};

use crate::ir::{Prog, Witness};
use crate::proof_system::ark::Ark;
use crate::proof_system::ark::Computation;
use crate::proof_system::ark::{parse_fr, parse_g1, parse_g2, parse_g2_fq};
use crate::proof_system::marlin::{self, NotBw6_761Field, ProofPoints, VerificationKey};
use crate::proof_system::Scheme;
use crate::proof_system::{Backend, Proof, SetupKeypair};

impl<T: Field + ArkFieldExtensions + NotBw6_761Field> Backend<T, marlin::Marlin> for Ark {
    fn setup(program: Prog<T>) -> SetupKeypair<<marlin::Marlin as Scheme<T>>::VerificationKey> {
        let computation = Computation::without_witness(program);

        use rand_0_7::SeedableRng;

        let rng = &mut rand_0_7::rngs::StdRng::from_entropy();

        println!("setup not found, creating local srs");

        let srs = Marlin::<
            <<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr,
            MarlinKZG10<
                T::ArkEngine,
                DensePolynomial<<<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr>,
            >,
            Sha256,
        >::universal_setup(2usize.pow(21), 2usize.pow(21), 2usize.pow(21), rng)
        .unwrap();

        println!("srs done!");

        use ark_poly_commit::PCUniversalParams;

        println!("srs max degree: {}", srs.max_degree());
        println!(
            "computation constraint count {}",
            computation.program.constraint_count()
        );

        let (pk, vk) = Marlin::<
            <<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr,
            MarlinKZG10<
                T::ArkEngine,
                DensePolynomial<<<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr>,
            >,
            Sha256,
        >::index(&srs, computation)
        .unwrap();

        println!("srs specialized for dummy circuit!");

        //let parameters = Computation::without_witness(program).setup();

        let mut serialized_pk: Vec<u8> = Vec::new();
        pk.serialize_uncompressed(&mut serialized_pk).unwrap();

        let mut serialized_vk: Vec<u8> = Vec::new();
        vk.serialize_uncompressed(&mut serialized_vk).unwrap();

        SetupKeypair::new(VerificationKey { raw: serialized_vk }, serialized_pk)
    }

    fn generate_proof(
        program: Prog<T>,
        witness: Witness<T>,
        proving_key: Vec<u8>,
    ) -> Proof<<marlin::Marlin as Scheme<T>>::ProofPoints> {
        let computation = Computation::with_witness(program, witness);

        use rand_0_7::SeedableRng;

        let rng = &mut rand_0_7::rngs::StdRng::from_entropy();

        let pk = IndexProverKey::<
            <<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr,
            MarlinKZG10<
                T::ArkEngine,
                DensePolynomial<<<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr>,
            >,
        >::deserialize_uncompressed(&mut proving_key.as_slice())
        .unwrap();

        let inputs = computation
            .public_inputs_values()
            .iter()
            .map(parse_fr::<T>)
            .collect::<Vec<_>>();

        let proof = Marlin::<
            <<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr,
            MarlinKZG10<
                T::ArkEngine,
                DensePolynomial<<<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr>,
            >,
            Sha256,
        >::prove(&pk, computation, rng)
        .unwrap();

        let mut serialized_proof: Vec<u8> = Vec::new();
        proof.serialize_uncompressed(&mut serialized_proof).unwrap();

        Proof::new(
            ProofPoints {
                raw: serialized_proof,
            },
            inputs,
        )
    }

    fn verify(
        vk: <marlin::Marlin as Scheme<T>>::VerificationKey,
        proof: Proof<<marlin::Marlin as Scheme<T>>::ProofPoints>,
    ) -> bool {
        let inputs: Vec<_> = proof
            .inputs
            .iter()
            .map(|s| {
                T::try_from_str(s.trim_start_matches("0x"), 16)
                    .unwrap()
                    .into_ark()
            })
            .collect::<Vec<_>>();

        let proof = ArkProof::<
            <<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr,
            MarlinKZG10<
                T::ArkEngine,
                DensePolynomial<<<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr>,
            >,
        >::deserialize_uncompressed(&mut proof.proof.raw.as_slice())
        .unwrap();

        let vk = IndexVerifierKey::<
            <<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr,
            MarlinKZG10<
                T::ArkEngine,
                DensePolynomial<<<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr>,
            >,
        >::deserialize_uncompressed(&mut vk.raw.as_slice())
        .unwrap();

        use rand_0_7::SeedableRng;

        let rng = &mut rand_0_7::rngs::StdRng::from_entropy();

        Marlin::<
            <<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr,
            MarlinKZG10<
                T::ArkEngine,
                DensePolynomial<<<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr>,
            >,
            Sha256,
        >::verify(&vk, &inputs, &proof, rng)
        .unwrap()
    }
}

impl Backend<Bw6_761Field, marlin::Marlin> for Ark {
    fn setup(
        program: Prog<Bw6_761Field>,
    ) -> SetupKeypair<<marlin::Marlin as Scheme<Bw6_761Field>>::VerificationKey> {
        unimplemented!();

        // let parameters = Computation::without_witness(program).setup();

        //         let mut pk: Vec<u8> = Vec::new();
        //         parameters.serialize_uncompressed(&mut pk).unwrap();

        //         let vk = VerificationKey {
        //             h: parse_g2_fq::<Bw6_761Field>(&parameters.vk.h_g2),
        //             g_alpha: parse_g1::<Bw6_761Field>(&parameters.vk.g_alpha_g1),
        //             h_beta: parse_g2_fq::<Bw6_761Field>(&parameters.vk.h_beta_g2),
        //             g_gamma: parse_g1::<Bw6_761Field>(&parameters.vk.g_gamma_g1),
        //             h_gamma: parse_g2_fq::<Bw6_761Field>(&parameters.vk.h_gamma_g2),
        //             query: parameters
        //                 .vk
        //                 .query
        //                 .iter()
        //                 .map(|g1| parse_g1::<Bw6_761Field>(g1))
        //                 .collect(),
        //         };

        //         SetupKeypair::new(vk, pk)
    }

    fn generate_proof(
        program: Prog<Bw6_761Field>,
        witness: Witness<Bw6_761Field>,
        proving_key: Vec<u8>,
    ) -> Proof<<marlin::Marlin as Scheme<Bw6_761Field>>::ProofPoints> {
        unimplemented!();

        // let computation = Computation::with_witness(program, witness);
        // let params =
        //     ProvingKey::<<Bw6_761Field as ArkFieldExtensions>::ArkEngine>::deserialize_uncompressed(
        //         &mut proving_key.as_slice(),
        //     )
        //         .unwrap();

        // let proof = computation.clone().prove(&params);
        // let proof_points = ProofPoints {
        //     a: parse_g1::<Bw6_761Field>(&proof.a),
        //     b: parse_g2_fq::<Bw6_761Field>(&proof.b),
        //     c: parse_g1::<Bw6_761Field>(&proof.c),
        // };

        // let inputs = computation
        //     .public_inputs_values()
        //     .iter()
        //     .map(parse_fr::<Bw6_761Field>)
        //     .collect::<Vec<_>>();

        // Proof::new(proof_points, inputs)
    }

    fn verify(
        vk: <marlin::Marlin as Scheme<Bw6_761Field>>::VerificationKey,
        proof: Proof<<marlin::Marlin as Scheme<Bw6_761Field>>::ProofPoints>,
    ) -> bool {
        unimplemented!();

        // let vk = VerifyingKey {
        //     h_g2: serialization::to_g2_fq::<Bw6_761Field>(vk.h),
        //     g_alpha_g1: serialization::to_g1::<Bw6_761Field>(vk.g_alpha),
        //     h_beta_g2: serialization::to_g2_fq::<Bw6_761Field>(vk.h_beta),
        //     g_gamma_g1: serialization::to_g1::<Bw6_761Field>(vk.g_gamma),
        //     h_gamma_g2: serialization::to_g2_fq::<Bw6_761Field>(vk.h_gamma),
        //     query: vk
        //         .query
        //         .into_iter()
        //         .map(serialization::to_g1::<Bw6_761Field>)
        //         .collect(),
        // };

        // let ark_proof = ArkProof {
        //     a: serialization::to_g1::<Bw6_761Field>(proof.proof.a),
        //     b: serialization::to_g2_fq::<Bw6_761Field>(proof.proof.b),
        //     c: serialization::to_g1::<Bw6_761Field>(proof.proof.c),
        // };

        // let pvk: PreparedVerifyingKey<<Bw6_761Field as ArkFieldExtensions>::ArkEngine> =
        //     prepare_verifying_key(&vk);

        // let public_inputs: Vec<_> = proof
        //     .inputs
        //     .iter()
        //     .map(|s| {
        //         Bw6_761Field::try_from_str(s.trim_start_matches("0x"), 16)
        //             .unwrap()
        //             .into_ark()
        //     })
        //     .collect::<Vec<_>>();

        // verify_proof(&pvk, &ark_proof, &public_inputs).unwrap()
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

        let keypair = <Ark as Backend<Bls12_377Field, Marlin>>::setup(program.clone());
        let interpreter = Interpreter::default();

        let witness = interpreter
            .execute(&program, &[Bls12_377Field::from(42)])
            .unwrap();

        let proof =
            <Ark as Backend<Bls12_377Field, Marlin>>::generate_proof(program, witness, keypair.pk);
        let ans = <Ark as Backend<Bls12_377Field, Marlin>>::verify(keypair.vk, proof);

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

        let keypair = <Ark as Backend<Bw6_761Field, Marlin>>::setup(program.clone());
        let interpreter = Interpreter::default();

        let witness = interpreter
            .execute(&program, &[Bw6_761Field::from(42)])
            .unwrap();

        let proof =
            <Ark as Backend<Bw6_761Field, Marlin>>::generate_proof(program, witness, keypair.pk);
        let ans = <Ark as Backend<Bw6_761Field, Marlin>>::verify(keypair.vk, proof);

        assert!(ans);
    }
}
