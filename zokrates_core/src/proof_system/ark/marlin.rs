use ark_marlin::{
    ahp::indexer::IndexInfo, ahp::prover::ProverMsg, IndexProverKey, IndexVerifierKey,
    Proof as ArkProof,
};

use ark_marlin::Marlin as ArkMarlin;

use ark_ec::PairingEngine;
use ark_poly::univariate::DensePolynomial;
use ark_poly_commit::{
    data_structures::BatchLCProof,
    kzg10::Commitment as KZG10Commitment,
    kzg10::Proof as KZG10Proof,
    kzg10::VerifierKey as KZG10VerifierKey,
    marlin_pc::{Commitment, MarlinKZG10, VerifierKey},
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use sha2::Sha256;
use rand_0_8::SeedableRng;

use zokrates_field::{ArkFieldExtensions, Field};

use crate::ir::{ProgIterator, Statement, Witness};
use crate::proof_system::ark::Ark;
use crate::proof_system::ark::Computation;
use crate::proof_system::ark::{parse_fr, parse_g1, parse_g2, serialization};
use crate::proof_system::marlin::{self, KZGVerifierKey, ProofPoints, VerificationKey};
use crate::proof_system::Scheme;
use crate::proof_system::{Backend, Proof, SetupKeypair, UniversalBackend};

const MINIMUM_CONSTRAINT_COUNT: usize = 2;

impl<T: Field + ArkFieldExtensions> UniversalBackend<T, marlin::Marlin> for Ark {
    fn universal_setup(size: u32) -> Vec<u8> {

        let rng = &mut rand_0_8::rngs::StdRng::from_entropy();

        let srs = ArkMarlin::<
            <<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr,
            MarlinKZG10<
                T::ArkEngine,
                DensePolynomial<<<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr>,
            >,
            Sha256,
        >::universal_setup(
            2usize.pow(size), 2usize.pow(size), 2usize.pow(size), rng
        )
        .unwrap();

        let mut res = vec![];

        srs.serialize(&mut res).unwrap();

        res
    }

    fn setup<I: IntoIterator<Item = Statement<T>>>(
        srs: Vec<u8>,
        program: ProgIterator<T, I>,
    ) -> Result<SetupKeypair<<marlin::Marlin as Scheme<T>>::VerificationKey>, String> {
        let program = program.collect();

        if program.constraint_count() < MINIMUM_CONSTRAINT_COUNT {
            return Err(format!("Programs must have a least {} constraints. This program is too small to generate a setup with Marlin, see [this issue](https://github.com/arkworks-rs/marlin/issues/79)", MINIMUM_CONSTRAINT_COUNT));
        }

        let computation = Computation::without_witness(program);

        let srs = ark_marlin::UniversalSRS::<
            <<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr,
            MarlinKZG10<
                T::ArkEngine,
                DensePolynomial<<<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr>,
            >,
        >::deserialize(&mut srs.as_slice())
        .unwrap();

        let (pk, vk) = ArkMarlin::<
            <<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr,
            MarlinKZG10<
                T::ArkEngine,
                DensePolynomial<<<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr>,
            >,
            Sha256,
        >::index(&srs, computation)
        .map_err(|e| match e {
            ark_marlin::Error::IndexTooLarge => String::from("The universal setup is too small for this program, please provide a larger universal setup"),
            _ => String::from("Unknown error specializing the universal setup for this program")
        })?;

        let mut serialized_pk: Vec<u8> = Vec::new();
        pk.serialize_uncompressed(&mut serialized_pk).unwrap();

        Ok(SetupKeypair::new(
            VerificationKey {
                index_comms: vk
                    .index_comms
                    .into_iter()
                    .map(|c| (parse_g1::<T>(&c.comm.0), None))
                    .collect(),
                num_constraints: vk.index_info.num_constraints,
                num_non_zero: vk.index_info.num_non_zero,
                num_instance_variables: vk.index_info.num_instance_variables,
                num_variables: vk.index_info.num_variables,
                vk: KZGVerifierKey {
                    g: parse_g1::<T>(&vk.verifier_key.vk.g),
                    gamma_g: parse_g1::<T>(&vk.verifier_key.vk.gamma_g),
                    h: parse_g2::<T>(&vk.verifier_key.vk.h),
                    beta_h: parse_g2::<T>(&vk.verifier_key.vk.beta_h),
                },
                max_degree: vk.verifier_key.max_degree,
                supported_degree: vk.verifier_key.supported_degree,
                degree_bounds_and_shift_powers: vk.verifier_key.degree_bounds_and_shift_powers.map(
                    |vk| {
                        vk.into_iter()
                            .map(|(bound, pow)| (bound, parse_g1::<T>(&pow)))
                            .collect()
                    },
                ),
            },
            serialized_pk,
        ))
    }
}

impl<T: Field + ArkFieldExtensions> Backend<T, marlin::Marlin> for Ark {
    fn generate_proof<I: IntoIterator<Item = Statement<T>>>(
        program: ProgIterator<T, I>,
        witness: Witness<T>,
        proving_key: Vec<u8>,
    ) -> Proof<<marlin::Marlin as Scheme<T>>::ProofPoints> {
        let computation = Computation::with_witness(program, witness);

        let rng = &mut rand_0_8::rngs::StdRng::from_entropy();

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

        let proof = ArkMarlin::<
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
                commitments: proof
                    .commitments
                    .into_iter()
                    .map(|r| {
                        r.into_iter()
                            .map(|c| {
                                (
                                    parse_g1::<T>(&c.comm.0),
                                    c.shifted_comm
                                        .map(|shifted_comm| parse_g1::<T>(&shifted_comm.0)),
                                )
                            })
                            .collect()
                    })
                    .collect(),
                evaluations: proof.evaluations.into_iter().map(T::from_ark).collect(),
                pc_proof_proof: proof
                    .pc_proof
                    .proof
                    .into_iter()
                    .map(|p| (parse_g1::<T>(&p.w), p.random_v.map(T::from_ark)))
                    .collect(),
                pc_proof_evals: proof
                    .pc_proof
                    .evals
                    .map(|evals| evals.into_iter().map(T::from_ark).collect()),
                prover_messages_count: proof.prover_messages.len(),
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
        > {
            commitments: proof
                .proof
                .commitments
                .into_iter()
                .map(|r| {
                    r.into_iter()
                        .map(|(c, shifted_comm)| Commitment {
                            comm: KZG10Commitment(serialization::to_g1::<T>(c)),
                            shifted_comm: shifted_comm.map(|shifted_comm| {
                                KZG10Commitment(serialization::to_g1::<T>(shifted_comm))
                            }),
                        })
                        .collect()
                })
                .collect(),
            evaluations: proof
                .proof
                .evaluations
                .into_iter()
                .map(|v| v.into_ark())
                .collect(),
            prover_messages: vec![ProverMsg::EmptyMessage; proof.proof.prover_messages_count],
            pc_proof: BatchLCProof {
                proof: proof
                    .proof
                    .pc_proof_proof
                    .into_iter()
                    .map(|(w, random_v)| KZG10Proof {
                        w: serialization::to_g1::<T>(w),
                        random_v: random_v.map(|v| v.into_ark()),
                    })
                    .collect(),
                evals: proof
                    .proof
                    .pc_proof_evals
                    .map(|evals| evals.into_iter().map(|eval| eval.into_ark()).collect()),
            },
        };

        let vk = IndexVerifierKey::<
            <<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr,
            MarlinKZG10<
                T::ArkEngine,
                DensePolynomial<<<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr>,
            >,
        > {
            index_info: IndexInfo::new(
                vk.num_variables,
                vk.num_constraints,
                vk.num_non_zero,
                vk.num_instance_variables,
            ),
            index_comms: vk
                .index_comms
                .into_iter()
                .map(|(c, shifted_comm)| Commitment {
                    comm: KZG10Commitment(serialization::to_g1::<T>(c)),
                    shifted_comm: shifted_comm.map(|shifted_comm| {
                        KZG10Commitment(serialization::to_g1::<T>(shifted_comm))
                    }),
                })
                .collect(),
            verifier_key: VerifierKey {
                degree_bounds_and_shift_powers: vk.degree_bounds_and_shift_powers.map(|vk| {
                    vk.into_iter()
                        .map(|(bound, pow)| (bound, serialization::to_g1::<T>(pow)))
                        .collect()
                }),
                max_degree: vk.max_degree,
                supported_degree: vk.supported_degree,
                vk: KZG10VerifierKey {
                    g: serialization::to_g1::<T>(vk.vk.g),
                    gamma_g: serialization::to_g1::<T>(vk.vk.gamma_g),
                    h: serialization::to_g2::<T>(vk.vk.h.clone()),
                    beta_h: serialization::to_g2::<T>(vk.vk.beta_h.clone()),
                    prepared_h: serialization::to_g2::<T>(vk.vk.h).into(),
                    prepared_beta_h: serialization::to_g2::<T>(vk.vk.beta_h).into(),
                },
            },
        };

        let rng = &mut rand_0_8::rngs::StdRng::from_entropy();

        ArkMarlin::<
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

#[cfg(test)]
mod tests {
    use crate::flat_absy::{FlatParameter, FlatVariable};
    use crate::ir::{Interpreter, Prog, QuadComb, Statement};

    use super::*;
    use crate::proof_system::scheme::Marlin;
    use zokrates_field::{Bls12_377Field, Bw6_761Field};

    #[test]
    fn verify_bls12_377_field() {
        let program: Prog<Bls12_377Field> = Prog {
            arguments: vec![FlatParameter::private(FlatVariable::new(0))],
            return_count: 1,
            statements: vec![
                Statement::constraint(
                    QuadComb::from_linear_combinations(
                        FlatVariable::new(0).into(),
                        FlatVariable::new(0).into(),
                    ),
                    FlatVariable::new(1),
                ),
                Statement::constraint(FlatVariable::new(1), FlatVariable::public(0)),
            ],
        };

        let srs = <Ark as UniversalBackend<Bls12_377Field, Marlin>>::universal_setup(5);
        let keypair =
            <Ark as UniversalBackend<Bls12_377Field, Marlin>>::setup(srs, program.clone().into())
                .unwrap();
        let interpreter = Interpreter::default();

        let witness = interpreter
            .execute(program.clone(), &[Bls12_377Field::from(42)])
            .unwrap();

        let proof = <Ark as Backend<Bls12_377Field, Marlin>>::generate_proof(
            program.clone(),
            witness,
            keypair.pk,
        );
        let ans = <Ark as Backend<Bls12_377Field, Marlin>>::verify(keypair.vk, proof);

        assert!(ans);
    }

    #[test]
    fn verify_bw6_761_field() {
        let program: Prog<Bw6_761Field> = Prog {
            arguments: vec![FlatParameter::private(FlatVariable::new(0))],
            return_count: 1,
            statements: vec![
                Statement::constraint(
                    QuadComb::from_linear_combinations(
                        FlatVariable::new(0).into(),
                        FlatVariable::new(0).into(),
                    ),
                    FlatVariable::new(1),
                ),
                Statement::constraint(FlatVariable::new(1), FlatVariable::public(0)),
            ],
        };

        let srs = <Ark as UniversalBackend<Bw6_761Field, Marlin>>::universal_setup(5);
        let keypair =
            <Ark as UniversalBackend<Bw6_761Field, Marlin>>::setup(srs, program.clone()).unwrap();
        let interpreter = Interpreter::default();

        let witness = interpreter
            .execute(program.clone(), &[Bw6_761Field::from(42)])
            .unwrap();

        let proof =
            <Ark as Backend<Bw6_761Field, Marlin>>::generate_proof(program, witness, keypair.pk);
        let ans = <Ark as Backend<Bw6_761Field, Marlin>>::verify(keypair.vk, proof);

        assert!(ans);
    }
}
