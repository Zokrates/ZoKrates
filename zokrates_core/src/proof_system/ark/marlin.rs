use ark_marlin::{
    ahp::indexer::IndexInfo, ahp::prover::ProverMsg, rng::FiatShamirRng, IndexProverKey,
    IndexVerifierKey, Proof as ArkProof,
};

use ark_marlin::Marlin as ArkMarlin;

use ark_ec::PairingEngine;
use ark_ff::{to_bytes, FftField, FromBytes, ToBytes};
use ark_poly::univariate::DensePolynomial;
use ark_poly_commit::{
    data_structures::BatchLCProof,
    kzg10::Commitment as KZG10Commitment,
    kzg10::Proof as KZG10Proof,
    kzg10::VerifierKey as KZG10VerifierKey,
    marlin_pc::{Commitment, MarlinKZG10, VerifierKey},
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use digest::Digest;
use rand_0_8::{Error, RngCore, SeedableRng};
use sha3::Keccak256;
use std::marker::PhantomData;

use zokrates_field::{ArkFieldExtensions, Field};

use crate::ir::{ProgIterator, Statement, Witness};
use crate::proof_system::ark::Ark;
use crate::proof_system::ark::Computation;
use crate::proof_system::ark::{parse_fr, parse_g1, parse_g2, serialization};
use crate::proof_system::marlin::{self, KZGVerifierKey, ProofPoints, VerificationKey};
use crate::proof_system::Scheme;
use crate::proof_system::{Backend, Proof, SetupKeypair, UniversalBackend};

const MINIMUM_CONSTRAINT_COUNT: usize = 2;

/// Simple hash-based Fiat-Shamir RNG that allows for efficient solidity verification.
pub struct HashFiatShamirRng<D: Digest> {
    seed: [u8; 32],
    ctr: u32,
    digest: PhantomData<D>,
}

impl<D: Digest> RngCore for HashFiatShamirRng<D> {
    fn next_u32(&mut self) -> u32 {
        let mut bytes = [0; 4];
        self.fill_bytes(&mut bytes);
        u32::from_be_bytes(bytes)
    }

    fn next_u64(&mut self) -> u64 {
        let mut bytes = [0; 8];
        self.fill_bytes(&mut bytes);
        u64::from_be_bytes(bytes)
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        let bytes_per_hash = D::output_size();
        let n_hashes = (dest.len() - 1) / bytes_per_hash + 1;
        let mut seed_ctr = self.seed.to_vec();
        for i in 0..n_hashes {
            seed_ctr.extend_from_slice(&self.ctr.to_be_bytes());
            let mut h = D::digest(&seed_ctr).to_vec();
            h.reverse(); // Switch to big endian representation for solidity translation
            let len = dest.len();
            if i * bytes_per_hash + bytes_per_hash >= len {
                dest[i * bytes_per_hash..]
                    .copy_from_slice(&h.as_slice()[..len - i * bytes_per_hash]);
            } else {
                dest[i * bytes_per_hash..i * bytes_per_hash + bytes_per_hash]
                    .copy_from_slice(h.as_slice());
            }
            self.ctr += 1;
            seed_ctr.truncate(seed_ctr.len() - 4);
        }
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

impl<D: Digest> FiatShamirRng for HashFiatShamirRng<D> {
    fn initialize<'a, T: 'a + ToBytes>(initial_input: &'a T) -> Self {
        let mut bytes = Vec::new();
        initial_input
            .write(&mut bytes)
            .expect("failed to convert to bytes");
        let seed = FromBytes::read(D::digest(&bytes).as_ref()).expect("failed to get [u8; 32]");
        Self {
            seed,
            ctr: 0,
            digest: PhantomData,
        }
    }

    fn absorb<'a, T: 'a + ToBytes>(&mut self, new_input: &'a T) {
        let mut bytes = Vec::new();
        new_input
            .write(&mut bytes)
            .expect("failed to convert to bytes");
        bytes.extend_from_slice(&self.seed);
        self.seed = FromBytes::read(D::digest(&bytes).as_ref()).expect("failed to get [u8; 32]");
        self.ctr = 0;
    }
}

type PCInst<T> = MarlinKZG10<
    <T as ArkFieldExtensions>::ArkEngine,
    DensePolynomial<<<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr>,
>;
type MarlinInst<T> = ArkMarlin<
    <<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr,
    PCInst<T>,
    HashFiatShamirRng<Keccak256>,
>;

impl<T: Field + ArkFieldExtensions> UniversalBackend<T, marlin::Marlin> for Ark {
    fn universal_setup(size: u32) -> Vec<u8> {
        let rng = &mut rand_0_8::rngs::StdRng::from_entropy();

        let srs = MarlinInst::<T>::universal_setup(
            2usize.pow(size),
            2usize.pow(size),
            2usize.pow(size),
            rng,
        )
        .unwrap();

        let mut res = vec![];

        srs.serialize(&mut res).unwrap();

        res
    }

    fn setup<I: IntoIterator<Item = Statement<T>>>(
        srs: Vec<u8>,
        program: ProgIterator<T, I>,
    ) -> Result<SetupKeypair<T, marlin::Marlin>, String> {
        let program = program.collect();

        if program.constraint_count() < MINIMUM_CONSTRAINT_COUNT {
            return Err(format!("Programs must have a least {} constraints. This program is too small to generate a setup with Marlin, see [this issue](https://github.com/arkworks-rs/marlin/issues/79)", MINIMUM_CONSTRAINT_COUNT));
        }

        let num_public_inputs = program.public_count();

        let computation = Computation::without_witness(program);

        let srs = ark_marlin::UniversalSRS::<
            <<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr,
            MarlinKZG10<
                T::ArkEngine,
                DensePolynomial<<<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr>,
            >,
        >::deserialize(&mut srs.as_slice())
        .unwrap();

        let (pk, vk) = MarlinInst::<T>::index(&srs, computation)
        .map_err(|e| match e {
            ark_marlin::Error::IndexTooLarge => String::from("The universal setup is too small for this program, please provide a larger universal setup"),
            _ => String::from("Unknown error specializing the universal setup for this program")
        })?;

        let mut serialized_pk: Vec<u8> = Vec::new();
        pk.serialize_uncompressed(&mut serialized_pk).unwrap();

        // Precompute some useful values for solidity contract
        let fs_seed = to_bytes![&MarlinInst::<T>::PROTOCOL_NAME, &vk].unwrap();
        let x_root_of_unity =
            <<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr::get_root_of_unity(
                vk.index_info.num_instance_variables,
            )
            .unwrap();

        Ok(SetupKeypair::new(
            VerificationKey {
                fs_seed,
                x_root_of_unity: parse_fr::<T>(&x_root_of_unity),
                index_comms: vk
                    .index_comms
                    .into_iter()
                    .map(|c| (parse_g1::<T>(&c.comm.0), None))
                    .collect(),
                num_public_inputs,
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
    ) -> Proof<T, marlin::Marlin> {
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

        let public_inputs = computation.public_inputs_values();

        let inputs = public_inputs.iter().map(parse_fr::<T>).collect::<Vec<_>>();

        let proof = MarlinInst::<T>::prove(&pk, computation, rng).unwrap();

        assert!(proof.pc_proof.evals.is_none());

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
                evaluations: proof
                    .evaluations
                    .into_iter()
                    .map(|e| parse_fr::<T>(&e))
                    .collect(),
                pc_lc_opening_1: parse_g1::<T>(&proof.pc_proof.proof[0].w),
                pc_lc_opening_1_degree: parse_fr::<T>(&proof.pc_proof.proof[0].random_v.unwrap()),
                pc_lc_opening_2: parse_g1::<T>(&proof.pc_proof.proof[1].w),
                prover_messages_count: proof.prover_messages.len(),
            },
            inputs,
        )
    }

    fn verify(
        vk: <marlin::Marlin as Scheme<T>>::VerificationKey,
        proof: Proof<T, marlin::Marlin>,
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
                .iter()
                .map(|r| {
                    r.iter()
                        .map(|(c, shifted_comm)| Commitment {
                            comm: KZG10Commitment(serialization::to_g1::<T>(c.clone())),
                            shifted_comm: shifted_comm.clone().map(|shifted_comm| {
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
                .map(|v| {
                    T::try_from_str(v.trim_start_matches("0x"), 16)
                        .unwrap()
                        .into_ark()
                })
                .collect(),
            prover_messages: vec![ProverMsg::EmptyMessage; proof.proof.prover_messages_count],
            pc_proof: BatchLCProof {
                proof: vec![
                    KZG10Proof {
                        w: serialization::to_g1::<T>(proof.proof.pc_lc_opening_1),
                        random_v: Some(
                            T::try_from_str(
                                proof.proof.pc_lc_opening_1_degree.trim_start_matches("0x"),
                                16,
                            )
                            .unwrap()
                            .into_ark(),
                        ),
                    },
                    KZG10Proof {
                        w: serialization::to_g1::<T>(proof.proof.pc_lc_opening_2),
                        random_v: None,
                    },
                ],
                evals: None,
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

        MarlinInst::<T>::verify(&vk, &inputs, &proof, rng).unwrap()
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
            <Ark as UniversalBackend<Bls12_377Field, Marlin>>::setup(srs, program.clone()).unwrap();
        let interpreter = Interpreter::default();

        let witness = interpreter
            .execute(program.clone(), &[Bls12_377Field::from(42)])
            .unwrap();

        let proof =
            <Ark as Backend<Bls12_377Field, Marlin>>::generate_proof(program, witness, keypair.pk);
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
