use ark_bls12_377::{
    constraints::PairingVar as BLS12PairingVar, Bls12_377 as BLS12PairingEngine, Fq as BLS12Fq,
    Fq2 as BLS12Fq2,
};
use ark_bw6_761::Fr as BW6Fr;
use ark_ec::PairingEngine;
use ark_ff::{BigInteger, One, PrimeField};
use ark_r1cs_std::bits::boolean::Boolean;
use ark_relations::{
    ns,
    r1cs::{ConstraintSystem, ConstraintSystemRef},
};

use ark_crypto_primitives::snark::constraints::SNARKGadget;
use ark_gm17::{constraints::GM17VerifierGadget, Proof, VerifyingKey, GM17};
use ark_r1cs_std::alloc::{AllocVar, AllocationMode};

use crate::Constraint;
use ark_crypto_primitives::SNARK;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::ToBitsGadget;
use ark_relations::r1cs::{ConstraintSynthesizer, SynthesisError};
use ark_std::test_rng;
use std::str::FromStr;
use zokrates_field::Field;

type GM17Snark = GM17<BLS12PairingEngine>;
type VerifierGadget = GM17VerifierGadget<BLS12PairingEngine, BLS12PairingVar>;

type G1 = <ark_ec::bls12::Bls12<ark_bls12_377::Parameters> as PairingEngine>::G1Affine;
type G2 = <ark_ec::bls12::Bls12<ark_bls12_377::Parameters> as PairingEngine>::G2Affine;

#[derive(Copy, Clone)]
struct DefaultCircuit {
    pub public_input_size: usize,
}

impl<F: PrimeField> ConstraintSynthesizer<F> for DefaultCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        for _ in 0..self.public_input_size {
            let _ = FpVar::<F>::new_input(ns!(cs, "alloc_input"), || Ok(F::one()))?;
        }
        Ok(())
    }
}

#[allow(clippy::type_complexity)]
pub fn generate_verify_constraints(
    public_input_size: usize,
) -> (
    usize,
    Vec<usize>,
    Vec<usize>,
    Vec<usize>,
    Vec<Constraint<BW6Fr>>,
    usize,
) {
    let cs_sys = ConstraintSystem::<BW6Fr>::new();
    let cs = ConstraintSystemRef::new(cs_sys);

    let mut rng = test_rng(); // has a fixed seed
    let circuit = DefaultCircuit { public_input_size };

    let (pk, vk) = GM17Snark::circuit_specific_setup(circuit, &mut rng).unwrap();
    let proof = GM17Snark::prove(&pk, circuit, &mut rng).unwrap();

    let mut fp_vars = Vec::new();
    for _ in 0..public_input_size {
        let fp = FpVar::new_input(ns!(cs, "alloc_input"), || Ok(BLS12Fq::one())).unwrap();
        fp_vars.push(fp);
    }

    let input_booleans: Vec<Vec<Boolean<_>>> =
        fp_vars.iter().map(|i| i.to_bits_le().unwrap()).collect();

    let inputs = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::InputVar::new(input_booleans);

    let proof = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::new_proof_unchecked(
        ns!(cs, "alloc_proof"),
        || Ok(proof),
        AllocationMode::Witness,
    )
    .unwrap();

    let vk = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::new_verification_key_unchecked(
        ns!(cs, "alloc_vk"), || Ok(vk), AllocationMode::Witness
    )
    .unwrap();

    let res = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::verify(&vk, &inputs, &proof)
    .unwrap();

    cs.finalize();

    let num_instance_variables = cs.num_instance_variables();
    let input_indices = fp_vars
        .iter()
        .map(|f| var_to_index(f, 0))
        .collect::<Vec<usize>>();

    let proof_indices: Vec<usize> = vec![
        var_to_index(&proof.a.x, num_instance_variables),
        var_to_index(&proof.a.y, num_instance_variables),
        var_to_index(&proof.b.x.c0, num_instance_variables),
        var_to_index(&proof.b.x.c1, num_instance_variables),
        var_to_index(&proof.b.y.c0, num_instance_variables),
        var_to_index(&proof.b.y.c1, num_instance_variables),
        var_to_index(&proof.c.x, num_instance_variables),
        var_to_index(&proof.c.y, num_instance_variables),
    ];

    let mut vk_indices: Vec<usize> = vec![
        var_to_index(&vk.h_g2.x.c0, num_instance_variables),
        var_to_index(&vk.h_g2.x.c1, num_instance_variables),
        var_to_index(&vk.h_g2.y.c0, num_instance_variables),
        var_to_index(&vk.h_g2.y.c1, num_instance_variables),
        var_to_index(&vk.g_alpha_g1.x, num_instance_variables),
        var_to_index(&vk.g_alpha_g1.y, num_instance_variables),
        var_to_index(&vk.h_beta_g2.x.c0, num_instance_variables),
        var_to_index(&vk.h_beta_g2.x.c1, num_instance_variables),
        var_to_index(&vk.h_beta_g2.y.c0, num_instance_variables),
        var_to_index(&vk.h_beta_g2.y.c1, num_instance_variables),
        var_to_index(&vk.g_gamma_g1.x, num_instance_variables),
        var_to_index(&vk.g_gamma_g1.y, num_instance_variables),
        var_to_index(&vk.h_gamma_g2.x.c0, num_instance_variables),
        var_to_index(&vk.h_gamma_g2.x.c1, num_instance_variables),
        var_to_index(&vk.h_gamma_g2.y.c0, num_instance_variables),
        var_to_index(&vk.h_gamma_g2.y.c1, num_instance_variables),
    ];

    vk_indices.extend(vk.query.iter().flat_map(|q| {
        vec![
            var_to_index(&q.x, num_instance_variables),
            var_to_index(&q.y, num_instance_variables),
        ]
    }));

    let out_index = match &res {
        Boolean::Is(x) => x
            .variable()
            .get_index_unchecked(num_instance_variables)
            .unwrap(),
        _ => unreachable!(),
    };

    let matrices = cs.to_matrices().unwrap();
    let constraints: Vec<Constraint<_>> = matrices
        .a
        .into_iter()
        .zip(matrices.b.into_iter())
        .zip(matrices.c.into_iter())
        .map(|((a, b), c)| Constraint { a, b, c })
        .collect();

    (
        out_index,
        input_indices,
        proof_indices,
        vk_indices,
        constraints,
        cs.num_witness_variables() + cs.num_instance_variables(),
    )
}

pub fn generate_verify_witness<T: Field>(inputs: &[T], proof: &[T], vk: &[T]) -> Vec<T> {
    assert_eq!(proof.len(), 8);
    assert_eq!(vk.len(), 18 + (2 * inputs.len()));

    let cs_sys = ConstraintSystem::<BW6Fr>::new();
    let cs = ConstraintSystemRef::new(cs_sys);

    let mut fp_vars = Vec::new();
    for input in inputs {
        let input_field: BLS12Fq = BLS12Fq::from_str(input.to_dec_string().as_str()).unwrap();
        let fp = FpVar::new_input(ns!(cs, "alloc_input"), || Ok(input_field)).unwrap();
        fp_vars.push(fp);
    }

    let input_booleans: Vec<Vec<Boolean<_>>> = fp_vars
        .into_iter()
        .map(|i| i.to_bits_le().unwrap())
        .collect();

    let inputs = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::InputVar::new(input_booleans);

    let proof = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::new_proof_unchecked(
        ns!(cs, "alloc_proof"),
        || {
            Ok(Proof {
                a: new_g1(&proof[0..2]),
                b: new_g2(&proof[2..6]),
                c: new_g1(&proof[6..8]),
            })
        },
        AllocationMode::Witness,
    )
    .unwrap();

    let vk = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::new_verification_key_unchecked(
        ns!(cs, "alloc_vk"),
        || {
            Ok(VerifyingKey {
                h_g2: new_g2(&vk[0..4]),
                g_alpha_g1: new_g1(&vk[4..6]),
                h_beta_g2: new_g2(&vk[6..10]),
                g_gamma_g1: new_g1(&vk[10..12]),
                h_gamma_g2: new_g2(&vk[12..16]),
                query: (16..vk.len())
                    .collect::<Vec<_>>()
                    .chunks(2)
                    .map(|c| new_g1(&vk[c[0]..c[1] + 1]))
                    .collect(),
            })
        },
        AllocationMode::Witness,
    )
    .unwrap();

    let _ = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::verify(&vk, &inputs, &proof)
    .unwrap();

    cs.finalize();

    let cs = cs.borrow().unwrap();
    let witness_variables: Vec<BLS12Fq> = cs.witness_assignment.clone();

    cs.instance_assignment
        .clone()
        .into_iter()
        .chain(witness_variables)
        .map(|fq| T::from_byte_vector(fq.into_repr().to_bytes_le()))
        .collect()
}

#[inline]
fn var_to_index<F: ark_ff::PrimeField>(var: &FpVar<F>, offset: usize) -> usize {
    match var {
        FpVar::Var(ref fp) => {
            let var = &fp.variable;
            var.get_index_unchecked(offset).unwrap()
        }
        _ => unreachable!("expected variable, but found a constant"),
    }
}

#[inline]
fn new_g1<T: Field>(flat: &[T]) -> G1 {
    assert_eq!(flat.len(), 2);
    G1::new(
        BLS12Fq::from_str(&flat[0].to_dec_string()).unwrap(),
        BLS12Fq::from_str(&flat[1].to_dec_string()).unwrap(),
        false,
    )
}

#[inline]
fn new_g2<T: Field>(flat: &[T]) -> G2 {
    assert_eq!(flat.len(), 4);
    G2::new(
        BLS12Fq2::new(
            BLS12Fq::from_str(&flat[0].to_dec_string()).unwrap(),
            BLS12Fq::from_str(&flat[1].to_dec_string()).unwrap(),
        ),
        BLS12Fq2::new(
            BLS12Fq::from_str(&flat[2].to_dec_string()).unwrap(),
            BLS12Fq::from_str(&flat[3].to_dec_string()).unwrap(),
        ),
        false,
    )
}

pub fn from_ark<T: zokrates_field::Field, E: PairingEngine>(c: Constraint<E::Fq>) -> Constraint<T> {
    Constraint {
        a: c.a
            .into_iter()
            .map(|(fq, index)| {
                let mut res: Vec<u8> = vec![];
                fq.into_repr().write_le(&mut res).unwrap();
                (T::from_byte_vector(res), index)
            })
            .collect(),
        b: c.b
            .into_iter()
            .map(|(fq, index)| {
                let mut res: Vec<u8> = vec![];
                fq.into_repr().write_le(&mut res).unwrap();
                (T::from_byte_vector(res), index)
            })
            .collect(),
        c: c.c
            .into_iter()
            .map(|(fq, index)| {
                let mut res: Vec<u8> = vec![];
                fq.into_repr().write_le(&mut res).unwrap();
                (T::from_byte_vector(res), index)
            })
            .collect(),
    }
}
