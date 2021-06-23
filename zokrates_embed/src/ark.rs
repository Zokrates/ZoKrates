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
use ark_crypto_primitives::snark::FromFieldElementsGadget;
use ark_gm17::{constraints::GM17VerifierGadget, Proof, VerifyingKey, GM17};
use ark_r1cs_std::alloc::{AllocVar, AllocationMode};

use crate::Constraint;
use ark_r1cs_std::fields::fp::FpVar;
use std::str::FromStr;
use zokrates_field::{Field};

macro_rules! var {
    ($f:expr, $offset:expr) => {
        match $f {
            FpVar::Var(ref fp) => {
                let var = &fp.variable;
                var.get_index_unchecked($offset).unwrap()
            }
            _ => unreachable!("expected variable, found constant"),
        }
    };
}

type GM17Snark = GM17<BLS12PairingEngine>;
type VerifierGadget = GM17VerifierGadget<BLS12PairingEngine, BLS12PairingVar>;

type G1 = <ark_ec::bls12::Bls12<ark_bls12_377::Parameters> as PairingEngine>::G1Affine;
type G2 = <ark_ec::bls12::Bls12<ark_bls12_377::Parameters> as PairingEngine>::G2Affine;

macro_rules! g1 {
    ($e:expr, $i0:expr, $i1:expr) => {
        G1::new(
            BLS12Fq::from_str(&*$e[$i0].to_dec_string()).unwrap(),
            BLS12Fq::from_str(&*$e[$i1].to_dec_string()).unwrap(),
            false,
        )
    };
}

macro_rules! g2 {
    ($e:expr, $i0:expr, $i1:expr, $i2:expr, $i3:expr) => {
        G2::new(
            BLS12Fq2::new(
                BLS12Fq::from_str(&*$e[$i0].to_dec_string()).unwrap(),
                BLS12Fq::from_str(&*$e[$i1].to_dec_string()).unwrap(),
            ),
            BLS12Fq2::new(
                BLS12Fq::from_str(&*$e[$i2].to_dec_string()).unwrap(),
                BLS12Fq::from_str(&*$e[$i3].to_dec_string()).unwrap(),
            ),
            false,
        )
    };
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

    let mut inputs = Vec::new();
    for _ in 0..public_input_size {
        inputs.push(FpVar::new_input(ns!(cs, "alloc_input"), || Ok(BLS12Fq::one())).unwrap());
    }

    let dummy_inputs = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::InputVar::from_field_elements(&inputs)
    .unwrap();

    let dummy_inputs_len = dummy_inputs.clone().into_iter().len();
    let dummy_proof = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::new_proof_unchecked(
        ns!(cs, "alloc_proof"),
        || {
            Ok(Proof {
                a: G1::default(),
                b: G2::default(),
                c: G1::default(),
            })
        },
        AllocationMode::Witness,
    )
    .unwrap();

    let dummy_vk = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::new_verification_key_unchecked(
        ns!(cs, "alloc_vk"),
        || {
            Ok(VerifyingKey {
                h_g2: G2::default(),
                g_alpha_g1: G1::default(),
                h_beta_g2: G2::default(),
                g_gamma_g1: G1::default(),
                h_gamma_g2: G2::default(),
                query: vec![G1::default(); dummy_inputs_len],
            })
        },
        AllocationMode::Witness,
    )
    .unwrap();

    let res = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::verify(&dummy_vk, &dummy_inputs, &dummy_proof)
    .unwrap();

    cs.finalize();

    let num_instance_variables = cs.num_instance_variables();
    let input_indices = inputs.iter().map(|f| var!(f, 0)).collect::<Vec<usize>>();

    let proof_indices: Vec<usize> = vec![
        var!(dummy_proof.a.x, num_instance_variables),
        var!(dummy_proof.a.y, num_instance_variables),
        var!(dummy_proof.b.x.c0, num_instance_variables),
        var!(dummy_proof.b.x.c1, num_instance_variables),
        var!(dummy_proof.b.y.c0, num_instance_variables),
        var!(dummy_proof.b.y.c1, num_instance_variables),
        var!(dummy_proof.c.x, num_instance_variables),
        var!(dummy_proof.c.y, num_instance_variables),
    ];

    let mut vk_indices: Vec<usize> = vec![
        var!(dummy_vk.h_g2.x.c0, num_instance_variables),
        var!(dummy_vk.h_g2.x.c1, num_instance_variables),
        var!(dummy_vk.h_g2.y.c0, num_instance_variables),
        var!(dummy_vk.h_g2.y.c1, num_instance_variables),
        var!(dummy_vk.g_alpha_g1.x, num_instance_variables),
        var!(dummy_vk.g_alpha_g1.y, num_instance_variables),
        var!(dummy_vk.h_beta_g2.x.c0, num_instance_variables),
        var!(dummy_vk.h_beta_g2.x.c1, num_instance_variables),
        var!(dummy_vk.h_beta_g2.y.c0, num_instance_variables),
        var!(dummy_vk.h_beta_g2.y.c1, num_instance_variables),
        var!(dummy_vk.g_gamma_g1.x, num_instance_variables),
        var!(dummy_vk.g_gamma_g1.y, num_instance_variables),
        var!(dummy_vk.h_gamma_g2.x.c0, num_instance_variables),
        var!(dummy_vk.h_gamma_g2.x.c1, num_instance_variables),
        var!(dummy_vk.h_gamma_g2.y.c0, num_instance_variables),
        var!(dummy_vk.h_gamma_g2.y.c1, num_instance_variables),
    ];

    vk_indices.extend(
        dummy_vk
            .query
            .iter()
            .map(|q| {
                vec![
                    var!(q.x, num_instance_variables),
                    var!(q.y, num_instance_variables),
                ]
            })
            .flatten(),
    );

    let out_index = match &res {
        Boolean::Is(x) => x
            .variable()
            .get_index_unchecked(num_instance_variables)
            .unwrap(),
        Boolean::Not(x) => x
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
        .map(|((a, b), c)| Constraint {
            a: a.into_iter().map(|(f, index)| (index, f)).collect(),
            b: b.into_iter().map(|(f, index)| (index, f)).collect(),
            c: c.into_iter().map(|(f, index)| (index, f)).collect(),
        })
        .collect();

    /*
    println!("num_instance_variables: {:?}", num_instance_variables);
    println!("input_indices: {:?}", input_indices);
    println!("proof_indices: {:?}", proof_indices);
    println!("vk_indices: {:?}", vk_indices);
    println!("out_index: {:?}", out_index);
    println!("constraint_count: {:?}", cs.num_constraints());
    println!(
        "variable_count: {:?}",
        cs.num_witness_variables() + cs.num_instance_variables()
    );
    */

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

    let mut input_vec = Vec::new();
    for input in inputs {
        input_vec.push(
            FpVar::new_input(ns!(cs, "alloc_input"), || {
                Ok(BLS12Fq::from_str(&*input.to_dec_string()).unwrap())
            })
            .unwrap(),
        );
    }

    let inputs = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::InputVar::from_field_elements(&input_vec)
    .unwrap();

    let proof = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::new_proof_unchecked(
        ns!(cs, "alloc_proof"),
        || {
            Ok(Proof {
                a: g1!(proof, 0, 1),
                b: g2!(proof, 2, 3, 4, 5),
                c: g1!(proof, 6, 7),
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
                h_g2: g2!(vk, 0, 1, 2, 3),
                g_alpha_g1: g1!(vk, 4, 5),
                h_beta_g2: g2!(vk, 6, 7, 8, 9),
                g_gamma_g1: g1!(vk, 10, 11),
                h_gamma_g2: g2!(vk, 12, 13, 14, 15),
                query: (16..vk.len())
                    .collect::<Vec<_>>()
                    .chunks(2)
                    .map(|c| g1!(vk, c[0], c[1]))
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

/*
#[test]
fn generate_verify_constraints_test() {
    let _ = generate_verify_constraints(1);
}
*/

pub fn from_ark<T: zokrates_field::Field, E: PairingEngine>(c: Constraint<E::Fq>) -> Constraint<T> {
    Constraint {
        a: c.a
            .into_iter()
            .map(|(index, fq)| {
                let mut res: Vec<u8> = vec![];
                fq.into_repr().write_le(&mut res).unwrap();
                (index, T::from_byte_vector(res))
            })
            .collect(),
        b: c.b
            .into_iter()
            .map(|(index, fq)| {
                let mut res: Vec<u8> = vec![];
                fq.into_repr().write_le(&mut res).unwrap();
                (index, T::from_byte_vector(res))
            })
            .collect(),
        c: c.c
            .into_iter()
            .map(|(index, fq)| {
                let mut res: Vec<u8> = vec![];
                fq.into_repr().write_le(&mut res).unwrap();
                (index, T::from_byte_vector(res))
            })
            .collect(),
    }
}
