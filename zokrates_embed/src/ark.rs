use ark_bls12_377::{
    constraints::PairingVar as BLS12PairingVar, Bls12_377 as BLS12PairingEngine, Fr as BLS12Fr,
};
use ark_bw6_761::Fr as BW6Fr;
use ark_ec::PairingEngine;
use ark_ff::{Field, UniformRand};
use ark_r1cs_std::bits::boolean::Boolean;
use ark_relations::{
    lc, ns,
    r1cs::{ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, SynthesisError},
};

use ark_crypto_primitives::snark::constraints::SNARKGadget;
use ark_crypto_primitives::snark::{CircuitSpecificSetupSNARK, SNARK};
use ark_gm17::{constraints::GM17VerifierGadget, GM17};
use ark_r1cs_std::ToBitsGadget;

use ark_r1cs_std::alloc::AllocVar;
use ark_std::test_rng;

use crate::Constraint;
use ark_r1cs_std::eq::EqGadget;
use ark_relations::r1cs::Variable;
use ark_std::ops::MulAssign;

#[derive(Copy, Clone)]
struct DummyCircuit<F: Field> {
    a: Option<F>,
    b: Option<F>,
    input_size: usize,
}

impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for DummyCircuit<ConstraintF> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ConstraintF>,
    ) -> Result<(), SynthesisError> {
        let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;

        for _ in 0..self.input_size {
            let c = cs.new_input_variable(|| {
                let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
                let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

                a.mul_assign(&b);
                Ok(a)
            })?;
            cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        }

        Ok(())
    }
}

type GM17Snark = GM17<BLS12PairingEngine>;
type VerifierGadget = GM17VerifierGadget<BLS12PairingEngine, BLS12PairingVar>;

// pub fn generate_verify_constraints(input_size: usize) -> (usize, Vec<Constraint<BW6Fr>>) {
#[test]
pub fn generate_verify_constraints() {
    let input_size: usize = 1;
    let mut rng = test_rng();
    let a = BLS12Fr::rand(&mut rng);
    let b = BLS12Fr::rand(&mut rng);
    let mut c = a.clone();
    c.mul_assign(&b);

    let circuit = DummyCircuit {
        a: Some(a),
        b: Some(b),
        input_size,
    };

    let (pk, vk) = GM17Snark::setup(circuit.clone(), &mut rng).unwrap();
    let proof = GM17Snark::prove(&pk, circuit, &mut rng).unwrap();

    let cs_sys = ConstraintSystem::<BW6Fr>::new();
    let cs = ConstraintSystemRef::new(cs_sys);

    let input_gadget =
        <VerifierGadget as SNARKGadget<
            <BLS12PairingEngine as PairingEngine>::Fr,
            <BLS12PairingEngine as PairingEngine>::Fq,
            GM17Snark,
        >>::InputVar::new_input(ns!(cs, "alloc_inputs"), || Ok(vec![c; input_size]))
        .unwrap();

    let input_indices = input_gadget
        .clone()
        .into_iter()
        .map(|f| {
            f.iter()
                .map(|b| match b {
                    Boolean::Is(x) => var_to_index(x.variable()),
                    Boolean::Not(x) => var_to_index(x.variable()),
                    _ => unreachable!(),
                })
                .collect()
        })
        .collect::<Vec<Vec<usize>>>();

    let proof_gadget = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::ProofVar::new_witness(ns!(cs, "alloc_proof"), || Ok(proof))
    .unwrap();

    let proof_indices = proof_gadget
        .clone()
        .a
        .to_bits_le()
        .unwrap()
        .into_iter()
        .map(|b| match b {
            Boolean::Is(x) => var_to_index(x.variable()),
            Boolean::Not(x) => var_to_index(x.variable()),
            _ => unreachable!(),
        })
        .collect::<Vec<usize>>();

    let vk_gadget = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::VerifyingKeyVar::new_constant(ns!(cs, "alloc_vk"), vk.clone())
    .unwrap();

    // let vk_indices = vk_gadget
    //     .clone()
    //     .into_iter()
    //     .map(|f| f.iter().map(|b| match b {
    //         Boolean::Is(x) => var_to_index(x.variable()),
    //         Boolean::Not(x) => var_to_index(x.variable()),
    //         _ => unreachable!(),
    //     }).collect())
    //     .collect::<Vec<Vec<usize>>>();

    let res = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::verify(&vk_gadget, &input_gadget, &proof_gadget)
    .unwrap();

    let out_index = match &res {
        Boolean::Is(x) => var_to_index(x.variable()),
        Boolean::Not(x) => var_to_index(x.variable()),
        _ => unreachable!(),
    };

    res.conditional_enforce_equal(&Boolean::constant(true), &Boolean::constant(true))
        .unwrap();
    cs.finalize();

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

    assert!(cs.is_satisfied().unwrap());

    println!("{}", input_indices.len());
    println!("{}", proof_indices.len());
    // println!("{}", vk_indices.len());

    // (out_index, constraints)
}

fn var_to_index(v: Variable) -> usize {
    v.get_index_unchecked(0)
        .expect("Could not get variable index")
}
