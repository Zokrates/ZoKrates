use ark_bls12_377::{
    constraints::PairingVar as BLS12PairingVar, Bls12_377 as BLS12PairingEngine, Fq as BLS12Fq,
};
use ark_bw6_761::Fr as BW6Fr;
use ark_ec::PairingEngine;
use ark_ff::{BigInteger, One, PrimeField};
use ark_r1cs_std::bits::boolean::Boolean;
use ark_relations::{
    ns,
    r1cs::{ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, SynthesisError},
};

use ark_crypto_primitives::snark::constraints::SNARKGadget;
use ark_crypto_primitives::snark::{FromFieldElementsGadget, SNARK};
use ark_gm17::{constraints::GM17VerifierGadget, GM17};
use ark_r1cs_std::ToConstraintFieldGadget;

use ark_r1cs_std::alloc::AllocVar;
use ark_std::test_rng;

use crate::Constraint;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::Variable;

#[derive(Copy, Clone)]
struct DefaultCircuit {
    pub public_input_size: usize,
}

impl<F: PrimeField> ConstraintSynthesizer<F> for DefaultCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        for _ in 0..self.public_input_size {
            let _ = FpVar::<F>::new_input(ns!(cs, "alloc"), || Ok(F::one()))?;
            // gadget.to_bits_le()?;
        }
        Ok(())
    }
}

type GM17Snark = GM17<BLS12PairingEngine>;
type VerifierGadget = GM17VerifierGadget<BLS12PairingEngine, BLS12PairingVar>;

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
    let mut rng = test_rng();
    let circuit = DefaultCircuit { public_input_size };

    let (pk, vk) = GM17Snark::circuit_specific_setup(circuit, &mut rng).unwrap();
    let proof = GM17Snark::prove(&pk, circuit, &mut rng).unwrap();

    let cs_sys = ConstraintSystem::<BW6Fr>::new();
    let cs = ConstraintSystemRef::new(cs_sys);

    let mut inputs = Vec::new();
    for _ in 0..public_input_size {
        inputs.push(FpVar::new_input(ns!(cs, "alloc_input"), || Ok(BLS12Fq::one())).unwrap());
    }

    let input_indices = inputs
        .iter()
        .map(|f| match f {
            FpVar::Var(fp) => var_to_index(&fp.variable),
            _ => unreachable!(),
        })
        .collect::<Vec<usize>>();

    let input_gadget = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::InputVar::from_field_elements(&inputs)
    .unwrap();

    let proof_gadget = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::ProofVar::new_witness(ns!(cs, "alloc_proof"), || Ok(proof))
    .unwrap();

    let proof_indices: Vec<usize> = vec![
        proof_gadget
            .a
            .to_constraint_field()
            .unwrap()
            .iter()
            .take(2) // [x, y, infinity] - infinity
            .map(|f| match f {
                FpVar::Var(fp) => var_to_index(&fp.variable),
                _ => unreachable!(),
            })
            .collect::<Vec<usize>>(),
        proof_gadget
            .b
            .to_constraint_field()
            .unwrap()
            .iter()
            .take(4) // [[x0, y0], [x1, y1], infinity] - infinity
            .map(|f| match f {
                FpVar::Var(fp) => var_to_index(&fp.variable),
                _ => unreachable!(),
            })
            .collect::<Vec<usize>>(),
        proof_gadget
            .c
            .to_constraint_field()
            .unwrap()
            .iter()
            .take(2) // [x, y, infinity] - infinity
            .map(|f| match f {
                FpVar::Var(fp) => var_to_index(&fp.variable),
                _ => unreachable!(),
            })
            .collect::<Vec<usize>>(),
    ]
    .into_iter()
    .flatten()
    .collect();

    let vk_gadget = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::VerifyingKeyVar::new_witness(ns!(cs, "alloc_vk"), || Ok(vk.clone()))
    .unwrap();

    let vk_indices: Vec<usize> = vec![
        vk_gadget
            .h_g2
            .to_constraint_field()
            .unwrap()
            .iter()
            .take(4) // [[x0, y0], [x1, y1], infinity] - infinity
            .map(|f| match f {
                FpVar::Var(fp) => var_to_index(&fp.variable),
                _ => unreachable!(),
            })
            .collect::<Vec<usize>>(),
        vk_gadget
            .g_alpha_g1
            .to_constraint_field()
            .unwrap()
            .iter()
            .take(2) // [x, y, infinity] - infinity
            .map(|f| match f {
                FpVar::Var(fp) => var_to_index(&fp.variable),
                _ => unreachable!(),
            })
            .collect::<Vec<usize>>(),
        vk_gadget
            .h_beta_g2
            .to_constraint_field()
            .unwrap()
            .iter()
            .take(4) // [[x0, y0], [x1, y1], infinity] - infinity
            .map(|f| match f {
                FpVar::Var(fp) => var_to_index(&fp.variable),
                _ => unreachable!(),
            })
            .collect::<Vec<usize>>(),
        vk_gadget
            .g_gamma_g1
            .to_constraint_field()
            .unwrap()
            .iter()
            .take(2) // [x, y, infinity] - infinity
            .map(|f| match f {
                FpVar::Var(fp) => var_to_index(&fp.variable),
                _ => unreachable!(),
            })
            .collect::<Vec<usize>>(),
        vk_gadget
            .h_gamma_g2
            .to_constraint_field()
            .unwrap()
            .iter()
            .take(4) // [[x0, y0], [x1, y1], infinity] - infinity
            .map(|f| match f {
                FpVar::Var(fp) => var_to_index(&fp.variable),
                _ => unreachable!(),
            })
            .collect::<Vec<usize>>(),
        vk_gadget
            .query
            .iter()
            .map(|q| {
                q.to_constraint_field()
                    .unwrap()
                    .iter()
                    .take(2) // [x, y, infinity] - infinity
                    .map(|f| match f {
                        FpVar::Var(fp) => var_to_index(&fp.variable),
                        _ => unreachable!(),
                    })
                    .collect::<Vec<usize>>()
            })
            .flatten()
            .collect::<Vec<usize>>(),
    ]
    .into_iter()
    .flatten()
    .collect::<Vec<usize>>();

    let res = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::verify(&vk_gadget, &input_gadget, &proof_gadget)
    .unwrap();

    let out_index = match &res {
        Boolean::Is(x) => var_to_index(&x.variable()),
        Boolean::Not(x) => var_to_index(&x.variable()),
        _ => unreachable!(),
    };

    // res.conditional_enforce_equal(&Boolean::TRUE, &Boolean::TRUE).unwrap();
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

    // println!("input_indices: {:?}", input_indices);
    // println!("proof_indices: {:?}", proof_indices);
    // println!("vk_indices: {:?}", vk_indices);
    // println!("out_index: {:?}", out_index);

    assert!(
        cs.is_satisfied().unwrap(),
        "Constraint not satisfied: {}",
        cs.which_is_unsatisfied().unwrap().unwrap_or_default()
    );

    (
        out_index,
        input_indices,
        proof_indices,
        vk_indices,
        constraints,
        cs.num_witness_variables(),
    )
}

#[test]
fn generate_verify_constraints_test() {
    let _ = generate_verify_constraints(2);
}

fn var_to_index(v: &Variable) -> usize {
    v.get_index_unchecked(0)
        .expect("Could not get variable index")
}

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
