use crate::{var_to_index, BellmanR1CS, BellmanWitness};
use bellman_ce::pairing::{ff::Field, Engine};
use bellman_ce::{ConstraintSystem, SynthesisError};

use sapling_crypto::circuit::{blake2s::blake2s, boolean::AllocatedBit};

fn blake2s_round<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    input: &Vec<Option<E::Fr>>,
) -> Result<(Vec<usize>, Vec<usize>), SynthesisError> {
    assert_eq!(input.len() % 8, 0);

    // Allocate bits for `input`
    let input_bits: Vec<_> = input
        .iter()
        .enumerate()
        .map(|(index, i)| {
            AllocatedBit::alloc(
                cs.namespace(|| format!("input bit {}", index)),
                Some(*i == Some(<E::Fr as Field>::one())),
            )
            .unwrap()
            .into()
        })
        .collect();

    // TODO: parameterize personalization
    let res = blake2s(&mut cs, &input_bits, b"12345678").unwrap();

    let output_bits = res
        .into_iter()
        .map(|b| b.get_variable().unwrap().clone())
        .collect::<Vec<_>>();

    Ok((
        input_bits
            .into_iter()
            .map(|b| var_to_index(b.get_variable().unwrap().get_variable()))
            .collect(),
        output_bits
            .into_iter()
            .map(|b| var_to_index(b.get_variable()))
            .collect(),
    ))
}

pub fn generate_blake2s_round_constraints<E: Engine>() -> (BellmanR1CS<E>, Vec<usize>, Vec<usize>) {
    let mut cs = BellmanR1CS::new();

    let (input_bits, output_bits) = blake2s_round(&mut cs, &vec![None; 512]).unwrap();

    // res is now the allocated bits for `input_bits` and `output_bits`
    (cs, input_bits, output_bits)
}

pub fn generate_blake2s_round_witness<E: Engine>(input: &[E::Fr]) -> Vec<E::Fr> {
    let mut cs: BellmanWitness<E> = BellmanWitness {
        values: vec![<E::Fr as Field>::one()],
    };

    blake2s_round(&mut cs, &input.iter().map(|x| Some(x.clone())).collect()).unwrap();
    cs.values
}

#[cfg(test)]
mod tests {
    use super::*;
    use bellman_ce::pairing::bn256::{Bn256, Fr};

    #[test]
    fn generate_constraints() {
        let (_c, input, output) = generate_blake2s_round_constraints::<Bn256>();
        assert_eq!(input.len(), 512);
        assert_eq!(output.len(), 256);
    }

    #[test]
    fn generate_witness() {
        let witness = generate_blake2s_round_witness::<Bn256>(&vec![Fr::one(); 512]);
        assert_eq!(witness.len(), 21473);
    }

    #[test]
    fn test_cs() {
        use sapling_crypto::circuit::test::TestConstraintSystem;
        let mut cs: TestConstraintSystem<Bn256> = TestConstraintSystem::new();

        let _ = blake2s_round(&mut cs, &vec![Some(Fr::one()); 512]).unwrap();
        assert!(cs.is_satisfied());
    }
}
