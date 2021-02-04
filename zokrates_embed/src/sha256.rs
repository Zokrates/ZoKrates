use crate::{var_to_index, BellmanR1CS, BellmanWitness};
use bellman_ce::pairing::{ff::Field, Engine};
use bellman_ce::{ConstraintSystem, SynthesisError};

use sapling_crypto::circuit::{
    boolean::{AllocatedBit, Boolean},
    sha256::sha256_compression_function,
    uint32::UInt32,
};

fn sha256_round<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    input: &Vec<Option<E::Fr>>,
    current_hash: &Vec<Option<E::Fr>>,
) -> Result<(Vec<usize>, Vec<usize>, Vec<usize>), SynthesisError> {
    // Allocate bits for `input`
    let input_bits = input
        .iter()
        .enumerate()
        .map(|(index, i)| {
            AllocatedBit::alloc::<E, _>(
                &mut cs.namespace(|| format!("input_{}", index)),
                Some(*i == Some(<E::Fr as Field>::one())),
            )
            .unwrap()
        })
        .collect::<Vec<_>>();

    // Define Booleans whose values are the defined bits
    let input = input_bits
        .iter()
        .map(|i| Boolean::Is(i.clone()))
        .collect::<Vec<_>>();

    // Allocate bits for `current_hash`
    let current_hash_bits = current_hash
        .iter()
        .enumerate()
        .map(|(index, i)| {
            AllocatedBit::alloc::<E, _>(
                &mut cs.namespace(|| format!("current_hash_{}", index)),
                Some(*i == Some(<E::Fr as Field>::one())),
            )
            .unwrap()
        })
        .collect::<Vec<_>>();

    // Define Booleans whose values are the defined bits
    let current_hash = current_hash_bits
        .chunks(32)
        .map(|chunk| {
            UInt32::from_bits_be(
                &chunk
                    .into_iter()
                    .map(|i| Boolean::Is(i.clone()))
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<Vec<_>>();

    // Apply the compression function, returning the 8 bytes of outputs
    let res = sha256_compression_function::<E, _>(&mut cs, &input, &current_hash).unwrap();

    // Extract the 256 bits of output out of the 8 bytes
    let output_bits = res
        .into_iter()
        .flat_map(|u| u.into_bits_be())
        .map(|b| b.get_variable().unwrap().clone())
        .collect::<Vec<_>>();

    // Return indices of `input`, `current_hash` and `output` in the CS
    Ok((
        input_bits
            .into_iter()
            .map(|b| var_to_index(b.get_variable()))
            .collect(),
        current_hash_bits
            .into_iter()
            .map(|b| var_to_index(b.get_variable()))
            .collect(),
        output_bits
            .into_iter()
            .map(|b| var_to_index(b.get_variable()))
            .collect(),
    ))
}

pub fn generate_sha256_round_constraints<E: Engine>(
) -> (BellmanR1CS<E>, Vec<usize>, Vec<usize>, Vec<usize>) {
    let mut cs = BellmanR1CS::new();

    let (input_bits, current_hash_bits, output_bits) =
        sha256_round(&mut cs, &vec![None; 512], &vec![None; 256]).unwrap();

    // res is now the allocated bits for `input`, `current_hash` and `sha256_output`
    (cs, input_bits, current_hash_bits, output_bits)
}

pub fn generate_sha256_round_witness<E: Engine>(
    input: &[E::Fr],
    current_hash: &[E::Fr],
) -> Vec<E::Fr> {
    assert_eq!(input.len(), 512);
    assert_eq!(current_hash.len(), 256);

    let mut cs: BellmanWitness<E> = BellmanWitness {
        values: vec![<E::Fr as Field>::one()],
    };

    sha256_round(
        &mut cs,
        &input.iter().map(|x| Some(x.clone())).collect(),
        &current_hash.iter().map(|x| Some(x.clone())).collect(),
    )
    .unwrap();

    cs.values
}

#[cfg(test)]
mod tests {
    use super::*;
    use bellman_ce::pairing::bn256::{Bn256, Fr};

    #[test]
    fn generate_constraints() {
        let (_c, input, current_hash, output) = generate_sha256_round_constraints::<Bn256>();
        assert_eq!(input.len(), 512);
        assert_eq!(current_hash.len(), 256);
        assert_eq!(output.len(), 256);
    }

    #[test]
    fn generate_witness() {
        let witness =
            generate_sha256_round_witness::<Bn256>(&vec![Fr::one(); 512], &vec![Fr::zero(); 256]);
        assert_eq!(witness.len(), 26935);
    }

    #[test]
    fn test_cs() {
        use sapling_crypto::circuit::test::TestConstraintSystem;

        let mut cs: TestConstraintSystem<Bn256> = TestConstraintSystem::new();

        let _ = sha256_round(
            &mut cs,
            &vec![Some(Fr::zero()); 512],
            &vec![Some(Fr::one()); 256],
        )
        .unwrap();

        assert!(cs.is_satisfied());
    }
}
