use bellman::kate_commitment::{Crs, CrsForMonomialForm};
use bellman::plonk::better_cs::cs::PlonkCsWidth4WithNextStepParams;
use bellman::plonk::commitments::transcript::keccak_transcript::RollingKeccakTranscript;
use bellman::plonk::{
    is_satisfied, make_verification_key, prove_by_steps, setup, transpile, verify,
    Proof as BellmanProof, SetupPolynomials, VerificationKey as BellmanVerificationKey,
};

use num_cpus;
use zokrates_field::BellmanPlonkFieldExtensions;
use zokrates_field::Field;
use zokrates_proof_systems::{Backend, Proof, SetupKeypair, UniversalBackend};

use crate::Computation;
use crate::{parse_fr, serialization, Bellman};
use crate::{parse_g1, parse_g2};
use std::io::Cursor;
use std::marker::PhantomData;
use zokrates_ast::ir::{ProgIterator, Statement, Witness};
use zokrates_proof_systems::plonk::{Plonk, ProofPoints, VerificationKey};
use zokrates_proof_systems::Scheme;

impl<T: Field + BellmanPlonkFieldExtensions> UniversalBackend<T, Plonk> for Bellman {
    fn universal_setup(size: u32) -> Vec<u8> {
        let crs: Crs<T::BellmanEngine, CrsForMonomialForm> =
            Crs::<T::BellmanEngine, CrsForMonomialForm>::dummy_crs(2usize.pow(size) as usize);
        let mut res = vec![];
        crs.write(&mut res).unwrap();
        res
    }

    fn setup<I: IntoIterator<Item = Statement<T>>>(
        srs: Vec<u8>,
        program: ProgIterator<T, I>,
    ) -> Result<SetupKeypair<T, Plonk>, String> {
        let crs = Crs::read(Cursor::new(srs)).unwrap();

        let program = program.collect();

        let hints = transpile(Computation::without_witness(program.clone())).unwrap();

        let pols = setup(Computation::without_witness(program), &hints).unwrap();

        let mut pk = vec![];

        pols.write(&mut pk).unwrap();

        let vk = make_verification_key(&pols, &crs).unwrap();

        assert_eq!(
            {
                let mut w = vec![];
                deserialize_vk::<T>(serialize_vk::<T>(vk.clone()))
                    .write(&mut w)
                    .unwrap();
                w
            },
            {
                let mut w = vec![];
                vk.write(&mut w).unwrap();
                w
            }
        );

        let vk = serialize_vk::<T>(vk);

        assert_eq!(serialize_vk::<T>(deserialize_vk::<T>(vk.clone())), vk);

        Ok(SetupKeypair { vk, pk })
    }
}

impl<T: Field + BellmanPlonkFieldExtensions> Backend<T, Plonk> for Bellman {
    fn generate_proof<I: IntoIterator<Item = Statement<T>>>(
        program: ProgIterator<T, I>,
        witness: Witness<T>,
        proving_key: Vec<u8>,
    ) -> Proof<T, Plonk> {
        let program = program.collect();
        let computation = Computation::with_witness(program.clone(), witness);
        let hints = transpile(Computation::without_witness(program)).unwrap();

        assert!(is_satisfied(computation.clone(), &hints).is_ok());

        let proving_key = Cursor::new(proving_key);

        let setup: SetupPolynomials<T::BellmanEngine, PlonkCsWidth4WithNextStepParams> =
            SetupPolynomials::read(proving_key).unwrap();

        let num_cpus = num_cpus::get_physical();
        println!("Num CPUs: {}", num_cpus);
        let proof: BellmanProof<T::BellmanEngine, PlonkCsWidth4WithNextStepParams> =
            prove_by_steps::<_, _, RollingKeccakTranscript<_>>(
                computation,
                &hints,
                &setup,
                None,
                &Crs::<T::BellmanEngine, CrsForMonomialForm>::dummy_crs(2usize.pow(10)),
                None,
                Some(16),
            )
            .unwrap();

        assert_eq!(
            {
                let mut w = vec![];
                deserialize_proof::<T>(serialize_proof(proof.clone()))
                    .write(&mut w)
                    .unwrap();
                w
            },
            {
                let mut w = vec![];
                proof.write(&mut w).unwrap();
                w
            }
        );

        let proof = serialize_proof(proof);

        assert_eq!(
            serialize_proof::<T>(deserialize_proof(proof.clone())),
            proof
        );

        proof
    }

    fn verify(vk: <Plonk as Scheme<T>>::VerificationKey, proof: Proof<T, Plonk>) -> bool {
        let vk = deserialize_vk::<T>(vk);

        let proof = deserialize_proof::<T>(proof);

        verify::<_, RollingKeccakTranscript<_>>(&proof, &vk).unwrap()
    }
}

fn deserialize_vk<T: Field + BellmanPlonkFieldExtensions>(
    vk: <Plonk as Scheme<T>>::VerificationKey,
) -> BellmanVerificationKey<T::BellmanEngine, PlonkCsWidth4WithNextStepParams> {
    BellmanVerificationKey {
        n: vk.n as usize,
        num_inputs: vk.num_inputs as usize,
        selector_commitments: vk
            .selector_commitments
            .into_iter()
            .map(serialization::to_g1::<T>)
            .collect(),
        next_step_selector_commitments: vk
            .next_step_selector_commitments
            .into_iter()
            .map(serialization::to_g1::<T>)
            .collect(),
        permutation_commitments: vk
            .permutation_commitments
            .into_iter()
            .map(serialization::to_g1::<T>)
            .collect(),
        non_residues: vk
            .non_residues
            .into_iter()
            .map(serialization::to_fr::<T>)
            .collect(),
        g2_elements: vk
            .g2_elements
            .into_iter()
            .map(serialization::to_g2::<T>)
            .collect::<Vec<_>>()
            .try_into()
            .map_err(|_| ())
            .unwrap(),
        _marker: PhantomData,
    }
}

fn serialize_vk<T: Field + BellmanPlonkFieldExtensions>(
    vk: BellmanVerificationKey<T::BellmanEngine, PlonkCsWidth4WithNextStepParams>,
) -> <Plonk as Scheme<T>>::VerificationKey {
    let domain = bellman::plonk::domains::Domain::<
        <T::BellmanEngine as bellman::pairing::ff::ScalarEngine>::Fr,
    >::new_for_size(vk.n.next_power_of_two() as u64)
    .unwrap();
    let omega = parse_fr::<T>(&domain.generator);

    VerificationKey {
        n: vk.n as u32,
        num_inputs: vk.num_inputs as u32,
        selector_commitments: vk.selector_commitments.iter().map(parse_g1::<T>).collect(),
        next_step_selector_commitments: vk
            .next_step_selector_commitments
            .iter()
            .map(parse_g1::<T>)
            .collect(),
        permutation_commitments: vk
            .permutation_commitments
            .iter()
            .map(parse_g1::<T>)
            .collect(),
        non_residues: vk.non_residues.iter().map(parse_fr::<T>).collect(),
        g2_elements: vk
            .g2_elements
            .iter()
            .map(parse_g2::<T>)
            .collect::<Vec<_>>()
            .try_into()
            .map_err(|_| ())
            .unwrap(),
        omega,
    }
}

fn deserialize_proof<T: Field + BellmanPlonkFieldExtensions>(
    proof: Proof<T, Plonk>,
) -> BellmanProof<T::BellmanEngine, PlonkCsWidth4WithNextStepParams> {
    let inputs = proof.inputs;
    let proof = proof.proof;

    BellmanProof {
        num_inputs: proof.num_inputs as usize,
        n: proof.n as usize,
        input_values: inputs.into_iter().map(serialization::to_fr::<T>).collect(),
        wire_commitments: proof
            .wire_commitments
            .into_iter()
            .map(serialization::to_g1::<T>)
            .collect(),
        grand_product_commitment: serialization::to_g1::<T>(proof.grand_product_commitment),
        quotient_poly_commitments: proof
            .quotient_poly_commitments
            .into_iter()
            .map(serialization::to_g1::<T>)
            .collect(),
        wire_values_at_z: proof
            .wire_values_at_z
            .into_iter()
            .map(serialization::to_fr::<T>)
            .collect(),
        wire_values_at_z_omega: proof
            .wire_values_at_z_omega
            .into_iter()
            .map(serialization::to_fr::<T>)
            .collect(),
        grand_product_at_z_omega: serialization::to_fr::<T>(proof.grand_product_at_z_omega),
        quotient_polynomial_at_z: serialization::to_fr::<T>(proof.quotient_polynomial_at_z),
        linearization_polynomial_at_z: serialization::to_fr::<T>(
            proof.linearization_polynomial_at_z,
        ),
        permutation_polynomials_at_z: proof
            .permutation_polynomials_at_z
            .into_iter()
            .map(serialization::to_fr::<T>)
            .collect(),
        opening_at_z_proof: serialization::to_g1::<T>(proof.opening_at_z_proof),
        opening_at_z_omega_proof: serialization::to_g1::<T>(proof.opening_at_z_omega_proof),
        _marker: PhantomData,
    }
}

fn serialize_proof<T: Field + BellmanPlonkFieldExtensions>(
    proof: BellmanProof<T::BellmanEngine, PlonkCsWidth4WithNextStepParams>,
) -> Proof<T, Plonk> {
    let public_inputs = proof.input_values.iter().map(parse_fr::<T>).collect();

    let proof = ProofPoints {
        num_inputs: proof.num_inputs as u32,
        n: proof.n as u32,
        wire_commitments: proof
            .wire_commitments
            .iter()
            .map(|c| parse_g1::<T>(c))
            .collect(),
        grand_product_commitment: parse_g1::<T>(&proof.grand_product_commitment),
        quotient_poly_commitments: proof
            .quotient_poly_commitments
            .iter()
            .map(|c| parse_g1::<T>(c))
            .collect(),
        wire_values_at_z: proof
            .wire_values_at_z
            .iter()
            .map(|v| parse_fr::<T>(v))
            .collect(),
        wire_values_at_z_omega: proof
            .wire_values_at_z_omega
            .iter()
            .map(|v| parse_fr::<T>(v))
            .collect(),
        grand_product_at_z_omega: parse_fr::<T>(&proof.grand_product_at_z_omega),
        quotient_polynomial_at_z: parse_fr::<T>(&proof.quotient_polynomial_at_z),
        linearization_polynomial_at_z: parse_fr::<T>(&proof.linearization_polynomial_at_z),
        permutation_polynomials_at_z: proof
            .permutation_polynomials_at_z
            .iter()
            .map(|v| parse_fr::<T>(v))
            .collect(),
        opening_at_z_proof: parse_g1::<T>(&proof.opening_at_z_proof),
        opening_at_z_omega_proof: parse_g1::<T>(&proof.opening_at_z_omega_proof),
    };

    Proof::new(proof, public_inputs)
}

#[cfg(test)]
mod tests {
    use bellman::plonk::commitments::transcript::Blake2sTranscript;
    use zokrates_field::Bn128Field;
    use zokrates_interpreter::Interpreter;

    use super::*;
    use zokrates_ast::common::{Parameter, Variable};
    use zokrates_ast::ir::{Prog, Statement};

    #[test]
    fn setup_prove_verify() {
        // the program `def main(public field a) -> field { return a }`
        let program: Prog<Bn128Field> = Prog {
            arguments: vec![Parameter::public(Variable::new(0))],
            return_count: 1,
            statements: vec![Statement::constraint(Variable::new(0), Variable::public(0))],
        };

        println!("{}", &program);

        // generate a dummy universal setup of size 2**10
        let crs: Crs<<Bn128Field as BellmanPlonkFieldExtensions>::BellmanEngine, CrsForMonomialForm> =
        Crs::<<Bn128Field as BellmanPlonkFieldExtensions>::BellmanEngine, CrsForMonomialForm>::dummy_crs(2usize.pow(10) as usize);

        // transpile
        let hints = transpile(Computation::without_witness(program.clone())).unwrap();

        // run a circuit specific (transparent) setup
        let pols = setup(Computation::without_witness(program.clone()), &hints).unwrap();

        // generate a verification key from the circuit specific setup and the crs
        let vk = make_verification_key(&pols, &crs).unwrap();

        // run the program
        let interpreter = Interpreter::default();

        // extract the witness
        let witness = interpreter
            .execute(program.clone(), &[Bn128Field::from(42)])
            .unwrap();

        // bundle the program and the witness together
        let computation = Computation::with_witness(program.clone(), witness);
        // transpile
        let hints = transpile(Computation::without_witness(program.clone())).unwrap();

        // check that the circuit is satisfied
        assert!(is_satisfied(computation.clone(), &hints).is_ok());

        // generate a proof with no setup precomputations and no init params for the transcript, using Blake2s
        let num_cpus = num_cpus::get_physical();
        println!("Num CPUs: {}", num_cpus);
        let proof: BellmanProof<
            <Bn128Field as BellmanPlonkFieldExtensions>::BellmanEngine,
            PlonkCsWidth4WithNextStepParams,
        > = prove_by_steps::<_, _, Blake2sTranscript<_>>(
            computation,
            &hints,
            &pols,
            None,
            &crs,
            None,
            Some(16),
        )
        .unwrap();

        // verify the proof using Blake2s
        let ans = verify::<_, Blake2sTranscript<_>>(&proof, &vk).unwrap();

        // check that the proof is verified
        assert!(ans);
    }
}
