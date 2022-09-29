use bellperson::gadgets::num::AllocatedNum;
use bellperson::SynthesisError;
use nova_snark::traits::circuit::StepCircuit;
use nova_snark::traits::circuit::TrivialTestCircuit;
use nova_snark::CompressedSNARK;
use nova_snark::PublicParams;
use nova_snark::RecursiveSNARK;
use pasta_curves::{Fp, Fq};
use std::time::Instant;
use std::{collections::BTreeMap, io};
use typed_arena::Arena;
use zokrates_ast::ir::{Statement, Witness};
use zokrates_bellperson::Computation;
use zokrates_core::compile::{compile, CompileConfig};
use zokrates_field::{BellpersonFieldExtensions, PallasField};
use zokrates_interpreter::Interpreter;

type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;

// we implemented a bellperson extension in zokrates_field for pallas so that we can convert back and forth to the bellperson data structures

// let's implement the StepCircuit trait for ir programs

// we use the newtype pattern to enable implementing a trait on ir::Prog because it is defined in another crate (zokrates_ast)

#[derive(Clone, Debug)]
struct PallasComputation(Computation<PallasField, Vec<Statement<PallasField>>>);

impl StepCircuit<Fq> for PallasComputation {
    fn arity(&self) -> usize {
        let input_count = self.0.program.arguments.len();
        let output_count = self.0.program.return_count;
        assert_eq!(input_count, output_count);
        input_count
    }

    fn synthesize<CS: bellperson::ConstraintSystem<Fq>>(
        &self,
        cs: &mut CS,
        input: &[bellperson::gadgets::num::AllocatedNum<Fq>],
    ) -> Result<Vec<bellperson::gadgets::num::AllocatedNum<Fq>>, bellperson::SynthesisError> {
        assert_eq!(self.0.program.arguments.len(), input.len());

        let mut symbols = BTreeMap::new();

        let mut witness = Witness::default();

        // populate the witness if we got some input values
        if input[0].get_value().is_some() {
            let interpreter = Interpreter::default();
            let inputs: Vec<_> = input
                .iter()
                .map(|v| PallasField::from_bellperson(v.get_value().unwrap()))
                .collect();
            witness = interpreter
                .execute(self.0.program.clone(), &inputs)
                .unwrap();
        }

        // allocate the inputs
        for (p, allocated_num) in self.0.program.arguments.iter().zip(input) {
            symbols.insert(p.id, allocated_num.get_variable());
        }

        // allocate the outputs

        let outputs: Vec<_> = self
            .0
            .program
            .returns()
            .iter()
            .map(|v| {
                assert!(v.id < 0); // this should indeed be an output
                let wire = AllocatedNum::alloc(
                    cs.namespace(|| format!("NOVA_INCREMENTAL_OUTPUT_{}", -v.id - 1)),
                    || {
                        Ok(witness
                            .0
                            .remove(v)
                            .ok_or(SynthesisError::AssignmentMissing)?
                            .into_bellperson())
                    },
                )
                .unwrap();
                symbols.insert(*v, wire.get_variable());
                wire
            })
            .collect();

        self.0
            .clone()
            .synthesize_input_to_output(cs, &mut symbols, &mut witness)?;

        Ok(outputs)
    }

    fn output(&self, z: &[Fq]) -> Vec<Fq> {
        let interpreter = Interpreter::default();
        let inputs: Vec<_> = z.iter().map(|v| PallasField::from_bellperson(*v)).collect();
        let output = interpreter
            .execute(self.0.program.clone(), &inputs)
            .unwrap();
        output
            .return_values()
            .into_iter()
            .map(|v| v.into_bellperson())
            .collect()
    }
}

fn main() {
    // create a circuit for the incremental computation

    let cube = r#"
        def main(field x) -> field {
            return x**123;
        }
    "#;

    let arena = Arena::new();

    let artifacts = compile::<PallasField, io::Error>(
        cube.to_string(),
        "main".into(),
        None,
        CompileConfig::default(),
        &arena,
    )
    .unwrap();

    let prog = artifacts.prog().collect();

    let circuit_primary = PallasComputation(Computation::without_witness(prog));
    let circuit_secondary = TrivialTestCircuit::default();

    type C1 = PallasComputation;
    type C2 = TrivialTestCircuit<Fp>;

    // produce public parameters
    println!("Producing public parameters...");
    let pp =
        PublicParams::<G1, G2, C1, C2>::setup(circuit_primary.clone(), circuit_secondary.clone());

    // produce a recursive SNARK
    println!("Generating a RecursiveSNARK...");
    let mut recursive_snark: Option<RecursiveSNARK<G1, G2, C1, C2>> = None;

    let num_steps: usize = 10;

    let z0_primary = vec![Fq::one() + Fq::one()];
    let z0_secondary = vec![Fp::one()];

    for i in 0..num_steps {
        let start = Instant::now();
        let res = RecursiveSNARK::prove_step(
            &pp,
            recursive_snark,
            circuit_primary.clone(),
            circuit_secondary.clone(),
            z0_primary.clone(),
            z0_secondary.clone(),
        );
        assert!(res.is_ok());
        println!(
            "RecursiveSNARK::prove_step {}: {:?}, took {:?} ",
            i,
            res.is_ok(),
            start.elapsed()
        );
        recursive_snark = Some(res.unwrap());
        println!("{:#?}", recursive_snark.as_ref().unwrap().zi_primary);
    }

    assert!(recursive_snark.is_some());
    let recursive_snark = recursive_snark.unwrap();

    // verify the recursive SNARK
    println!("Verifying a RecursiveSNARK...");
    let start = Instant::now();
    let res = recursive_snark.verify(&pp, num_steps, z0_primary.clone(), z0_secondary.clone());

    println!("{:#?}", res);

    println!(
        "RecursiveSNARK::verify: {:?}, took {:?}",
        res.is_ok(),
        start.elapsed()
    );
    assert!(res.is_ok());

    // produce a compressed SNARK
    println!("Generating a CompressedSNARK using Spartan with IPA-PC...");
    let start = Instant::now();
    type S1 = nova_snark::spartan_with_ipa_pc::RelaxedR1CSSNARK<G1>;
    type S2 = nova_snark::spartan_with_ipa_pc::RelaxedR1CSSNARK<G2>;
    let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &recursive_snark);
    println!(
        "CompressedSNARK::prove: {:?}, took {:?}",
        res.is_ok(),
        start.elapsed()
    );
    assert!(res.is_ok());
    let compressed_snark = res.unwrap();

    // verify the compressed SNARK
    println!("Verifying a CompressedSNARK...");
    let start = Instant::now();
    let res = compressed_snark.verify(&pp, num_steps, z0_primary, z0_secondary);
    println!(
        "CompressedSNARK::verify: {:?}, took {:?}",
        res.is_ok(),
        start.elapsed()
    );
    assert!(res.is_ok());
    println!("=========================================================");
}
