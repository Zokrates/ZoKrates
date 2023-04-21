use nova_snark::traits::circuit::TrivialTestCircuit;
use nova_snark::CompressedSNARK;
use nova_snark::PublicParams;
use nova_snark::RecursiveSNARK;
use pasta_curves::{Fp, Fq};
use std::io;
use std::time::Instant;
use typed_arena::Arena;
use zokrates_bellperson::nova::NovaComputation;
use zokrates_bellperson::Computation;
use zokrates_core::compile::{compile, CompileConfig};
use zokrates_field::PallasField;

type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;

fn main() {
    // create a circuit for the incremental computation

    let cube = r#"
        def main(field x) -> field {
            return x**3;
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

    let circuit_primary = NovaComputation::try_from(Computation::without_witness(&prog)).unwrap();
    let circuit_secondary = TrivialTestCircuit::default();

    type C1<'a> = NovaComputation<'a, PallasField>;
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
    type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<G1>;
    type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<G2>;
    type S1 = nova_snark::spartan::RelaxedR1CSSNARK<G1, EE1>;
    type S2 = nova_snark::spartan::RelaxedR1CSSNARK<G2, EE2>;

    let (pk, vk) = CompressedSNARK::<_, _, _, _, S1, S2>::setup(&pp).unwrap();

    let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &pk, &recursive_snark);
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
    let res = compressed_snark.verify(&vk, num_steps, z0_primary, z0_secondary);
    println!(
        "CompressedSNARK::verify: {:?}, took {:?}",
        res.is_ok(),
        start.elapsed()
    );
    assert!(res.is_ok());
    println!("=========================================================");
}
