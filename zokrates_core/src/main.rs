extern crate zokrates_core;
extern crate zokrates_field;

use zokrates_core::compile::CompilationArtifacts;
use zokrates_core::proof_system::{self, ProofSystem, SetupKeypair};
use zokrates_field::field::FieldPrime;

fn main() {
    fn resolve_closure<'a>(
        _l: String,
        _p: String,
    ) -> Result<(String, String), zokrates_core::imports::Error> {
        Ok((
            String::from("def main() -> ():\nreturn"),
            String::from("test"),
        ))
    };

    let artifacts: CompilationArtifacts<FieldPrime> = zokrates_core::compile::compile(
        String::from("def main(field a) -> (field): return a"),
        String::from("main"),
        Some(&resolve_closure),
    )
        .expect("Could not compile program");

    let prog = artifacts.prog();

    let scheme = proof_system::G16::new();
    let keypair: SetupKeypair = scheme.setup(prog.clone());

    let _verifier = scheme.export_solidity_verifier(keypair.vk.clone(), false);
    println!("{}", _verifier);

    println!("{}", keypair.vk.clone());

    let witness = prog.clone().execute(&vec![FieldPrime::from(1)]).unwrap();
    let proof = scheme.generate_proof(prog.clone(), witness, keypair.pk);

    println!("{}", proof);

    let verified = scheme.verify(keypair.vk.clone(), proof);
    println!("verify: {}", verified);
}
