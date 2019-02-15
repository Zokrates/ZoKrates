use bellman::groth16::Parameters;
use ir;
use ir::backend::Computation;
use proof_system::Metadata;
use proof_system::ProofSystem;
use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;
use zokrates_field::field::FieldPrime;

pub struct G16 {}
impl ProofSystem for G16 {
    fn setup(&self, program: ir::Prog<FieldPrime>, pk_path: &str, _vk_path: &str) -> Metadata {
        let parameters = Computation::without_witness(program).setup();
        let parameters_file = File::create(PathBuf::from(pk_path)).unwrap();
        parameters.write(parameters_file).unwrap();
        // TODO write pk, vk to files
        Metadata {
            offset: 42,
            variables: vec![],
        }
    }

    fn generate_proof(
        &self,
        program: ir::Prog<FieldPrime>,
        witness: ir::Witness<FieldPrime>,
        _metadata: Metadata,
        pk_path: &str,
        proof_path: &str,
    ) -> bool {
        let computation = Computation::with_witness(program, witness);
        let parameters_file = File::open(PathBuf::from(pk_path)).unwrap();

        let params = Parameters::read(parameters_file, true).unwrap();

        let proof = computation.prove(params);

        let proof_file = File::create(PathBuf::from(proof_path)).unwrap();
        proof.write(proof_file).unwrap();
        true
    }

    fn export_solidity_verifier(&self, reader: BufReader<File>) -> String {
        unimplemented!()
    }
}
