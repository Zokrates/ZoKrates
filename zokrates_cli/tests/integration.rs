extern crate assert_cli;
extern crate serde_json;

#[cfg(test)]
mod integration {
    use assert_cli;
    use serde_json;
    use serde_json::Value;
    use std::fs;
    use std::fs::File;
    use std::io::prelude::*;
    use std::panic;
    use std::path::Path;
    use tempdir::TempDir;

    #[test]
    #[ignore]
    fn test_compile_and_witness_dir() {
        let dir = Path::new("./code");
        if dir.is_dir() {
            for entry in fs::read_dir(dir).unwrap() {
                let entry = entry.unwrap();
                let path = entry.path();
                if path.extension().unwrap() == "witness" {
                    let program_name =
                        Path::new(Path::new(path.file_stem().unwrap()).file_stem().unwrap());
                    let prog = dir.join(program_name).with_extension("zok");
                    let witness = dir.join(program_name).with_extension("expected.witness");
                    let args = dir.join(program_name).with_extension("arguments.json");
                    test_compile_and_witness(
                        program_name.to_str().unwrap(),
                        &prog,
                        &args,
                        &witness,
                    );
                }
            }
        }
    }

    fn test_compile_and_witness(
        program_name: &str,
        program_path: &Path,
        arguments_path: &Path,
        expected_witness_path: &Path,
    ) {
        let tmp_dir = TempDir::new(".tmp").unwrap();
        let tmp_base = tmp_dir.path();
        let test_case_path = tmp_base.join(program_name);
        let flattened_path = tmp_base.join(program_name).join("out");
        let witness_path = tmp_base.join(program_name).join("witness");
        let inline_witness_path = tmp_base.join(program_name).join("inline_witness");
        let verification_key_path = tmp_base
            .join(program_name)
            .join("verification")
            .with_extension("key");
        let proving_key_path = tmp_base
            .join(program_name)
            .join("proving")
            .with_extension("key");
        let verification_contract_path = tmp_base
            .join(program_name)
            .join("verifier")
            .with_extension("sol");

        // create a tmp folder to store artifacts
        fs::create_dir(test_case_path).unwrap();

        // prepare compile arguments
        let compile = vec![
            "../target/release/zokrates",
            "compile",
            "-i",
            program_path.to_str().unwrap(),
            "-o",
            flattened_path.to_str().unwrap(),
            "--light",
        ];

        if program_name.contains("sha") {
            // we don't want to test libsnark integrations if libsnark is not available
            #[cfg(not(feature = "libsnark"))]
            return;
        }

        // compile
        assert_cli::Assert::command(&compile).succeeds().unwrap();

        // COMPUTE_WITNESS
        let arguments: Value =
            serde_json::from_reader(File::open(arguments_path).unwrap()).unwrap();

        let arguments_str_list: Vec<String> = arguments
            .as_array()
            .unwrap()
            .iter()
            .map(|i| match *i {
                Value::Number(ref n) => n.to_string(),
                _ => panic!(format!(
                    "Cannot read arguments. Check {}",
                    arguments_path.to_str().unwrap()
                )),
            })
            .collect();

        // WITH `-a <arguments>`

        let mut compute_inline = vec![
            "../target/release/zokrates",
            "compute-witness",
            "-i",
            flattened_path.to_str().unwrap(),
            "-o",
            inline_witness_path.to_str().unwrap(),
            "-a",
        ];

        for arg in arguments_str_list.iter() {
            compute_inline.push(arg);
        }

        assert_cli::Assert::command(&compute_inline)
            .succeeds()
            .unwrap();

        // WITH stdin ARGUMENTS

        let compute = vec![
            "../target/release/zokrates",
            "compute-witness",
            "-i",
            flattened_path.to_str().unwrap(),
            "-o",
            witness_path.to_str().unwrap(),
        ];

        assert_cli::Assert::command(&compute)
            .stdin(&arguments_str_list.join(" "))
            .succeeds()
            .unwrap();

        // load the expected witness
        let mut expected_witness_file = File::open(&expected_witness_path).unwrap();
        let mut expected_witness = String::new();
        expected_witness_file
            .read_to_string(&mut expected_witness)
            .unwrap();

        // load the actual witness
        let mut witness_file = File::open(&witness_path).unwrap();
        let mut witness = String::new();
        witness_file.read_to_string(&mut witness).unwrap();

        // load the actual inline witness
        let mut inline_witness_file = File::open(&inline_witness_path).unwrap();
        let mut inline_witness = String::new();
        inline_witness_file
            .read_to_string(&mut inline_witness)
            .unwrap();

        assert_eq!(inline_witness, witness);

        for line in expected_witness.as_str().split("\n") {
            assert!(
                witness.contains(line),
                "Witness generation failed for {}\n\nLine \"{}\" not found in witness",
                program_path.to_str().unwrap(),
                line
            );
        }

        #[cfg(feature = "libsnark")]
        let schemes = ["pghr13", "gm17", "g16"];
        #[cfg(not(feature = "libsnark"))]
        let schemes = ["g16"];

        for scheme in &schemes {
            // SETUP
            assert_cli::Assert::command(&[
                "../target/release/zokrates",
                "setup",
                "-i",
                flattened_path.to_str().unwrap(),
                "-p",
                proving_key_path.to_str().unwrap(),
                "-v",
                verification_key_path.to_str().unwrap(),
                "--proving-scheme",
                scheme,
            ])
            .succeeds()
            .unwrap();

            // EXPORT-VERIFIER
            assert_cli::Assert::command(&[
                "../target/release/zokrates",
                "export-verifier",
                "-i",
                verification_key_path.to_str().unwrap(),
                "-o",
                verification_contract_path.to_str().unwrap(),
                "--proving-scheme",
                scheme,
            ])
            .succeeds()
            .unwrap();

            let mut verifier_file = File::open(&verification_contract_path).unwrap();
            let mut verifier_string = String::new();
            verifier_file.read_to_string(&mut verifier_string).unwrap();

            let solc_json_input = format!(
                r#"{{"language": "Solidity", "sources": {{ "this": {{ "content": {:?} }} }} }}"#,
                verifier_string
            );

            assert_cli::Assert::command(&["solcjs", "--standard-json"])
                .stdin(&solc_json_input)
                .succeeds()
                .stdout()
                .doesnt_contain(r#""severity":"error""#)
                .unwrap();

            // GENERATE-PROOF
            assert_cli::Assert::command(&[
                "../target/release/zokrates",
                "generate-proof",
                "-i",
                flattened_path.to_str().unwrap(),
                "-w",
                witness_path.to_str().unwrap(),
                "-p",
                proving_key_path.to_str().unwrap(),
                "--proving-scheme",
                scheme,
            ])
            .succeeds()
            .unwrap();
        }
    }
}
