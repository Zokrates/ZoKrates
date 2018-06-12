extern crate assert_cli;
extern crate serde_json;

#[cfg(test)]
mod integration {
    use assert_cli;
    use std::fs::{File};
    use std::path::Path;
    use std::io::prelude::*;
    use std::fs::{self};
    use std::panic;
    use serde_json;
    use serde_json::Value;

    fn setup() {
        fs::create_dir(".tmp").unwrap();
    }

    fn teardown() {
        fs::remove_dir_all(".tmp").unwrap();
    } 
    
    #[test]
    fn run_integration_tests() {
        // see https://medium.com/@ericdreichert/test-setup-and-teardown-in-rust-without-a-framework-ba32d97aa5ab
        setup();

        let result = panic::catch_unwind(|| {
            test_compile_and_witness_dir()
        });

        teardown();

        assert!(result.is_ok())
    }

    fn test_compile_and_witness_dir() {
        let dir = Path::new("./tests/code");
        if dir.is_dir() {
            for entry in fs::read_dir(dir).unwrap() {
                let entry = entry.unwrap();
                let path = entry.path();
                if path.extension().unwrap() == "witness" {
                    let program_name = Path::new(Path::new(path.file_stem().unwrap()).file_stem().unwrap());
                    let prog = dir.join(program_name).with_extension("code");
                    let flat = dir.join(program_name).with_extension("expected.out.code");
                    let witness = dir.join(program_name).with_extension("expected.witness");
                    let args = dir.join(program_name).with_extension("arguments.json");
                    test_compile_and_witness(program_name.to_str().unwrap(), &prog, &flat, &args, &witness);
                }
            }
        }
    }

    fn test_compile_and_witness(program_name: &str, program_path: &Path, expected_flattened_code_path: &Path, arguments_path: &Path, expected_witness_path: &Path) {
        let tmp_base = Path::new(".tmp/");
        let test_case_path = tmp_base.join(program_name);
    	let flattened_path = tmp_base.join(program_name).join("out");
    	let flattened_code_path = tmp_base.join(program_name).join("out").with_extension("code");
    	let witness_path = tmp_base.join(program_name).join("witness");

        // create a tmp folder to store artifacts
        fs::create_dir(test_case_path).unwrap();

        // prepare compile arguments
        let mut compile = vec!["./target/debug/zokrates", "compile", "-i", program_path.to_str().unwrap(), "-o", flattened_path.to_str().unwrap()];

        if program_name.contains("sha_libsnark") {
            compile.push("--gadgets");
            compile.push("--optimized");
        }

    	// compile
        assert_cli::Assert::command(&compile)
            .succeeds()
            .unwrap();

        // compute
        let arguments: Value = serde_json::from_reader(File::open(arguments_path).unwrap()).unwrap();

        let arguments_str_list: Vec<String> = arguments.as_array().unwrap().iter().map(|i| match *i {
            Value::Number(ref n) => n.to_string(),
            _ => panic!(format!("Cannot read arguments. Check {}", arguments_path.to_str().unwrap()))
        }).collect();

        let mut compute = vec!["cargo", "run", "--", "compute-witness", "-i", flattened_path.to_str().unwrap(), "-o", witness_path.to_str().unwrap(), "-a"];

        for arg in arguments_str_list.iter() {
            compute.push(arg);
        }
        
        assert_cli::Assert::command(&compute)
            .succeeds()
            .unwrap();

    	// load the expected result
    	let mut expected_flattened_code_file = File::open(&expected_flattened_code_path).unwrap();
        let mut expected_flattened_code = String::new();
		expected_flattened_code_file.read_to_string(&mut expected_flattened_code).unwrap();

		// load the expected witness
		let mut expected_witness_file = File::open(&expected_witness_path).unwrap();
		let mut expected_witness = String::new();
		expected_witness_file.read_to_string(&mut expected_witness).unwrap();

		// load the actual result
    	let mut flattened_code_file = File::open(&flattened_code_path).unwrap();
        let mut flattened_code = String::new();
		flattened_code_file.read_to_string(&mut flattened_code).unwrap();

		// load the actual witness
    	let mut witness_file = File::open(&witness_path).unwrap();
        let mut witness = String::new();
		witness_file.read_to_string(&mut witness).unwrap();

		// check equality
        assert_eq!(flattened_code, expected_flattened_code, "Flattening failed for {}\n\nExpected\n\n{}\n\nGot\n\n{}", program_path.to_str().unwrap(), expected_flattened_code.as_str(), flattened_code.as_str());
        for line in expected_witness.as_str().split("\n") {
            assert!(witness.contains(line), "Witness generation failed for {}\n\nLine \"{}\" not found in witness", program_path.to_str().unwrap(), line);
        }
    }
}