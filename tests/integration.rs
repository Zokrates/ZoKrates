extern crate assert_cli;
extern crate serde_json;

#[cfg(test)]
mod integration {
    use assert_cli;
    use std::fs::{File};
    use std::path::Path;
    use std::io::prelude::*;
    use std::fs::{self};
    use serde_json;
    use serde_json::Value;
    
    #[test]
    fn test_compile_and_witness_dir() {
        let dir = Path::new("./tests/code");
        if dir.is_dir() {
            for entry in fs::read_dir(dir).unwrap() {
                let entry = entry.unwrap();
                let path = entry.path();
                if path.extension().unwrap() == "witness" {
                    let base = Path::new(Path::new(path.file_stem().unwrap()).file_stem().unwrap());
                    let prog = dir.join(base).with_extension("code");
                    let flat = dir.join(base).with_extension("expected.out.code");
                    let witness = dir.join(base).with_extension("expected.witness");
                    let args = dir.join(base).with_extension("arguments.json");
                    test_compile_and_witness(&prog, &flat, &args, &witness);
                }
            }
        }
    }

    fn test_compile_and_witness(program_path: &Path, expected_flattened_code_path: &Path, arguments_path: &Path, expected_witness_path: &Path) {
    	let flattened_path = Path::new("./tests/tmp/out");
    	let flattened_code_path = Path::new("./tests/tmp/out.code");
    	let witness_path = Path::new("./tests/tmp/witness");

    	// compile
        assert_cli::Assert::command(&["cargo", "run", "--", "compile", "-i", program_path.to_str().unwrap(), "-o", flattened_path.to_str().unwrap()])
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
    	let mut expected_flattened_code_file = File::open(expected_flattened_code_path).unwrap();
        let mut expected_flattened_code = String::new();
		expected_flattened_code_file.read_to_string(&mut expected_flattened_code).unwrap();

		// load the expected witness
		let mut expected_witness_file = File::open(expected_witness_path).unwrap();
		let mut expected_witness = String::new();
		expected_witness_file.read_to_string(&mut expected_witness).unwrap();

		// load the actual result
    	let mut flattened_code_file = File::open(flattened_code_path).unwrap();
        let mut flattened_code = String::new();
		flattened_code_file.read_to_string(&mut flattened_code).unwrap();

		// load the actual witness
    	let mut witness_file = File::open(witness_path).unwrap();
        let mut witness = String::new();
		witness_file.read_to_string(&mut witness).unwrap();

		// check equality
		assert_eq!(flattened_code, expected_flattened_code);
		assert_eq!(witness, expected_witness);
    }
}