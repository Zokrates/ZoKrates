extern crate assert_cli;

#[cfg(test)]
mod integration {
    use assert_cli;
    use std::fs::{File};
    use std::path::Path;
    use std::io;
    use std::io::prelude::*;
    use std::fs::{self};

    // one possible implementation of walking a directory only visiting files
    fn visit_dirs(dir: &Path) -> io::Result<()> {
        if dir.is_dir() {
            for entry in fs::read_dir(dir)? {
                let entry = entry?;
                let path = entry.path();
                if path.is_dir() {
                    visit_dirs(&path)?;
                } else {
                    assert_eq!(path.into_os_string().into_string().unwrap(), "abc".to_string());
                }
            }
        }
        Ok(())
    }

    #[test]
    fn simple_add() {
    	test_compile_and_witness("./tests/code/simple_add.code", "./tests/code/simple_add.expected.out.code", "-a 1 2", "./tests/code/simple_add.expected.witness")
    }

    #[test]
    fn t() {
        visit_dirs(Path::new("./tests/code"));
    }

    fn test_compile_and_witness(program_path: &str, expected_flattened_code_path: &str, arguments: &str, expected_witness_path: &str) {
    	let flattened_path = "./tests/tmp/out";
    	let flattened_code_path = "./tests/tmp/out.code";
    	let witness_path = "./tests/tmp/witness";

    	// compile
        assert_cli::Assert::command(&["cargo", "run", "--", "compile", "-i", program_path, "-o", flattened_path])
            .succeeds()
            .unwrap();

        // compile
        assert_cli::Assert::command(&["cargo", "run", "--", "compute-witness", "-i", flattened_path, "-o", witness_path, "-a", "1", "2"])
            .succeeds()
            .unwrap();

    	// load the expected result
    	let mut expected_flattened_code_file = File::open(expected_flattened_code_path).unwrap();
        let mut expected_flattened_code = String::new();
		expected_flattened_code_file.read_to_string(&mut expected_flattened_code);

		// load the expected witness
		let mut expected_witness_file = File::open(expected_witness_path).unwrap();
		let mut expected_witness = String::new();
		expected_witness_file.read_to_string(&mut expected_witness);

		// load the actual result
    	let mut flattened_code_file = File::open(flattened_code_path).unwrap();
        let mut flattened_code = String::new();
		flattened_code_file.read_to_string(&mut flattened_code);

		// load the actual witness
    	let mut witness_file = File::open(witness_path).unwrap();
        let mut witness = String::new();
		witness_file.read_to_string(&mut witness);

		// check equality
		assert_eq!(flattened_code, expected_flattened_code);
		assert_eq!(witness, expected_witness);
    }
}