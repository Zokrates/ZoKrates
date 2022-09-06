extern crate assert_cli;
extern crate ethabi;
extern crate primitive_types;
extern crate rand_0_4;
extern crate rand_0_8;
extern crate serde_json;
extern crate zokrates_solidity_test;

#[cfg(test)]
mod integration {
    use fs_extra::copy_items;
    use fs_extra::dir::CopyOptions;
    use pretty_assertions::assert_eq;
    use primitive_types::U256;
    use serde_json::from_reader;
    use std::fs;
    use std::fs::File;
    use std::io::{BufReader, Read};
    use std::panic;
    use std::path::Path;
    use tempdir::TempDir;
    use zokrates_abi::{parse_strict, Encode};
    use zokrates_ast::typed::abi::Abi;
    use zokrates_field::Bn128Field;
    use zokrates_proof_systems::{
        to_token::ToToken, Marlin, Proof, SolidityCompatibleScheme, G16, GM17,
        SOLIDITY_G2_ADDITION_LIB,
    };

    macro_rules! map(
    {
        $($key:expr => $value:expr),+ } => {
            {
                let mut m = ::std::collections::HashMap::new();
                $(m.insert($key, $value);)+
                m
            }
        };
    );

    #[test]
    #[ignore]
    fn test_compile_and_witness_dir() {
        let global_dir = TempDir::new("global").unwrap();
        let global_base = global_dir.path();
        let universal_setup_path = global_base.join("universal_setup.dat");

        // GENERATE A UNIVERSAL SETUP
        assert_cli::Assert::main_binary()
            .with_args(&[
                "universal-setup",
                "--size",
                "10",
                "--proving-scheme",
                "marlin",
                "--universal-setup-path",
                universal_setup_path.to_str().unwrap(),
            ])
            .succeeds()
            .unwrap();

        let dir = Path::new("./tests/code");
        assert!(dir.is_dir());
        for entry in fs::read_dir(dir).unwrap() {
            let entry = entry.unwrap();
            let path = entry.path();
            if path.extension().unwrap() == "witness" {
                let program_name =
                    Path::new(Path::new(path.file_stem().unwrap()).file_stem().unwrap());
                let prog = dir.join(program_name).with_extension("zok");
                let witness = dir.join(program_name).with_extension("expected.witness");
                let json_input = dir.join(program_name).with_extension("arguments.json");

                test_compile_and_witness(
                    program_name.to_str().unwrap(),
                    &prog,
                    &json_input,
                    &witness,
                    global_base,
                );
            }
        }
    }

    fn test_compile_and_witness(
        program_name: &str,
        program_path: &Path,
        inputs_path: &Path,
        expected_witness_path: &Path,
        global_path: &Path,
    ) {
        let tmp_dir = TempDir::new(program_name).unwrap();
        let tmp_base = tmp_dir.path();
        let test_case_path = tmp_base.join(program_name);
        let flattened_path = tmp_base.join(program_name).join("out");
        let abi_spec_path = tmp_base.join(program_name).join("abi.json");
        let witness_path = tmp_base.join(program_name).join("witness");
        let inline_witness_path = tmp_base.join(program_name).join("inline_witness");
        let proof_path = tmp_base.join(program_name).join("proof.json");
        let universal_setup_path = global_path.join("universal_setup.dat");
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

        let stdlib = std::fs::canonicalize("../zokrates_stdlib/stdlib").unwrap();

        // prepare compile arguments
        let compile = vec![
            "compile",
            "-i",
            program_path.to_str().unwrap(),
            "--stdlib-path",
            stdlib.to_str().unwrap(),
            "-s",
            abi_spec_path.to_str().unwrap(),
            "-o",
            flattened_path.to_str().unwrap(),
        ];

        // compile
        assert_cli::Assert::main_binary()
            .with_args(&compile)
            .succeeds()
            .unwrap();

        // COMPUTE_WITNESS
        let compute = vec![
            "compute-witness",
            "-i",
            flattened_path.to_str().unwrap(),
            "-s",
            abi_spec_path.to_str().unwrap(),
            "-o",
            witness_path.to_str().unwrap(),
            "--stdin",
            "--abi",
        ];

        // run witness-computation for ABI-encoded inputs through stdin
        let json_input_str = fs::read_to_string(inputs_path).unwrap();

        assert_cli::Assert::main_binary()
            .with_args(&compute)
            .stdin(&json_input_str)
            .succeeds()
            .unwrap();

        // run witness-computation for raw-encoded inputs (converted) with `-a <arguments>`

        // First we need to convert our test input into raw field elements. We need to ABI spec for that
        let file = File::open(&abi_spec_path)
            .map_err(|why| format!("Could not open {}: {}", flattened_path.display(), why))
            .unwrap();

        let mut reader = BufReader::new(file);

        let abi: Abi = from_reader(&mut reader)
            .map_err(|why| why.to_string())
            .unwrap();

        let signature = abi.signature();

        let inputs_abi: zokrates_abi::Inputs<zokrates_field::Bn128Field> =
            parse_strict(&json_input_str, signature.inputs)
                .map(zokrates_abi::Inputs::Abi)
                .map_err(|why| why.to_string())
                .unwrap();
        let inputs_raw: Vec<_> = inputs_abi
            .encode()
            .into_iter()
            .map(|v| v.to_string())
            .collect();

        let mut compute_inline = vec![
            "compute-witness",
            "-i",
            flattened_path.to_str().unwrap(),
            "-o",
            inline_witness_path.to_str().unwrap(),
        ];

        if !inputs_raw.is_empty() {
            compute_inline.push("-a");

            for arg in &inputs_raw {
                compute_inline.push(arg);
            }
        }

        assert_cli::Assert::main_binary()
            .with_args(&compute_inline)
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

        for line in expected_witness.as_str().split('\n') {
            assert!(
                witness.contains(line),
                "Witness generation failed for {}\n\nLine \"{}\" not found in witness",
                program_path.to_str().unwrap(),
                line
            );
        }

        let backends = map! {
            "bellman" => vec!["g16"],
            "ark" => vec!["g16", "gm17", "marlin"]
        };

        for (backend, schemes) in backends {
            for scheme in &schemes {
                println!("test with {}, {}", backend, scheme);
                // SETUP
                let setup = assert_cli::Assert::main_binary()
                    .with_args(&[
                        "setup",
                        "-i",
                        flattened_path.to_str().unwrap(),
                        "-p",
                        proving_key_path.to_str().unwrap(),
                        "-v",
                        verification_key_path.to_str().unwrap(),
                        "--backend",
                        backend,
                        "--proving-scheme",
                        scheme,
                        "--universal-setup-path",
                        universal_setup_path.to_str().unwrap(),
                    ])
                    .succeeds()
                    .stdout()
                    .doesnt_contain("This program is too small to generate a setup with Marlin")
                    .execute();

                if setup.is_ok() {
                    // GENERATE-PROOF
                    assert_cli::Assert::main_binary()
                        .with_args(&[
                            "generate-proof",
                            "-i",
                            flattened_path.to_str().unwrap(),
                            "-w",
                            witness_path.to_str().unwrap(),
                            "-p",
                            proving_key_path.to_str().unwrap(),
                            "--proving-scheme",
                            scheme,
                            "--backend",
                            backend,
                            "-j",
                            proof_path.to_str().unwrap(),
                        ])
                        .succeeds()
                        .unwrap();

                    // CLI VERIFICATION
                    assert_cli::Assert::main_binary()
                        .with_args(&[
                            "verify",
                            "--proof-path",
                            proof_path.to_str().unwrap(),
                            "--backend",
                            backend,
                            "-v",
                            verification_key_path.to_str().unwrap(),
                        ])
                        .succeeds()
                        .unwrap();

                    // EXPORT-VERIFIER
                    assert_cli::Assert::main_binary()
                        .with_args(&[
                            "export-verifier",
                            "-i",
                            verification_key_path.to_str().unwrap(),
                            "-o",
                            verification_contract_path.to_str().unwrap(),
                        ])
                        .succeeds()
                        .unwrap();

                    // TEST VERIFIER
                    // Get the contract
                    let contract_str =
                        std::fs::read_to_string(verification_contract_path.to_str().unwrap())
                            .unwrap();
                    match *scheme {
                        "marlin" => {
                            // Get the proof
                            let proof: Proof<Bn128Field, Marlin> = serde_json::from_reader(
                                File::open(proof_path.to_str().unwrap()).unwrap(),
                            )
                            .unwrap();

                            test_solidity_verifier(contract_str, proof);
                        }
                        "g16" => {
                            // Get the proof
                            let proof: Proof<Bn128Field, G16> = serde_json::from_reader(
                                File::open(proof_path.to_str().unwrap()).unwrap(),
                            )
                            .unwrap();

                            test_solidity_verifier(contract_str, proof);
                        }
                        "gm17" => {
                            // Get the proof
                            let proof: Proof<Bn128Field, GM17> = serde_json::from_reader(
                                File::open(proof_path.to_str().unwrap()).unwrap(),
                            )
                            .unwrap();

                            test_solidity_verifier(contract_str, proof);
                        }
                        _ => unreachable!(),
                    }
                }
            }
        }
    }

    fn test_solidity_verifier<S: SolidityCompatibleScheme<Bn128Field> + ToToken<Bn128Field>>(
        src: String,
        proof: Proof<Bn128Field, S>,
    ) {
        use ethabi::Token;
        use rand_0_8::{rngs::StdRng, SeedableRng};
        use zokrates_solidity_test::{address::*, contract::*, evm::*, to_be_bytes};

        // Setup EVM
        let mut rng = StdRng::from_seed([0; 32]);
        let mut evm = Evm::default();
        let deployer = Address::random(&mut rng);
        evm.create_account(&deployer, 0);

        // Compile lib
        let g2_lib =
            Contract::compile_from_src_string(SOLIDITY_G2_ADDITION_LIB, "BN256G2", true, &[])
                .unwrap();

        // Deploy lib
        let create_result = evm
            .deploy(g2_lib.encode_create_contract_bytes(&[]).unwrap(), &deployer)
            .unwrap();
        let lib_addr = create_result.addr;

        // Compile contract
        let contract = Contract::compile_from_src_string(
            &src,
            "Verifier",
            true,
            &[("BN256G2", lib_addr.as_token())],
        )
        .unwrap();

        // Deploy contract
        let create_result = evm
            .deploy(
                contract.encode_create_contract_bytes(&[]).unwrap(),
                &deployer,
            )
            .unwrap();
        let contract_addr = create_result.addr;

        // convert to the solidity proof format
        let solidity_proof = S::Proof::from(proof.proof);

        // convert to tokens to build a call
        let proof_token = S::to_token(solidity_proof.clone());

        let input_token = Token::FixedArray(
            proof
                .inputs
                .iter()
                .map(|s| {
                    let bytes = hex::decode(s.trim_start_matches("0x")).unwrap();
                    debug_assert_eq!(bytes.len(), 32);
                    Token::Uint(U256::from(&bytes[..]))
                })
                .collect::<Vec<_>>(),
        );

        let inputs = [proof_token, input_token.clone()];

        // Call verify function on contract
        let result = evm
            .call(
                contract
                    .encode_call_contract_bytes("verifyTx", &inputs)
                    .unwrap(),
                &contract_addr,
                &deployer,
            )
            .unwrap();

        assert_eq!(&result.out, &to_be_bytes(&U256::from(1)));

        // modify the proof
        let modified_solidity_proof = S::modify(solidity_proof);

        let modified_proof_token = S::to_token(modified_solidity_proof);

        let inputs = [modified_proof_token, input_token];

        // Call verify function on contract
        let result = evm
            .call(
                contract
                    .encode_call_contract_bytes("verifyTx", &inputs)
                    .unwrap(),
                &contract_addr,
                &deployer,
            )
            .unwrap();

        assert_eq!(result.op_out, Return::InvalidOpcode);
    }

    fn test_compile_and_smtlib2(
        program_name: &str,
        program_path: &Path,
        expected_smtlib2_path: &Path,
    ) {
        println!("test smtlib2 for {}", program_path.display());

        let tmp_dir = TempDir::new(program_name).unwrap();
        let tmp_base = tmp_dir.path();
        let test_case_path = tmp_base.join(program_name);
        let flattened_path = tmp_base.join(program_name).join("out");
        let smtlib2_path = tmp_base.join(program_name).join("out.smt2");

        // create a tmp folder to store artifacts
        fs::create_dir(test_case_path).unwrap();

        let stdlib = std::fs::canonicalize("../zokrates_stdlib/stdlib").unwrap();

        // prepare compile arguments
        let compile = vec![
            "compile",
            "-i",
            program_path.to_str().unwrap(),
            "--stdlib-path",
            stdlib.to_str().unwrap(),
            "-o",
            flattened_path.to_str().unwrap(),
        ];

        // compile
        assert_cli::Assert::main_binary()
            .with_args(&compile)
            .succeeds()
            .unwrap();

        // prepare generate-smtlib2 arguments
        let gen = vec![
            "generate-smtlib2",
            "-i",
            flattened_path.to_str().unwrap(),
            "-o",
            smtlib2_path.to_str().unwrap(),
        ];

        // generate-smtlib2
        assert_cli::Assert::main_binary()
            .with_args(&gen)
            .succeeds()
            .unwrap();

        // load the expected smtlib2
        let mut expected_smtlib2_file = File::open(&expected_smtlib2_path).unwrap();
        let mut expected_smtlib2 = String::new();
        expected_smtlib2_file
            .read_to_string(&mut expected_smtlib2)
            .unwrap();

        // load the actual smtlib2
        let mut smtlib2_file = File::open(&smtlib2_path).unwrap();
        let mut smtlib2 = String::new();
        smtlib2_file.read_to_string(&mut smtlib2).unwrap();

        assert_eq!(expected_smtlib2, smtlib2);
    }

    #[test]
    #[ignore]
    fn test_compile_and_smtlib2_dir() {
        let dir = Path::new("./tests/code");
        assert!(dir.is_dir());
        for entry in fs::read_dir(dir).unwrap() {
            let entry = entry.unwrap();
            let path = entry.path();
            if path.extension().unwrap() == "smt2" {
                let program_name = Path::new(path.file_stem().unwrap());
                let prog = dir.join(program_name).with_extension("zok");
                test_compile_and_smtlib2(program_name.to_str().unwrap(), &prog, &path);
            }
        }
    }

    #[test]
    #[ignore]
    fn test_rng_tutorial() {
        let tmp_dir = TempDir::new(".tmp").unwrap();
        let tmp_base = tmp_dir.path();

        let mut options = CopyOptions::new();
        options.copy_inside = true;
        copy_items(&["examples/book/rng_tutorial"], tmp_base, &options).unwrap();

        let stdlib = std::fs::canonicalize("../zokrates_stdlib/stdlib").unwrap();
        let binary_path = env!("CARGO_BIN_EXE_zokrates");

        assert_cli::Assert::command(&["bash", "test.sh", binary_path, stdlib.to_str().unwrap()])
            .current_dir(tmp_base.join("rng_tutorial"))
            .succeeds()
            .unwrap();
    }

    #[test]
    #[ignore]
    fn test_sha256_tutorial() {
        let tmp_dir = TempDir::new(".tmp").unwrap();
        let tmp_base = tmp_dir.path();

        let mut options = CopyOptions::new();
        options.copy_inside = true;
        copy_items(&["examples/book/sha256_tutorial"], tmp_base, &options).unwrap();

        let stdlib = std::fs::canonicalize("../zokrates_stdlib/stdlib").unwrap();
        let binary_path = env!("CARGO_BIN_EXE_zokrates");

        assert_cli::Assert::command(&["bash", "test.sh", binary_path, stdlib.to_str().unwrap()])
            .current_dir(tmp_base.join("sha256_tutorial"))
            .succeeds()
            .unwrap();
    }

    #[test]
    #[ignore]
    fn test_mpc_tutorial() {
        let tmp_dir = TempDir::new(".tmp").unwrap();
        let tmp_base = tmp_dir.path();

        let mut options = CopyOptions::new();
        options.copy_inside = true;
        copy_items(&["examples/book/mpc_tutorial"], tmp_base, &options).unwrap();

        let stdlib = std::fs::canonicalize("../zokrates_stdlib/stdlib").unwrap();
        let binary_path = env!("CARGO_BIN_EXE_zokrates");

        assert_cli::Assert::command(&["bash", "test.sh", binary_path, stdlib.to_str().unwrap()])
            .current_dir(tmp_base.join("mpc_tutorial"))
            .succeeds()
            .unwrap();
    }
}
