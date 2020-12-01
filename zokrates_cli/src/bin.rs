//
// @file bin.rs
// @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
// @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
// @date 2017

mod constants;
mod helpers;

use constants::*;
use helpers::*;

use clap::{App, AppSettings, Arg, ArgMatches, SubCommand};
use serde_json::{from_reader, to_writer_pretty, Value};
use std::convert::TryFrom;
use std::env;
use std::fs::File;
use std::io::{stdin, BufReader, BufWriter, Read, Write};
use std::path::{Path, PathBuf};
use std::string::String;
use zokrates_abi::Encode;
use zokrates_core::compile::{check, compile, CompilationArtifacts, CompileError};
use zokrates_core::ir::{self, ProgEnum};
use zokrates_core::proof_system::{
    ark::Ark, bellman::Bellman, gm17::GM17, groth16::G16, SolidityCompatibleField,
};
use zokrates_core::proof_system::{Backend, Scheme, SolidityAbi, SolidityCompatibleScheme};
use zokrates_core::typed_absy::abi::Abi;
use zokrates_core::typed_absy::{types::Signature, Type};
use zokrates_field::{Bls12_377Field, Bls12_381Field, Bn128Field, Bw6_761Field, Field};
use zokrates_fs_resolver::FileSystemResolver;
#[cfg(feature = "libsnark")]
use {
    zokrates_core::proof_system::libsnark::Libsnark, zokrates_core::proof_system::pghr13::PGHR13,
};

fn main() {
    cli().unwrap_or_else(|e| {
        println!("{}", e);
        std::process::exit(1);
    })
}

fn cli_generate_proof<T: Field, S: Scheme<T>, B: Backend<T, S>>(
    program: ir::Prog<T>,
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    println!("Generating proof...");

    // deserialize witness
    let witness_path = Path::new(sub_matches.value_of("witness").unwrap());
    let witness_file = match File::open(&witness_path) {
        Ok(file) => file,
        Err(why) => panic!("Couldn't open {}: {}", witness_path.display(), why),
    };

    let witness = ir::Witness::read(witness_file)
        .map_err(|why| format!("Could not load witness: {:?}", why))?;

    let pk_path = Path::new(sub_matches.value_of("proving-key-path").unwrap());
    let proof_path = Path::new(sub_matches.value_of("proof-path").unwrap());

    let pk_file = File::open(&pk_path)
        .map_err(|why| format!("Couldn't open {}: {}", pk_path.display(), why))?;

    let mut pk: Vec<u8> = Vec::new();
    let mut pk_reader = BufReader::new(pk_file);
    pk_reader
        .read_to_end(&mut pk)
        .map_err(|why| format!("Couldn't read {}: {}", pk_path.display(), why))?;

    let proof = B::generate_proof(program, witness, pk);
    let mut proof_file = File::create(proof_path).unwrap();

    let proof = serde_json::to_string_pretty(&proof).unwrap();
    proof_file
        .write(proof.as_bytes())
        .map_err(|why| format!("Couldn't write to {}: {}", proof_path.display(), why))?;

    println!("Proof:\n{}", format!("{}", proof));

    Ok(())
}

fn cli_export_verifier<T: SolidityCompatibleField, S: SolidityCompatibleScheme<T>>(
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    println!("Exporting verifier...");

    // read vk file
    let input_path = Path::new(sub_matches.value_of("input").unwrap());
    let input_file = File::open(&input_path)
        .map_err(|why| format!("Couldn't open {}: {}", input_path.display(), why))?;
    let reader = BufReader::new(input_file);

    let vk = serde_json::from_reader(reader)
        .map_err(|why| format!("Couldn't deserialize verifying key: {}", why))?;

    let abi = SolidityAbi::from(sub_matches.value_of("solidity-abi").unwrap())?;

    let verifier = S::export_solidity_verifier(vk, abi);

    //write output file
    let output_path = Path::new(sub_matches.value_of("output").unwrap());
    let output_file = File::create(&output_path)
        .map_err(|why| format!("Couldn't create {}: {}", output_path.display(), why))?;

    let mut writer = BufWriter::new(output_file);

    writer
        .write_all(&verifier.as_bytes())
        .map_err(|_| "Failed writing output to file.".to_string())?;

    println!("Finished exporting verifier.");
    Ok(())
}

fn cli_setup<T: Field, S: Scheme<T>, B: Backend<T, S>>(
    program: ir::Prog<T>,
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    println!("Performing setup...");

    // print deserialized flattened program
    if !sub_matches.is_present("light") {
        println!("{}", program);
    }

    // get paths for proving and verification keys
    let pk_path = Path::new(sub_matches.value_of("proving-key-path").unwrap());
    let vk_path = Path::new(sub_matches.value_of("verification-key-path").unwrap());

    // run setup phase
    let keypair = B::setup(program);

    // write verification key
    let mut vk_file = File::create(vk_path)
        .map_err(|why| format!("couldn't create {}: {}", vk_path.display(), why))?;
    vk_file
        .write(
            serde_json::to_string_pretty(&keypair.vk)
                .unwrap()
                .as_bytes(),
        )
        .map_err(|why| format!("couldn't write to {}: {}", vk_path.display(), why))?;

    // write proving key
    let mut pk_file = File::create(pk_path)
        .map_err(|why| format!("couldn't create {}: {}", pk_path.display(), why))?;
    pk_file
        .write(keypair.pk.as_ref())
        .map_err(|why| format!("couldn't write to {}: {}", pk_path.display(), why))?;

    println!("Setup completed.");

    Ok(())
}

fn cli_compute<T: Field>(ir_prog: ir::Prog<T>, sub_matches: &ArgMatches) -> Result<(), String> {
    println!("Computing witness...");

    // print deserialized flattened program
    if !sub_matches.is_present("light") {
        println!("{}", ir_prog);
    }

    let is_stdin = sub_matches.is_present("stdin");
    let is_abi = sub_matches.is_present("abi");

    if !is_stdin && is_abi {
        return Err("ABI input as inline argument is not supported. Please use `--stdin`.".into());
    }

    let signature = match is_abi {
        true => {
            let path = Path::new(sub_matches.value_of("abi_spec").unwrap());
            let file = File::open(&path)
                .map_err(|why| format!("couldn't open {}: {}", path.display(), why))?;
            let mut reader = BufReader::new(file);

            let abi: Abi = from_reader(&mut reader).map_err(|why| why.to_string())?;

            abi.signature()
        }
        false => Signature::new()
            .inputs(vec![Type::FieldElement; ir_prog.main.arguments.len()])
            .outputs(vec![Type::FieldElement; ir_prog.main.returns.len()]),
    };

    use zokrates_abi::Inputs;

    // get arguments
    let arguments = match is_stdin {
        // take inline arguments
        false => {
            let arguments = sub_matches.values_of("arguments");
            arguments
                .map(|a| {
                    a.map(|x| T::try_from_dec_str(x).map_err(|_| x.to_string()))
                        .collect::<Result<Vec<_>, _>>()
                })
                .unwrap_or(Ok(vec![]))
                .map(|v| Inputs::Raw(v))
        }
        // take stdin arguments
        true => {
            let mut stdin = stdin();
            let mut input = String::new();

            match is_abi {
                true => match stdin.read_to_string(&mut input) {
                    Ok(_) => {
                        use zokrates_abi::parse_strict;

                        parse_strict(&input, signature.inputs)
                            .map(|parsed| Inputs::Abi(parsed))
                            .map_err(|why| why.to_string())
                    }
                    Err(_) => Err(String::from("???")),
                },
                false => match ir_prog.arguments_count() {
                    0 => Ok(Inputs::Raw(vec![])),
                    _ => match stdin.read_to_string(&mut input) {
                        Ok(_) => {
                            input.retain(|x| x != '\n');
                            input
                                .split(" ")
                                .map(|x| T::try_from_dec_str(x).map_err(|_| x.to_string()))
                                .collect::<Result<Vec<_>, _>>()
                                .map(|v| Inputs::Raw(v))
                        }
                        Err(_) => Err(String::from("???")),
                    },
                },
            }
        }
    }
    .map_err(|e| format!("Could not parse argument: {}", e))?;

    let interpreter = ir::Interpreter::default();

    let witness = interpreter
        .execute(&ir_prog, &arguments.encode())
        .map_err(|e| format!("Execution failed: {}", e))?;

    use zokrates_abi::Decode;

    let results_json_value: serde_json::Value =
        zokrates_abi::CheckedValues::decode(witness.return_values(), signature.outputs).into();

    println!("\nWitness: \n\n{}", results_json_value);

    // write witness to file
    let output_path = Path::new(sub_matches.value_of("output").unwrap());
    let output_file = File::create(&output_path)
        .map_err(|why| format!("couldn't create {}: {}", output_path.display(), why))?;

    let writer = BufWriter::new(output_file);

    witness
        .write(writer)
        .map_err(|why| format!("could not save witness: {:?}", why))?;

    Ok(())
}

fn cli_compile<T: Field>(sub_matches: &ArgMatches) -> Result<(), String> {
    println!("Compiling {}\n", sub_matches.value_of("input").unwrap());
    let path = PathBuf::from(sub_matches.value_of("input").unwrap());

    let light = sub_matches.occurrences_of("light") > 0;

    let bin_output_path = Path::new(sub_matches.value_of("output").unwrap());

    let abi_spec_path = Path::new(sub_matches.value_of("abi_spec").unwrap());

    let hr_output_path = bin_output_path.to_path_buf().with_extension("ztf");

    let file = File::open(path.clone())
        .map_err(|why| format!("Couldn't open input file {}: {}", path.display(), why))?;

    let mut reader = BufReader::new(file);
    let mut source = String::new();
    reader.read_to_string(&mut source).unwrap();

    let fmt_error = |e: &CompileError| {
        let file = e.file().canonicalize().unwrap();
        format!(
            "{}:{}",
            file.strip_prefix(std::env::current_dir().unwrap())
                .unwrap_or(file.as_path())
                .display(),
            e.value()
        )
    };

    let resolver =
        FileSystemResolver::with_stdlib_root(sub_matches.value_of("stdlib-path").unwrap());
    let artifacts: CompilationArtifacts<T> =
        compile(source, path, Some(&resolver)).map_err(|e| {
            format!(
                "Compilation failed:\n\n{}",
                e.0.iter()
                    .map(|e| fmt_error(e))
                    .collect::<Vec<_>>()
                    .join("\n\n")
            )
        })?;

    let program_flattened = artifacts.prog();

    // number of constraints the flattened program will translate to.
    let num_constraints = program_flattened.constraint_count();

    // serialize flattened program and write to binary file
    let bin_output_file = File::create(&bin_output_path)
        .map_err(|why| format!("Couldn't create {}: {}", bin_output_path.display(), why))?;

    let mut writer = BufWriter::new(bin_output_file);

    program_flattened.serialize(&mut writer);

    // serialize ABI spec and write to JSON file
    let abi_spec_file = File::create(&abi_spec_path)
        .map_err(|why| format!("Couldn't create {}: {}", abi_spec_path.display(), why))?;

    let abi = artifacts.abi();

    let mut writer = BufWriter::new(abi_spec_file);

    to_writer_pretty(&mut writer, &abi).map_err(|_| "Unable to write data to file.".to_string())?;

    if !light {
        // write human-readable output file
        let hr_output_file = File::create(&hr_output_path)
            .map_err(|why| format!("Couldn't create {}: {}", hr_output_path.display(), why))?;

        let mut hrofb = BufWriter::new(hr_output_file);
        write!(&mut hrofb, "{}\n", program_flattened)
            .map_err(|_| "Unable to write data to file.".to_string())?;
        hrofb
            .flush()
            .map_err(|_| "Unable to flush buffer.".to_string())?;
    }

    if !light {
        // debugging output
        println!("Compiled program:\n{}", program_flattened);
    }

    println!("Compiled code written to '{}'", bin_output_path.display());

    if !light {
        println!("Human readable code to '{}'", hr_output_path.display());
    }

    println!("Number of constraints: {}", num_constraints);
    Ok(())
}

fn cli_check<T: Field>(sub_matches: &ArgMatches) -> Result<(), String> {
    println!("Checking {}\n", sub_matches.value_of("input").unwrap());
    let path = PathBuf::from(sub_matches.value_of("input").unwrap());

    let file = File::open(path.clone())
        .map_err(|why| format!("Couldn't open input file {}: {}", path.display(), why))?;

    let mut reader = BufReader::new(file);
    let mut source = String::new();
    reader.read_to_string(&mut source).unwrap();

    let fmt_error = |e: &CompileError| {
        let file = e.file().canonicalize().unwrap();
        format!(
            "{}:{}",
            file.strip_prefix(std::env::current_dir().unwrap())
                .unwrap_or(file.as_path())
                .display(),
            e.value()
        )
    };

    let resolver =
        FileSystemResolver::with_stdlib_root(sub_matches.value_of("stdlib-path").unwrap());
    let _ = check::<T, _>(source, path, Some(&resolver)).map_err(|e| {
        format!(
            "Check failed:\n\n{}",
            e.0.iter()
                .map(|e| fmt_error(e))
                .collect::<Vec<_>>()
                .join("\n\n")
        )
    })?;

    println!("Program checked, no errors found.");

    Ok(())
}

fn cli_verify<T: Field, S: Scheme<T>, B: Backend<T, S>>(
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    let vk_path = Path::new(sub_matches.value_of("verification-key-path").unwrap());
    let vk_file = File::open(&vk_path)
        .map_err(|why| format!("Couldn't open {}: {}", vk_path.display(), why))?;

    let vk_reader = BufReader::new(vk_file);
    let vk = serde_json::from_reader(vk_reader)
        .map_err(|why| format!("Couldn't deserialize verification key: {}", why))?;

    let proof_path = Path::new(sub_matches.value_of("proof-path").unwrap());
    let proof_file = File::open(&proof_path)
        .map_err(|why| format!("Couldn't open {}: {}", proof_path.display(), why))?;

    let proof_reader = BufReader::new(proof_file);
    let proof = serde_json::from_reader(proof_reader)
        .map_err(|why| format!("Couldn't deserialize proof: {}", why))?;

    println!("Performing verification...");
    println!(
        "The verification result is: {}",
        match B::verify(vk, proof) {
            true => "PASS",
            false => "FAIL",
        }
    );

    Ok(())
}

fn cli() -> Result<(), String> {
    const FLATTENED_CODE_DEFAULT_PATH: &str = "out";
    const ABI_SPEC_DEFAULT_PATH: &str = "abi.json";
    const VERIFICATION_KEY_DEFAULT_PATH: &str = "verification.key";
    const PROVING_KEY_DEFAULT_PATH: &str = "proving.key";
    const VERIFICATION_CONTRACT_DEFAULT_PATH: &str = "verifier.sol";
    const WITNESS_DEFAULT_PATH: &str = "witness";
    const JSON_PROOF_PATH: &str = "proof.json";
    let default_curve = env::var("ZOKRATES_CURVE").unwrap_or(constants::BN128.into());
    let default_backend = env::var("ZOKRATES_BACKEND").unwrap_or(constants::BELLMAN.into());
    let default_scheme = env::var("ZOKRATES_PROVING_SCHEME").unwrap_or(constants::G16.into());
    let default_solidity_abi = "v1";
    let default_stdlib_path = dirs::home_dir()
        .map(|p| p.join(".zokrates/stdlib"))
        .unwrap();

    // cli specification using clap library
    let matches = App::new("ZoKrates")
    .setting(AppSettings::SubcommandRequiredElseHelp)
    .version(env!("CARGO_PKG_VERSION"))
    .author("Jacob Eberhardt, Thibaut Schaeffer, Stefan Deml, Darko Macesic")
    .about("Supports generation of zkSNARKs from high level language code including Smart Contracts for proof verification on the Ethereum Blockchain.\n'I know that I show nothing!'")
    .subcommand(SubCommand::with_name("compile")
        .about("Compiles into flattened conditions. Produces two files: human-readable '.ztf' file for debugging and binary file")
        .arg(Arg::with_name("input")
            .short("i")
            .long("input")
            .help("Path of the source code")
            .value_name("FILE")
            .takes_value(true)
            .required(true)
        ).arg(Arg::with_name("stdlib-path")
            .long("stdlib-path")
            .help("Path to the standard library")
            .value_name("PATH")
            .takes_value(true)
            .required(false)
            .env("ZOKRATES_STDLIB")
            .default_value(default_stdlib_path.to_str().unwrap_or(""))
        ).arg(Arg::with_name("abi_spec")
            .short("s")
            .long("abi_spec")
            .help("Path of the ABI specification")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(ABI_SPEC_DEFAULT_PATH)
        ).arg(Arg::with_name("output")
            .short("o")
            .long("output")
            .help("Path of the output binary")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(FLATTENED_CODE_DEFAULT_PATH)
        ).arg(Arg::with_name("curve")
            .short("c")
            .long("curve")
            .help("Curve to be used in the compilation")
            .takes_value(true)
            .required(false)
            .possible_values(CURVES)
            .default_value(&default_curve)
        ).arg(Arg::with_name("light")
            .long("light")
            .help("Skip logs and human readable output")
            .required(false)
        )
     )
    .subcommand(SubCommand::with_name("check")
        .about("Checks a program for errors")
        .arg(Arg::with_name("input")
            .short("i")
            .long("input")
            .help("Path of the source code")
            .value_name("FILE")
            .takes_value(true)
            .required(true)
        ).arg(Arg::with_name("stdlib-path")
            .long("stdlib-path")
            .help("Path to the standard library")
            .value_name("PATH")
            .takes_value(true)
            .required(false)
            .env("ZOKRATES_STDLIB")
            .default_value(default_stdlib_path.to_str().unwrap_or(""))
        ).arg(Arg::with_name("curve")
            .short("c")
            .long("curve")
            .help("Curve to be used in the compilation")
            .takes_value(true)
            .required(false)
            .possible_values(CURVES)
            .default_value(&default_curve)
        )
     )
    .subcommand(SubCommand::with_name("setup")
        .about("Performs a trusted setup for a given constraint system")
        .arg(Arg::with_name("input")
            .short("i")
            .long("input")
            .help("Path of the binary")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(FLATTENED_CODE_DEFAULT_PATH)
        ).arg(Arg::with_name("proving-key-path")
            .short("p")
            .long("proving-key-path")
            .help("Path of the generated proving key file")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(PROVING_KEY_DEFAULT_PATH)
        ).arg(Arg::with_name("verification-key-path")
            .short("v")
            .long("verification-key-path")
            .help("Path of the generated verification key file")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(VERIFICATION_KEY_DEFAULT_PATH)
        ).arg(Arg::with_name("backend")
            .short("b")
            .long("backend")
            .help("Backend to use")
            .takes_value(true)
            .required(false)
            .possible_values(BACKENDS)
            .default_value(&default_backend)
        ).arg(Arg::with_name("proving-scheme")
            .short("s")
            .long("proving-scheme")
            .help("Proving scheme to use in the setup")
            .takes_value(true)
            .required(false)
            .possible_values(SCHEMES)
            .default_value(&default_scheme)
        ).arg(Arg::with_name("light")
            .long("light")
            .help("Skip logging the human-readable program and writing it to a file")
            .required(false)
        )
    )
    .subcommand(SubCommand::with_name("export-verifier")
        .about("Exports a verifier as Solidity smart contract")
        .arg(Arg::with_name("input")
            .short("i")
            .long("input")
            .help("Path of the verifier")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(VERIFICATION_KEY_DEFAULT_PATH)
        ).arg(Arg::with_name("output")
            .short("o")
            .long("output")
            .help("Path of the output file")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(VERIFICATION_CONTRACT_DEFAULT_PATH)
        ).arg(Arg::with_name("curve")
            .short("c")
            .long("curve")
            .help("Curve to be used to export the verifier")
            .takes_value(true)
            .required(false)
            .possible_values(CURVES)
            .default_value(&default_curve)
        ).arg(Arg::with_name("proving-scheme")
            .short("s")
            .long("proving-scheme")
            .help("Proving scheme to use to export the verifier")
            .takes_value(true)
            .required(false)
            .possible_values(SCHEMES)
            .default_value(&default_scheme)
        ).arg(Arg::with_name("solidity-abi")
            .short("a")
            .long("solidity-abi")
            .help("Flag for setting the version of the ABI Encoder used in the contract")
            .takes_value(true)
            .possible_values(&["v1", "v2"])
            .default_value(&default_solidity_abi)
            .required(false)
        )
    )
    .subcommand(SubCommand::with_name("compute-witness")
        .about("Calculates a witness for a given constraint system")
        .arg(Arg::with_name("input")
            .short("i")
            .long("input")
            .help("Path of the binary")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(FLATTENED_CODE_DEFAULT_PATH)
        ).arg(Arg::with_name("abi_spec")
            .short("s")
            .long("abi_spec")
            .help("Path of the ABI specification")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(ABI_SPEC_DEFAULT_PATH)
        ).arg(Arg::with_name("output")
            .short("o")
            .long("output")
            .help("Path of the output file")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(WITNESS_DEFAULT_PATH)
        ).arg(Arg::with_name("arguments")
            .short("a")
            .long("arguments")
            .help("Arguments for the program's main function, when not using ABI encoding. Expects a space-separated list of field elements like `-a 1 2 3`")
            .takes_value(true)
            .multiple(true) // allows multiple values
            .required(false)
            .conflicts_with("abi")
            .conflicts_with("stdin")
        ).arg(Arg::with_name("abi")
            .long("abi")
            .help("Use ABI encoding. Arguments are expected as a JSON object as specified at zokrates.github.io/toolbox/abi.html#abi-input-format")
            .conflicts_with("arguments")
            .required(false)
        ).arg(Arg::with_name("stdin")
            .long("stdin")
            .help("Read arguments from stdin")
            .conflicts_with("arguments")
            .required(false)
        ).arg(Arg::with_name("light")
            .long("light")
            .help("Skip logging the human-readable program")
            .required(false)
        )
    )
    .subcommand(SubCommand::with_name("generate-proof")
        .about("Calculates a proof for a given constraint system and witness")
        .arg(Arg::with_name("witness")
            .short("w")
            .long("witness")
            .help("Path of the witness file")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(WITNESS_DEFAULT_PATH)
        ).arg(Arg::with_name("proving-key-path")
            .short("p")
            .long("proving-key-path")
            .help("Path of the proving key file")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(PROVING_KEY_DEFAULT_PATH)
        ).arg(Arg::with_name("proof-path")
            .short("j")
            .long("proof-path")
            .help("Path of the JSON proof file")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(JSON_PROOF_PATH)
        ).arg(Arg::with_name("input")
            .short("i")
            .long("input")
            .help("Path of the binary")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(FLATTENED_CODE_DEFAULT_PATH)
        ).arg(Arg::with_name("backend")
            .short("b")
            .long("backend")
            .help("Backend to use")
            .takes_value(true)
            .required(false)
            .possible_values(BACKENDS)
            .default_value(&default_backend)
        ).arg(Arg::with_name("proving-scheme")
            .short("s")
            .long("proving-scheme")
            .help("Proving scheme to use to generate the proof")
            .takes_value(true)
            .required(false)
            .possible_values(SCHEMES)
            .default_value(&default_scheme)
        )
    )
     .subcommand(SubCommand::with_name("print-proof")
        .about("Prints proof in the chosen format")
        .arg(Arg::with_name("proof-path")
            .short("j")
            .long("proof-path")
            .help("Path of the JSON proof file")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(JSON_PROOF_PATH)
        ).arg(Arg::with_name("format")
            .short("f")
            .long("format")
            .value_name("FORMAT")
            .help("Format in which the proof should be printed")
            .takes_value(true)
            .possible_values(&["remix", "json"])
            .required(true)
        )
    )
    .subcommand(SubCommand::with_name("verify")
        .about("Verifies a given proof with the given verification key")
        .arg(Arg::with_name("proof-path")
            .short("j")
            .long("proof-path")
            .help("Path of the JSON proof file")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(JSON_PROOF_PATH)
        ).arg(Arg::with_name("verification-key-path")
            .short("v")
            .long("verification-key-path")
            .help("Path of the generated verification key file")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(VERIFICATION_KEY_DEFAULT_PATH)
        ).arg(Arg::with_name("backend")
            .short("b")
            .long("backend")
            .help("Backend to use")
            .takes_value(true)
            .required(false)
            .possible_values(BACKENDS)
            .default_value(&default_backend)
        ).arg(Arg::with_name("proving-scheme")
            .short("s")
            .long("proving-scheme")
            .help("Proving scheme to use in the setup. Available options are G16 (default), PGHR13 and GM17")
            .takes_value(true)
            .required(false)
            .default_value(&default_scheme)
        ).arg(Arg::with_name("curve")
            .short("c")
            .long("curve")
            .help("Curve to be used in the verification")
            .takes_value(true)
            .required(false)
            .possible_values(CURVES)
            .default_value(&default_curve)
        )
    )
    .get_matches();

    match matches.subcommand() {
        ("compile", Some(sub_matches)) => {
            let curve = CurveParameter::try_from(sub_matches.value_of("curve").unwrap())?;
            match curve {
                CurveParameter::Bn128 => cli_compile::<Bn128Field>(sub_matches)?,
                CurveParameter::Bls12_377 => cli_compile::<Bls12_377Field>(sub_matches)?,
                CurveParameter::Bls12_381 => cli_compile::<Bls12_381Field>(sub_matches)?,
                CurveParameter::Bw6_761 => cli_compile::<Bw6_761Field>(sub_matches)?,
            }
        }
        ("check", Some(sub_matches)) => {
            let curve = CurveParameter::try_from(sub_matches.value_of("curve").unwrap())?;
            match curve {
                CurveParameter::Bn128 => cli_check::<Bn128Field>(sub_matches)?,
                CurveParameter::Bls12_377 => cli_check::<Bls12_377Field>(sub_matches)?,
                CurveParameter::Bls12_381 => cli_check::<Bls12_381Field>(sub_matches)?,
                CurveParameter::Bw6_761 => cli_check::<Bw6_761Field>(sub_matches)?,
            }
        }
        ("compute-witness", Some(sub_matches)) => {
            // read compiled program
            let path = Path::new(sub_matches.value_of("input").unwrap());
            let file = File::open(&path)
                .map_err(|why| format!("Couldn't open {}: {}", path.display(), why))?;

            let mut reader = BufReader::new(file);

            match ProgEnum::deserialize(&mut reader)? {
                ProgEnum::Bn128Program(p) => cli_compute(p, sub_matches)?,
                ProgEnum::Bls12_377Program(p) => cli_compute(p, sub_matches)?,
                ProgEnum::Bls12_381Program(p) => cli_compute(p, sub_matches)?,
                ProgEnum::Bw6_761Program(p) => cli_compute(p, sub_matches)?,
            }
        }
        ("setup", Some(sub_matches)) => {
            // read compiled program
            let path = Path::new(sub_matches.value_of("input").unwrap());
            let file = File::open(&path)
                .map_err(|why| format!("Couldn't open {}: {}", path.display(), why))?;

            let mut reader = BufReader::new(file);
            let prog = ProgEnum::deserialize(&mut reader)?;

            let parameters = Parameters::try_from((
                sub_matches.value_of("backend").unwrap(),
                match prog {
                    ProgEnum::Bn128Program(_) => constants::BN128,
                    ProgEnum::Bls12_377Program(_) => constants::BLS12_377,
                    ProgEnum::Bls12_381Program(_) => constants::BLS12_381,
                    ProgEnum::Bw6_761Program(_) => constants::BW6_761,
                },
                sub_matches.value_of("proving-scheme").unwrap(),
            ))?;

            match parameters {
                Parameters(BackendParameter::Bellman, _, SchemeParameter::G16) => match prog {
                    ProgEnum::Bn128Program(p) => cli_setup::<_, G16, Bellman>(p, sub_matches),
                    ProgEnum::Bls12_381Program(p) => cli_setup::<_, G16, Bellman>(p, sub_matches),
                    _ => unreachable!(),
                },
                Parameters(BackendParameter::Ark, _, SchemeParameter::GM17) => match prog {
                    ProgEnum::Bls12_377Program(p) => cli_setup::<_, GM17, Ark>(p, sub_matches),
                    ProgEnum::Bw6_761Program(p) => cli_setup::<_, GM17, Ark>(p, sub_matches),
                    ProgEnum::Bn128Program(p) => cli_setup::<_, GM17, Ark>(p, sub_matches),
                    _ => unreachable!(),
                },
                #[cfg(feature = "libsnark")]
                Parameters(
                    BackendParameter::Libsnark,
                    CurveParameter::Bn128,
                    SchemeParameter::GM17,
                ) => match prog {
                    ProgEnum::Bn128Program(p) => cli_setup::<_, GM17, Libsnark>(p, sub_matches),
                    _ => unreachable!(),
                },
                #[cfg(feature = "libsnark")]
                Parameters(
                    BackendParameter::Libsnark,
                    CurveParameter::Bn128,
                    SchemeParameter::PGHR13,
                ) => match prog {
                    ProgEnum::Bn128Program(p) => cli_setup::<_, PGHR13, Libsnark>(p, sub_matches),
                    _ => unreachable!(),
                },
                _ => unreachable!(),
            }?
        }
        ("export-verifier", Some(sub_matches)) => {
            let curve = sub_matches.value_of("curve").unwrap();
            let scheme = sub_matches.value_of("proving-scheme").unwrap();
            let curve_parameter = CurveParameter::try_from(curve)?;
            let scheme_parameter = SchemeParameter::try_from(scheme)?;

            match (curve_parameter, scheme_parameter) {
                (CurveParameter::Bn128, SchemeParameter::G16) => {
                    cli_export_verifier::<Bn128Field, G16>(sub_matches)
                }
                (CurveParameter::Bn128, SchemeParameter::GM17) => {
                    cli_export_verifier::<Bn128Field, GM17>(sub_matches)
                }
                #[cfg(feature = "libsnark")]
                (CurveParameter::Bn128, SchemeParameter::PGHR13) => {
                    cli_export_verifier::<Bn128Field, PGHR13>(sub_matches)
                }
                _ => Err(format!("Could not export verifier with given parameters (curve: {}, scheme: {}): not supported", curve, scheme))
            }?
        }
        ("generate-proof", Some(sub_matches)) => {
            let program_path = Path::new(sub_matches.value_of("input").unwrap());
            let program_file = File::open(&program_path)
                .map_err(|why| format!("Couldn't open {}: {}", program_path.display(), why))?;

            let mut reader = BufReader::new(program_file);
            let prog = ProgEnum::deserialize(&mut reader)?;

            let parameters = Parameters::try_from((
                sub_matches.value_of("backend").unwrap(),
                match prog {
                    ProgEnum::Bn128Program(_) => constants::BN128,
                    ProgEnum::Bls12_381Program(_) => constants::BLS12_381,
                    ProgEnum::Bls12_377Program(_) => constants::BLS12_377,
                    ProgEnum::Bw6_761Program(_) => constants::BW6_761,
                },
                sub_matches.value_of("proving-scheme").unwrap(),
            ))?;

            match parameters {
                Parameters(BackendParameter::Bellman, _, SchemeParameter::G16) => match prog {
                    ProgEnum::Bn128Program(p) => {
                        cli_generate_proof::<_, G16, Bellman>(p, sub_matches)
                    }
                    ProgEnum::Bls12_381Program(p) => {
                        cli_generate_proof::<_, G16, Bellman>(p, sub_matches)
                    }
                    _ => unreachable!(),
                },
                Parameters(BackendParameter::Ark, _, SchemeParameter::GM17) => match prog {
                    ProgEnum::Bls12_377Program(p) => {
                        cli_generate_proof::<_, GM17, Ark>(p, sub_matches)
                    }
                    ProgEnum::Bw6_761Program(p) => {
                        cli_generate_proof::<_, GM17, Ark>(p, sub_matches)
                    }
                    ProgEnum::Bn128Program(p) => cli_generate_proof::<_, GM17, Ark>(p, sub_matches),
                    _ => unreachable!(),
                },
                #[cfg(feature = "libsnark")]
                Parameters(
                    BackendParameter::Libsnark,
                    CurveParameter::Bn128,
                    SchemeParameter::GM17,
                ) => match prog {
                    ProgEnum::Bn128Program(p) => {
                        cli_generate_proof::<_, GM17, Libsnark>(p, sub_matches)
                    }
                    _ => unreachable!(),
                },
                #[cfg(feature = "libsnark")]
                Parameters(
                    BackendParameter::Libsnark,
                    CurveParameter::Bn128,
                    SchemeParameter::PGHR13,
                ) => match prog {
                    ProgEnum::Bn128Program(p) => {
                        cli_generate_proof::<_, PGHR13, Libsnark>(p, sub_matches)
                    }
                    _ => unreachable!(),
                },
                _ => unreachable!(),
            }?
        }
        ("print-proof", Some(sub_matches)) => {
            let format = sub_matches.value_of("format").unwrap();
            let path = Path::new(sub_matches.value_of("proof-path").unwrap());

            let file = File::open(&path)
                .map_err(|why| format!("Couldn't open {}: {}", path.display(), why))?;

            let proof_object: Value =
                serde_json::from_reader(file).map_err(|why| format!("{:?}", why))?;

            match format {
                "json" => {
                    println!("~~~~~~~~ Copy the output below for valid ABIv2 format ~~~~~~~~");
                    println!();
                    print!("{}", proof_object["proof"]);
                    print!(",");
                    println!("{}", proof_object["inputs"]);
                    println!();
                    println!("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~");
                }
                "remix" => {
                    println!("~~~~~~~~ Copy the output below for valid ABIv1 format ~~~~~~~~");
                    println!();

                    for (_, value) in proof_object["proof"].as_object().unwrap().iter() {
                        print!("{}", value);
                        print!(",");
                    }

                    println!("{}", proof_object["inputs"]);
                    println!();
                    println!("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~");
                }
                _ => unreachable!(),
            }
        }
        ("verify", Some(sub_matches)) => {
            let parameters = Parameters::try_from((
                sub_matches.value_of("backend").unwrap(),
                sub_matches.value_of("curve").unwrap(),
                sub_matches.value_of("proving-scheme").unwrap(),
            ))?;

            match parameters {
                Parameters(
                    BackendParameter::Bellman,
                    CurveParameter::Bn128,
                    SchemeParameter::G16,
                ) => cli_verify::<Bn128Field, G16, Bellman>(sub_matches),
                Parameters(
                    BackendParameter::Bellman,
                    CurveParameter::Bls12_381,
                    SchemeParameter::G16,
                ) => cli_verify::<Bls12_381Field, G16, Bellman>(sub_matches),
                Parameters(
                    BackendParameter::Ark,
                    CurveParameter::Bls12_377,
                    SchemeParameter::GM17,
                ) => cli_verify::<Bls12_377Field, GM17, Ark>(sub_matches),
                Parameters(
                    BackendParameter::Ark,
                    CurveParameter::Bw6_761,
                    SchemeParameter::GM17,
                ) => cli_verify::<Bw6_761Field, GM17, Ark>(sub_matches),
                Parameters(BackendParameter::Ark, CurveParameter::Bn128, SchemeParameter::GM17) => {
                    cli_verify::<Bn128Field, GM17, Ark>(sub_matches)
                }
                #[cfg(feature = "libsnark")]
                Parameters(
                    BackendParameter::Libsnark,
                    CurveParameter::Bn128,
                    SchemeParameter::GM17,
                ) => cli_verify::<Bn128Field, GM17, Libsnark>(sub_matches),
                #[cfg(feature = "libsnark")]
                Parameters(
                    BackendParameter::Libsnark,
                    CurveParameter::Bn128,
                    SchemeParameter::PGHR13,
                ) => cli_verify::<Bn128Field, PGHR13, Libsnark>(sub_matches),
                _ => unreachable!(),
            }?
        }
        _ => unreachable!(),
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    extern crate glob;
    use self::glob::glob;
    use super::*;

    #[test]
    fn compile_examples() {
        for p in glob("./examples/**/*").expect("Failed to read glob pattern") {
            let path = match p {
                Ok(x) => x,
                Err(why) => panic!("Error: {:?}", why),
            };

            if !path.is_file() {
                continue;
            }

            assert!(path.extension().expect("extension expected") == "zok");

            let should_error = path.to_str().unwrap().contains("compile_errors");

            println!("Testing {:?}", path);

            let file = File::open(path.clone()).unwrap();

            let mut reader = BufReader::new(file);

            let mut source = String::new();
            reader.read_to_string(&mut source).unwrap();

            let stdlib = std::fs::canonicalize("../zokrates_stdlib/stdlib").unwrap();
            let resolver = FileSystemResolver::with_stdlib_root(stdlib.to_str().unwrap());
            let res = compile::<Bn128Field, _>(source, path, Some(&resolver));

            assert_eq!(res.is_err(), should_error);
        }
    }

    #[test]
    fn execute_examples_ok() {
        //these examples should compile and run
        for p in glob("./examples/test*").expect("Failed to read glob pattern") {
            let path = match p {
                Ok(x) => x,
                Err(why) => panic!("Error: {:?}", why),
            };
            println!("Testing {:?}", path);

            let file = File::open(path.clone()).unwrap();

            let mut reader = BufReader::new(file);
            let mut source = String::new();
            reader.read_to_string(&mut source).unwrap();

            let stdlib = std::fs::canonicalize("../zokrates_stdlib/stdlib").unwrap();
            let resolver = FileSystemResolver::with_stdlib_root(stdlib.to_str().unwrap());

            let artifacts: CompilationArtifacts<Bn128Field> =
                compile(source, path, Some(&resolver)).unwrap();

            let interpreter = ir::Interpreter::default();

            let _ = interpreter
                .execute(&artifacts.prog(), &vec![Bn128Field::from(0)])
                .unwrap();
        }
    }

    #[test]
    fn execute_examples_err() {
        //these examples should compile but not run
        for p in glob("./examples/runtime_errors/*").expect("Failed to read glob pattern") {
            let path = match p {
                Ok(x) => x,
                Err(why) => panic!("Error: {:?}", why),
            };
            println!("Testing {:?}", path);

            let file = File::open(path.clone()).unwrap();

            let mut reader = BufReader::new(file);
            let mut source = String::new();
            reader.read_to_string(&mut source).unwrap();

            let stdlib = std::fs::canonicalize("../zokrates_stdlib/stdlib").unwrap();
            let resolver = FileSystemResolver::with_stdlib_root(stdlib.to_str().unwrap());

            let artifacts: CompilationArtifacts<Bn128Field> =
                compile(source, path, Some(&resolver)).unwrap();

            let interpreter = ir::Interpreter::default();

            let res = interpreter.execute(&artifacts.prog(), &vec![Bn128Field::from(0)]);

            assert!(res.is_err());
        }
    }
}
