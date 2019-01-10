//
// @file bin.rs
// @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
// @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
// @date 2017

extern crate bincode;
extern crate clap;
extern crate regex;
extern crate serde_json;
extern crate zokrates_core;
extern crate zokrates_field;
extern crate zokrates_fs_resolver;

use bincode::{deserialize_from, serialize_into, Infinite};
use clap::{App, AppSettings, Arg, SubCommand};
use std::env;
use std::fs::File;
use std::io::{stdin, BufRead, BufReader, BufWriter, Write};
use std::path::{Path, PathBuf};
use std::string::String;
use zokrates_core::compile::compile;
use zokrates_core::ir;
#[cfg(feature = "libsnark")]
use zokrates_core::proof_system::{ProofSystem, GM17, PGHR13};
use zokrates_field::field::FieldPrime;
use zokrates_fs_resolver::resolve as fs_resolve;

#[cfg(feature = "libsnark")]
fn get_backend(backend_str: &str) -> &'static ProofSystem {
    match backend_str.to_lowercase().as_ref() {
        "pghr13" => &PGHR13 {},
        "gm17" => &GM17 {},
        s => panic!("Backend \"{}\" not supported", s),
    }
}

fn main() {
    const FLATTENED_CODE_DEFAULT_PATH: &str = "out";
    const VERIFICATION_KEY_DEFAULT_PATH: &str = "verification.key";
    const PROVING_KEY_DEFAULT_PATH: &str = "proving.key";
    const VERIFICATION_CONTRACT_DEFAULT_PATH: &str = "verifier.sol";
    const WITNESS_DEFAULT_PATH: &str = "witness";
    const VARIABLES_INFORMATION_KEY_DEFAULT_PATH: &str = "variables.inf";
    const JSON_PROOF_PATH: &str = "proof.json";
    let default_backend = env::var("ZOKRATES_BACKEND").unwrap_or(String::from("pghr13"));

    // cli specification using clap library
    let matches = App::new("ZoKrates")
    .setting(AppSettings::SubcommandRequiredElseHelp)
    .version("0.3.2")
    .author("Jacob Eberhardt, Thibaut Schaeffer, Dennis Kuhnert")
    .about("Supports generation of zkSNARKs from high level language code including Smart Contracts for proof verification on the Ethereum Blockchain.\n'I know that I show nothing!'")
    .subcommand(SubCommand::with_name("compile")
        .about("Compiles into flattened conditions. Produces two files: human-readable '.code' file and binary file")
        .arg(Arg::with_name("input")
            .short("i")
            .long("input")
            .help("path of source code file to compile.")
            .value_name("FILE")
            .takes_value(true)
            .required(true)
        ).arg(Arg::with_name("output")
            .short("o")
            .long("output")
            .help("output file path.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(FLATTENED_CODE_DEFAULT_PATH)
        ).arg(Arg::with_name("light")
            .long("light")
            .help("Skip logs and human readable output")
            .required(false)
        )
     )
    .subcommand(SubCommand::with_name("setup")
        .about("Performs a trusted setup for a given constraint system.")
        .arg(Arg::with_name("input")
            .short("i")
            .long("input")
            .help("path of compiled code.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(FLATTENED_CODE_DEFAULT_PATH)
        )
        .arg(Arg::with_name("proving-key-path")
            .short("p")
            .long("proving-key-path")
            .help("Path of the generated proving key file.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(PROVING_KEY_DEFAULT_PATH)
        )
        .arg(Arg::with_name("verification-key-path")
            .short("v")
            .long("verification-key-path")
            .help("Path of the generated verification key file.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(VERIFICATION_KEY_DEFAULT_PATH)
        )
        .arg(Arg::with_name("meta-information")
            .short("m")
            .long("meta-information")
            .help("Path of file containing meta information for variable transformation.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(VARIABLES_INFORMATION_KEY_DEFAULT_PATH)
        )
        .arg(Arg::with_name("backend")
            .short("b")
            .long("backend")
            .help("Backend to use in the setup. Available options are PGHR13 and GM17")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(&default_backend)
        )
    )
    .subcommand(SubCommand::with_name("export-verifier")
        .about("Exports a verifier as Solidity smart contract.")
        .arg(Arg::with_name("input")
            .short("i")
            .long("input")
            .help("path of verifier.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(VERIFICATION_KEY_DEFAULT_PATH)
        )
        .arg(Arg::with_name("output")
            .short("o")
            .long("output")
            .help("output file path.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(VERIFICATION_CONTRACT_DEFAULT_PATH)
        ).arg(Arg::with_name("backend")
            .short("b")
            .long("backend")
            .help("Backend to use to export the verifier. Available options are PGHR13 and GM17")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(&default_backend)
        )
    )
    .subcommand(SubCommand::with_name("compute-witness")
        .about("Calculates a witness for a given constraint system, i.e., a variable assignment which satisfies all constraints. Private inputs are specified interactively.")
        .arg(Arg::with_name("input")
            .short("i")
            .long("input")
            .help("path of compiled code.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(FLATTENED_CODE_DEFAULT_PATH)
        ).arg(Arg::with_name("output")
            .short("o")
            .long("output")
            .help("output file path.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(WITNESS_DEFAULT_PATH)
        ).arg(Arg::with_name("arguments")
            .short("a")
            .long("arguments")
            .help("Arguments for the program's main method. Space separated list.")
            .takes_value(true)
            .multiple(true) // allows multiple values
            .required(false)
        ).arg(Arg::with_name("interactive")
            .long("interactive")
            .help("enter private inputs interactively.")
            .required(false)
        )
    )
    .subcommand(SubCommand::with_name("generate-proof")
        .about("Calculates a proof for a given constraint system and witness.")
        .arg(Arg::with_name("witness")
            .short("w")
            .long("witness")
            .help("Path of witness file.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(WITNESS_DEFAULT_PATH)
        ).arg(Arg::with_name("provingkey")
            .short("p")
            .long("provingkey")
            .help("Path of proving key file.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(PROVING_KEY_DEFAULT_PATH)
        ).arg(Arg::with_name("proofpath")
            .short("j")
            .long("proofpath")
            .help("Path of the json proof file")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(JSON_PROOF_PATH)
        ).arg(Arg::with_name("meta-information")
            .short("i")
            .long("meta-information")
            .help("Path of file containing meta information for variable transformation.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(VARIABLES_INFORMATION_KEY_DEFAULT_PATH)
        ).arg(Arg::with_name("backend")
            .short("b")
            .long("backend")
            .help("Backend to use to generate the proof. Available options are PGHR13 and GM17")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(&default_backend)
        )
    )
    .get_matches();

    match matches.subcommand() {
        ("compile", Some(sub_matches)) => {
            println!("Compiling {}", sub_matches.value_of("input").unwrap());

            let path = PathBuf::from(sub_matches.value_of("input").unwrap());

            let location = path
                .parent()
                .unwrap()
                .to_path_buf()
                .into_os_string()
                .into_string()
                .unwrap();

            let light = sub_matches.occurrences_of("light") > 0;

            let bin_output_path = Path::new(sub_matches.value_of("output").unwrap());

            let hr_output_path = bin_output_path.to_path_buf().with_extension("code");

            let file = File::open(path.clone()).unwrap();

            let mut reader = BufReader::new(file);

            let program_flattened: ir::Prog<FieldPrime> =
                match compile(&mut reader, Some(location), Some(fs_resolve)) {
                    Ok(p) => p,
                    Err(why) => panic!("Compilation failed: {}", why),
                };

            // number of constraints the flattened program will translate to.
            let num_constraints = program_flattened.constraint_count();

            // serialize flattened program and write to binary file
            let mut bin_output_file = match File::create(&bin_output_path) {
                Ok(file) => file,
                Err(why) => panic!("couldn't create {}: {}", bin_output_path.display(), why),
            };

            serialize_into(&mut bin_output_file, &program_flattened, Infinite)
                .expect("Unable to write data to file.");

            if !light {
                // write human-readable output file
                let hr_output_file = match File::create(&hr_output_path) {
                    Ok(file) => file,
                    Err(why) => panic!("couldn't create {}: {}", hr_output_path.display(), why),
                };

                let mut hrofb = BufWriter::new(hr_output_file);
                write!(&mut hrofb, "{}\n", program_flattened)
                    .expect("Unable to write data to file.");
                hrofb.flush().expect("Unable to flush buffer.");
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
        }
        ("compute-witness", Some(sub_matches)) => {
            println!("Computing witness for:");

            // read compiled program
            let path = Path::new(sub_matches.value_of("input").unwrap());
            let mut file = match File::open(&path) {
                Ok(file) => file,
                Err(why) => panic!("couldn't open {}: {}", path.display(), why),
            };

            let program_ast: ir::Prog<FieldPrime> = match deserialize_from(&mut file, Infinite) {
                Ok(x) => x,
                Err(why) => {
                    println!("{:?}", why);
                    std::process::exit(1);
                }
            };

            // print deserialized flattened program
            println!("{}", program_ast);

            // validate #arguments
            let mut cli_arguments: Vec<FieldPrime> = Vec::new();
            match sub_matches.values_of("arguments") {
                Some(p) => {
                    let arg_strings: Vec<&str> = p.collect();
                    cli_arguments = arg_strings
                        .into_iter()
                        .map(|x| FieldPrime::from(x))
                        .collect();
                }
                None => {}
            }

            // handle interactive and non-interactive modes
            let is_interactive = sub_matches.occurrences_of("interactive") > 0;

            // in interactive mode, only public inputs are expected
            let expected_cli_args_count = if is_interactive {
                program_ast.public_arguments_count()
            } else {
                program_ast.public_arguments_count() + program_ast.private_arguments_count()
            };

            if cli_arguments.len() != expected_cli_args_count {
                println!(
                    "Wrong number of arguments. Given: {}, Required: {}.",
                    cli_arguments.len(),
                    expected_cli_args_count
                );
                std::process::exit(1);
            }

            let mut cli_arguments_iter = cli_arguments.into_iter();
            let arguments: Vec<FieldPrime> = program_ast
                .parameters()
                .iter()
                .map(|x| {
                    match x.is_private() && is_interactive {
                        // private inputs are passed interactively when the flag is present
                        true => {
                            println!("Please enter a value for {:?}:", x);
                            let mut input = String::new();
                            let stdin = stdin();
                            stdin
                                .lock()
                                .read_line(&mut input)
                                .expect("Did not enter a correct String");
                            FieldPrime::from(input.trim())
                        }
                        // otherwise, they are taken from the CLI arguments
                        false => match cli_arguments_iter.next() {
                            Some(x) => x,
                            None => {
                                std::process::exit(1);
                            }
                        },
                    }
                })
                .collect();

            let witness = program_ast
                .execute(&arguments)
                .unwrap_or_else(|e| panic!(format!("Execution failed: {}", e)));

            println!("\nWitness: \n\n{}", witness.format_outputs());

            // write witness to file
            let output_path = Path::new(sub_matches.value_of("output").unwrap());
            let output_file = match File::create(&output_path) {
                Ok(file) => file,
                Err(why) => panic!("couldn't create {}: {}", output_path.display(), why),
            };
            let mut bw = BufWriter::new(output_file);
            write!(
                &mut bw,
                "{}",
                &serde_json::to_string(&ir::FullWitness::from(witness)).unwrap()
            )
            .expect("Unable to write data to file.");
            bw.flush().expect("Unable to flush buffer.");
        }
        #[cfg(feature = "libsnark")]
        ("setup", Some(sub_matches)) => {
            println!("Performing setup...");

            let backend = get_backend(sub_matches.value_of("backend").unwrap());

            let path = Path::new(sub_matches.value_of("input").unwrap());
            let mut file = match File::open(&path) {
                Ok(file) => file,
                Err(why) => panic!("couldn't open {}: {}", path.display(), why),
            };

            let program: ir::Prog<FieldPrime> = match deserialize_from(&mut file, Infinite) {
                Ok(x) => x,
                Err(why) => {
                    println!("{:?}", why);
                    std::process::exit(1);
                }
            };

            // print deserialized flattened program
            println!("{}", program);

            // get paths for proving and verification keys
            let pk_path = sub_matches.value_of("proving-key-path").unwrap();
            let vk_path = sub_matches.value_of("verification-key-path").unwrap();

            // run setup phase
            // number of inputs in the zkSNARK sense, i.e., input variables + output variables
            println!(
                "setup successful: {:?}",
                backend.setup(program, pk_path, vk_path)
            );
        }
        #[cfg(feature = "libsnark")]
        ("export-verifier", Some(sub_matches)) => {
            {
                println!("Exporting verifier...");

                let backend = get_backend(sub_matches.value_of("backend").unwrap());

                // read vk file
                let input_path = Path::new(sub_matches.value_of("input").unwrap());
                let input_file = match File::open(&input_path) {
                    Ok(input_file) => input_file,
                    Err(why) => panic!("couldn't open {}: {}", input_path.display(), why),
                };
                let reader = BufReader::new(input_file);

                let verifier = backend.export_solidity_verifier(reader);

                //write output file
                let output_path = Path::new(sub_matches.value_of("output").unwrap());
                let mut output_file = match File::create(&output_path) {
                    Ok(file) => file,
                    Err(why) => panic!("couldn't create {}: {}", output_path.display(), why),
                };

                output_file
                    .write_all(&verifier.as_bytes())
                    .expect("Failed writing output to file.");
                println!("Finished exporting verifier.");
            }
        }
        #[cfg(feature = "libsnark")]
        ("generate-proof", Some(sub_matches)) => {
            println!("Generating proof...");

            let backend = get_backend(sub_matches.value_of("backend").unwrap());

            // deserialize witness
            let witness_path = Path::new(sub_matches.value_of("witness").unwrap());
            let witness_file = match File::open(&witness_path) {
                Ok(file) => file,
                Err(why) => panic!("couldn't open {}: {}", witness_path.display(), why),
            };

            let e = serde_json::to_string(&FieldPrime::from(4986798698698608979879872)).unwrap();

            println!("{:?}", e);

            let e: Result<FieldPrime, _> = serde_json::from_str(&e);

            let reader = BufReader::new(witness_file);

            let witness: ir::FullWitness<FieldPrime> = serde_json::from_reader(reader).unwrap();

            println!("Using Witness: {:?}", witness);

            // println!("Public inputs: {:?}", public_inputs);
            // println!("Private inputs: {:?}", private_inputs);

            let pk_path = sub_matches.value_of("provingkey").unwrap();
            let proof_path = sub_matches.value_of("proofpath").unwrap();

            // run libsnark
            // println!(
            //     "generate-proof successful: {:?}",
            //     backend.generate_proof(witness, pk_path, proof_path)
            // );
        }
        _ => unimplemented!(), // Either no subcommand or one not tested for...
    }
}

#[cfg(test)]
mod tests {
    extern crate glob;
    use self::glob::glob;
    use super::*;

    #[test]
    fn examples() {
        for p in glob("./examples/**/*.code").expect("Failed to read glob pattern") {
            let path = match p {
                Ok(x) => x,
                Err(why) => panic!("Error: {:?}", why),
            };

            if path.to_str().unwrap().contains("error") {
                continue;
            }

            println!("Testing {:?}", path);

            let file = File::open(path.clone()).unwrap();

            let mut reader = BufReader::new(file);
            let location = path
                .parent()
                .unwrap()
                .to_path_buf()
                .into_os_string()
                .into_string()
                .unwrap();

            let program_flattened: ir::Prog<FieldPrime> =
                compile(&mut reader, Some(location), Some(fs_resolve)).unwrap();
        }
    }

    #[test]
    fn examples_with_input_success() {
        //these examples should compile and run
        for p in glob("./examples/test*.code").expect("Failed to read glob pattern") {
            let path = match p {
                Ok(x) => x,
                Err(why) => panic!("Error: {:?}", why),
            };
            println!("Testing {:?}", path);

            let file = File::open(path.clone()).unwrap();

            let location = path
                .parent()
                .unwrap()
                .to_path_buf()
                .into_os_string()
                .into_string()
                .unwrap();

            let mut reader = BufReader::new(file);

            let program_flattened: ir::Prog<FieldPrime> =
                compile(&mut reader, Some(location), Some(fs_resolve)).unwrap();

            let _ = program_flattened
                .execute(&vec![FieldPrime::from(0)])
                .unwrap();
        }
    }

    #[test]
    fn examples_with_input_failure() {
        //these examples should compile but not run
        for p in glob("./examples/runtime_errors/*.code").expect("Failed to read glob pattern") {
            let path = match p {
                Ok(x) => x,
                Err(why) => panic!("Error: {:?}", why),
            };
            println!("Testing {:?}", path);

            let file = File::open(path.clone()).unwrap();

            let location = path
                .parent()
                .unwrap()
                .to_path_buf()
                .into_os_string()
                .into_string()
                .unwrap();

            let mut reader = BufReader::new(file);

            let program_flattened: ir::Prog<FieldPrime> =
                compile(&mut reader, Some(location), Some(fs_resolve)).unwrap();

            let result = std::panic::catch_unwind(|| {
                let _ = program_flattened
                    .execute(&vec![FieldPrime::from(0)])
                    .unwrap();
            });
            assert!(result.is_err());
        }
    }
}
