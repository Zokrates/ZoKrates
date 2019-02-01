//
// @file bin.rs
// @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
// @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
// @date 2017

use bincode::{deserialize_from, serialize_into, Infinite};
use clap::{App, AppSettings, Arg, SubCommand};
#[cfg(feature = "libsnark")]
use std::collections::HashMap;
use std::env;
use std::fs::File;
use std::io::{stdin, BufRead, BufReader, BufWriter, Write};
use std::path::{Path, PathBuf};
use std::string::String;
use zokrates_core::compile::compile;
use zokrates_core::ir;
#[cfg(feature = "libsnark")]
use zokrates_core::ir::r1cs_program;
#[cfg(feature = "libsnark")]
use zokrates_core::proof_system::{ProofSystem, GM17, PGHR13};
use zokrates_field::field::{Field, FieldPrime};
use zokrates_fs_resolver::resolve as fs_resolve;

fn main() {
    cli().unwrap_or_else(|e| {
        println!("{}", e);
        std::process::exit(1);
    })
}

fn cli() -> Result<(), String> {
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
    .version("0.4.0")
    .author("Jacob Eberhardt, Thibaut Schaeffer, Dennis Kuhnert")
    .about("Supports generation of zkSNARKs from high level language code including Smart Contracts for proof verification on the Ethereum Blockchain.\n'I know that I show nothing!'")
    .subcommand(SubCommand::with_name("compile")
        .about("Compiles into flattened conditions. Produces two files: human-readable '.code' file for debugging and binary file")
        .arg(Arg::with_name("input")
            .short("i")
            .long("input")
            .help("Path of the source code")
            .value_name("FILE")
            .takes_value(true)
            .required(true)
        ).arg(Arg::with_name("output")
            .short("o")
            .long("output")
            .help("Path of the output file")
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
        .about("Performs a trusted setup for a given constraint system")
        .arg(Arg::with_name("input")
            .short("i")
            .long("input")
            .help("Path of compiled code")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(FLATTENED_CODE_DEFAULT_PATH)
        )
        .arg(Arg::with_name("proving-key-path")
            .short("p")
            .long("proving-key-path")
            .help("Path of the generated proving key file")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(PROVING_KEY_DEFAULT_PATH)
        )
        .arg(Arg::with_name("verification-key-path")
            .short("v")
            .long("verification-key-path")
            .help("Path of the generated verification key file")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(VERIFICATION_KEY_DEFAULT_PATH)
        )
        .arg(Arg::with_name("meta-information")
            .short("m")
            .long("meta-information")
            .help("Path of the file containing meta-information for variable transformation")
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
        .about("Exports a verifier as Solidity smart contract")
        .arg(Arg::with_name("input")
            .short("i")
            .long("input")
            .help("Path of the verifier")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(VERIFICATION_KEY_DEFAULT_PATH)
        )
        .arg(Arg::with_name("output")
            .short("o")
            .long("output")
            .help("Path of the output file")
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
        .about("Calculates a witness for a given constraint system")
        .arg(Arg::with_name("input")
            .short("i")
            .long("input")
            .help("Path of compiled code")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(FLATTENED_CODE_DEFAULT_PATH)
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
            .help("Arguments for the program's main method as a space separated list")
            .takes_value(true)
            .multiple(true) // allows multiple values
            .required(false)
        ).arg(Arg::with_name("interactive")
            .long("interactive")
            .help("Enter private inputs interactively. Public inputs still need to be passed non-interactively")
            .required(false)
        )
    )
    .subcommand(SubCommand::with_name("generate-proof")
        .about("Calculates a proof for a given constraint system and witness.")
        .arg(Arg::with_name("witness")
            .short("w")
            .long("witness")
            .help("Path of the witness file")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(WITNESS_DEFAULT_PATH)
        ).arg(Arg::with_name("provingkey")
            .short("p")
            .long("provingkey")
            .help("Path of the proving key file")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(PROVING_KEY_DEFAULT_PATH)
        ).arg(Arg::with_name("proofpath")
            .short("j")
            .long("proofpath")
            .help("Path of the JSON proof file")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(JSON_PROOF_PATH)
        ).arg(Arg::with_name("meta-information")
            .short("i")
            .long("meta-information")
            .help("Path of file containing meta information for variable transformation")
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
            println!("Compiling {}\n", sub_matches.value_of("input").unwrap());

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
                compile(&mut reader, Some(location), Some(fs_resolve))
                    .map_err(|e| format!("Compilation failed:\n\n {}", e))?;

            // number of constraints the flattened program will translate to.
            let num_constraints = program_flattened.constraint_count();

            // serialize flattened program and write to binary file
            let mut bin_output_file = File::create(&bin_output_path)
                .map_err(|why| format!("couldn't create {}: {}", bin_output_path.display(), why))?;

            serialize_into(&mut bin_output_file, &program_flattened, Infinite)
                .map_err(|_| "Unable to write data to file.".to_string())?;

            if !light {
                // write human-readable output file
                let hr_output_file = File::create(&hr_output_path).map_err(|why| {
                    format!("couldn't create {}: {}", hr_output_path.display(), why)
                })?;

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
        }
        ("compute-witness", Some(sub_matches)) => {
            println!("Computing witness for:");

            // read compiled program
            let path = Path::new(sub_matches.value_of("input").unwrap());
            let mut file = File::open(&path)
                .map_err(|why| format!("couldn't open {}: {}", path.display(), why))?;

            let program_ast: ir::Prog<FieldPrime> =
                deserialize_from(&mut file, Infinite).map_err(|why| why.to_string())?;

            // print deserialized flattened program
            println!("{}", program_ast);

            // validate #arguments
            let cli_arguments = match sub_matches.values_of("arguments") {
                Some(p) => p.map(|x| FieldPrime::try_from_str(x)).collect(),
                None => Ok(vec![]),
            }
            .map_err(|_| "Could not parse arguments".to_string())?;

            // handle interactive and non-interactive modes
            let is_interactive = sub_matches.occurrences_of("interactive") > 0;

            // in interactive mode, only public inputs are expected
            let expected_cli_args_count = if is_interactive {
                program_ast.public_arguments_count()
            } else {
                program_ast.public_arguments_count() + program_ast.private_arguments_count()
            };

            if cli_arguments.len() != expected_cli_args_count {
                return Err(format!(
                    "Wrong number of arguments. Given: {}, Required: {}.",
                    cli_arguments.len(),
                    expected_cli_args_count
                ));
            }

            let mut cli_arguments_iter = cli_arguments.into_iter();
            let arguments: Vec<FieldPrime> = program_ast
                .parameters()
                .iter()
                .map(|x| {
                    match x.private && is_interactive {
                        // private inputs are passed interactively when the flag is present
                        true => loop {
                            println!("Please enter a value for {:?}:", x.id);
                            let mut input = String::new();
                            let stdin = stdin();
                            let r = stdin.lock().read_line(&mut input);

                            match r {
                                Ok(_) => {
                                    let input = input.trim();
                                    match FieldPrime::try_from_str(&input) {
                                        Ok(v) => return v,
                                        Err(_) => {
                                            println!("Not a correct String, try again");
                                            continue;
                                        }
                                    }
                                }
                                Err(_) => {
                                    println!("Not a correct String, try again");
                                    continue;
                                }
                            };
                        },
                        // otherwise, they are taken from the CLI arguments
                        false => cli_arguments_iter.next().unwrap(),
                    }
                })
                .collect();

            let witness = program_ast
                .execute(&arguments)
                .map_err(|e| format!("Execution failed: {}", e))?;

            println!("\nWitness: \n\n{}", witness.format_outputs());

            // write witness to file
            let output_path = Path::new(sub_matches.value_of("output").unwrap());
            let output_file = File::create(&output_path)
                .map_err(|why| format!("couldn't create {}: {}", output_path.display(), why))?;

            let mut bw = BufWriter::new(output_file);
            write!(&mut bw, "{}", witness)
                .map_err(|_| "Unable to write data to file.".to_string())?;
            bw.flush()
                .map_err(|_| "Unable to flush buffer.".to_string())?;
        }
        #[cfg(feature = "libsnark")]
        ("setup", Some(sub_matches)) => {
            let backend = get_backend(sub_matches.value_of("backend").unwrap())?;

            println!("Performing setup...");

            let path = Path::new(sub_matches.value_of("input").unwrap());
            let mut file = File::open(&path)
                .map_err(|why| format!("couldn't open {}: {}", path.display(), why))?;

            let program: ir::Prog<FieldPrime> =
                deserialize_from(&mut file, Infinite).map_err(|why| format!("{:?}", why))?;

            // print deserialized flattened program
            println!("{}", program);

            // transform to R1CS
            let (variables, public_variables_count, a, b, c) = r1cs_program(program);

            // write variables meta information to file
            let var_inf_path = Path::new(sub_matches.value_of("meta-information").unwrap());
            let var_inf_file = File::create(&var_inf_path)
                .map_err(|why| format!("couldn't open {}: {}", var_inf_path.display(), why))?;
            let mut bw = BufWriter::new(var_inf_file);

            write!(
                &mut bw,
                "Private inputs offset:\n{}\n",
                public_variables_count
            )
            .map_err(|_| "Unable to write data to file.".to_string())?;
            write!(&mut bw, "R1CS variable order:\n")
                .map_err(|_| "Unable to write data to file.".to_string())?;

            for var in &variables {
                write!(&mut bw, "{} ", var)
                    .map_err(|_| "Unable to write data to file.".to_string())?;
            }
            write!(&mut bw, "\n").map_err(|_| "Unable to write data to file.".to_string())?;
            bw.flush()
                .map_err(|_| "Unable to flush buffer.".to_string())?;

            // get paths for proving and verification keys
            let pk_path = sub_matches.value_of("proving-key-path").unwrap();
            let vk_path = sub_matches.value_of("verification-key-path").unwrap();

            // run setup phase
            // number of inputs in the zkSNARK sense, i.e., input variables + output variables
            println!(
                "setup successful: {:?}",
                backend.setup(
                    variables,
                    a,
                    b,
                    c,
                    public_variables_count - 1,
                    pk_path,
                    vk_path
                )
            );
        }
        #[cfg(feature = "libsnark")]
        ("export-verifier", Some(sub_matches)) => {
            {
                let backend = get_backend(sub_matches.value_of("backend").unwrap())?;

                println!("Exporting verifier...");

                // read vk file
                let input_path = Path::new(sub_matches.value_of("input").unwrap());
                let input_file = File::open(&input_path)
                    .map_err(|why| format!("couldn't open {}: {}", input_path.display(), why))?;
                let reader = BufReader::new(input_file);

                let verifier = backend.export_solidity_verifier(reader);

                //write output file
                let output_path = Path::new(sub_matches.value_of("output").unwrap());
                let mut output_file = File::create(&output_path)
                    .map_err(|why| format!("couldn't create {}: {}", output_path.display(), why))?;

                output_file
                    .write_all(&verifier.as_bytes())
                    .map_err(|_| "Failed writing output to file.".to_string())?;
                println!("Finished exporting verifier.");
            }
        }
        #[cfg(feature = "libsnark")]
        ("generate-proof", Some(sub_matches)) => {
            println!("Generating proof...");

            let backend = get_backend(sub_matches.value_of("backend").unwrap())?;

            // deserialize witness
            let witness_path = Path::new(sub_matches.value_of("witness").unwrap());
            let witness_file = File::open(&witness_path)
                .map_err(|why| format!("couldn't open {}: {}", witness_path.display(), why))?;

            let reader = BufReader::new(witness_file);
            let mut lines = reader.lines();
            let mut witness_map = HashMap::new();

            loop {
                match lines.next() {
                    Some(Ok(ref x)) => {
                        let pairs: Vec<&str> = x.split_whitespace().collect();
                        witness_map.insert(
                            pairs[0].to_string(),
                            FieldPrime::from_dec_string(pairs[1].to_string()),
                        );
                    }
                    None => break,
                    Some(Err(err)) => return Err(format!("Error reading witness: {}", err)),
                }
            }

            // determine variable order
            let var_inf_path = Path::new(sub_matches.value_of("meta-information").unwrap());
            let var_inf_file = File::open(&var_inf_path)
                .map_err(|why| format!("couldn't open {}: {}", var_inf_path.display(), why))?;
            let var_reader = BufReader::new(var_inf_file);
            let mut var_lines = var_reader.lines();

            // get private inputs offset
            let private_inputs_offset;
            if let Some(Ok(ref o)) = var_lines.nth(1) {
                // consumes first 2 lines
                private_inputs_offset = o
                    .parse()
                    .map_err(|_| "Failed parsing private inputs offset")?;
            } else {
                return Err(format!("Error reading private inputs offset"));
            }

            // get variables vector
            let mut variables: Vec<String> = Vec::new();
            if let Some(Ok(ref v)) = var_lines.nth(1) {
                let iter = v.split_whitespace();
                for i in iter {
                    variables.push(i.to_string());
                }
            } else {
                return Err(format!("Error reading variables"));
            }

            println!("Using Witness: {:?}", witness_map);

            let witness: Vec<_> = variables.iter().map(|x| witness_map[x].clone()).collect();

            // split witness into public and private inputs at offset
            let mut public_inputs: Vec<_> = witness.clone();
            let private_inputs: Vec<_> = public_inputs.split_off(private_inputs_offset);

            println!("Public inputs: {:?}", public_inputs);
            println!("Private inputs: {:?}", private_inputs);

            let pk_path = sub_matches.value_of("provingkey").unwrap();
            let proof_path = sub_matches.value_of("proofpath").unwrap();

            // run libsnark
            println!(
                "generate-proof successful: {:?}",
                backend.generate_proof(pk_path, proof_path, public_inputs, private_inputs)
            );
        }
        _ => unreachable!(),
    }
    Ok(())
}

#[cfg(feature = "libsnark")]
fn get_backend(backend_str: &str) -> Result<&'static ProofSystem, String> {
    match backend_str.to_lowercase().as_ref() {
        "pghr13" => Ok(&PGHR13 {}),
        "gm17" => Ok(&GM17 {}),
        s => Err(format!("Backend \"{}\" not supported", s)),
    }
}

#[cfg(test)]
mod tests {
    extern crate glob;
    use self::glob::glob;
    use super::*;
    use zokrates_core::ir::r1cs_program;

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

            let (..) = r1cs_program(program_flattened);
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

            let (..) = r1cs_program(program_flattened.clone());
            let _ = program_flattened
                .execute(&vec![FieldPrime::from(0)])
                .unwrap();
        }
    }

    #[test]
    #[should_panic]
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

            let (..) = r1cs_program(program_flattened.clone());

            let _ = program_flattened
                .execute(&vec![FieldPrime::from(0)])
                .unwrap();
        }
    }
}
