//
// @file bin.rs
// @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
// @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
// @date 2017

use bincode::{deserialize_from, serialize_into, Infinite};
use clap::{App, AppSettings, Arg, SubCommand};
use std::env;
use std::fs::File;
use std::io::{stdin, BufRead, BufReader, BufWriter, Write};
use std::path::{Path, PathBuf};
use std::string::String;
use zokrates_core::compile::compile;
use zokrates_core::ir;
use zokrates_core::proof_system::*;
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
    const JSON_PROOF_PATH: &str = "proof.json";
    let default_scheme = env::var("ZOKRATES_BACKEND").unwrap_or(String::from("g16"));

    // cli specification using clap library
    let matches = App::new("ZoKrates")
    .setting(AppSettings::SubcommandRequiredElseHelp)
    .version("0.4.2")
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
        .arg(Arg::with_name("scheme")
            .short("s")
            .long("scheme")
            .help("Backend to use in the setup. Available options are PGHR13 and GM17")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(&default_scheme)
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
        ).arg(Arg::with_name("scheme")
            .short("s")
            .long("scheme")
            .help("Backend to use to export the verifier. Available options are PGHR13 and GM17")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(&default_scheme)
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
        ).arg(Arg::with_name("input")
            .short("i")
            .long("input")
            .help("Path of compiled code")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(FLATTENED_CODE_DEFAULT_PATH)
        ).arg(Arg::with_name("scheme")
            .short("s")
            .long("scheme")
            .help("Backend to use to generate the proof. Available options are PGHR13 and GM17")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(&default_scheme)
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

            // create a CSV writer
            let mut wtr = csv::WriterBuilder::new()
                .delimiter(b' ')
                .flexible(true)
                .has_headers(false)
                .from_writer(output_file);

            // Write each line of the witness to the file
            for line in witness.into_human_readable() {
                wtr.serialize(line)
                    .map_err(|_| "Error writing witness to file".to_string())?;
            }

            wtr.flush()
                .map_err(|_| "Unable to flush buffer.".to_string())?;
        }
        ("setup", Some(sub_matches)) => {
            let scheme = get_scheme(sub_matches.value_of("scheme").unwrap())?;

            println!("Performing setup...");

            let path = Path::new(sub_matches.value_of("input").unwrap());
            let mut file = File::open(&path)
                .map_err(|why| format!("couldn't open {}: {}", path.display(), why))?;

            let program: ir::Prog<FieldPrime> =
                deserialize_from(&mut file, Infinite).map_err(|why| format!("{:?}", why))?;

            // print deserialized flattened program
            println!("{}", program);

            // get paths for proving and verification keys
            let pk_path = sub_matches.value_of("proving-key-path").unwrap();
            let vk_path = sub_matches.value_of("verification-key-path").unwrap();

            // run setup phase
            scheme.setup(program, pk_path, vk_path);
        }
        ("export-verifier", Some(sub_matches)) => {
            {
                let scheme = get_scheme(sub_matches.value_of("scheme").unwrap())?;

                println!("Exporting verifier...");

                // read vk file
                let input_path = Path::new(sub_matches.value_of("input").unwrap());
                let input_file = File::open(&input_path)
                    .map_err(|why| format!("couldn't open {}: {}", input_path.display(), why))?;
                let reader = BufReader::new(input_file);

                let verifier = scheme.export_solidity_verifier(reader);

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
        ("generate-proof", Some(sub_matches)) => {
            println!("Generating proof...");

            let scheme = get_scheme(sub_matches.value_of("scheme").unwrap())?;

            // deserialize witness
            let witness_path = Path::new(sub_matches.value_of("witness").unwrap());
            let witness_file = match File::open(&witness_path) {
                Ok(file) => file,
                Err(why) => panic!("couldn't open {}: {}", witness_path.display(), why),
            };

            let mut rdr = csv::ReaderBuilder::new()
                .delimiter(b' ')
                .flexible(true)
                .has_headers(false)
                .from_reader(witness_file);

            let witness = ir::Witness::from_human_readable(rdr.deserialize().map(|i| i.unwrap()));

            let pk_path = sub_matches.value_of("provingkey").unwrap();
            let proof_path = sub_matches.value_of("proofpath").unwrap();

            let program_path = Path::new(sub_matches.value_of("input").unwrap());
            let mut program_file = File::open(&program_path)
                .map_err(|why| format!("couldn't open {}: {}", program_path.display(), why))?;

            let program: ir::Prog<FieldPrime> = deserialize_from(&mut program_file, Infinite)
                .map_err(|why| format!("{:?}", why))?;

            println!(
                "generate-proof successful: {:?}",
                scheme.generate_proof(program, witness, pk_path, proof_path)
            );
        }
        _ => unreachable!(),
    }
    Ok(())
}

fn get_scheme(scheme_str: &str) -> Result<&'static ProofSystem, String> {
    match scheme_str.to_lowercase().as_ref() {
        #[cfg(feature = "libsnark")]
        "pghr13" => Ok(&PGHR13 {}),
        #[cfg(feature = "libsnark")]
        "gm17" => Ok(&GM17 {}),
        "g16" => Ok(&G16 {}),
        s => Err(format!("Backend \"{}\" not supported", s)),
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

            let _: ir::Prog<FieldPrime> =
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

            let _ = program_flattened
                .execute(&vec![FieldPrime::from(0)])
                .unwrap();
        }
    }
}
