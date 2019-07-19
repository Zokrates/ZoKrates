//
// @file bin.rs
// @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
// @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
// @date 2017

use bincode::{deserialize_from, serialize_into, Infinite};
use clap::{App, AppSettings, Arg, ArgMatches, SubCommand};
use serde_json::Value;
use std::fs::File;
use std::io::{stdin, BufReader, BufWriter, Read, Write};
use std::path::{Path, PathBuf};
use std::string::String;
use std::{env, io};
use zokrates_core::compile::compile;
use zokrates_core::ir;
use zokrates_core::proof_system::*;
use zokrates_field::{Bls12Field, Bn128Field, Field};
use zokrates_fs_resolver::resolve as fs_resolve;
#[cfg(feature = "github")]
use zokrates_github_resolver::{is_github_import, resolve as github_resolve};

const ZOKRATES_MAGIC: &[u8; 4] = &[0x5a, 0x4f, 0x4b, 0];
const ZOKRATES_VERSION_1: &[u8; 4] = &[0, 0, 0, 1];

fn main() {
    cli().unwrap_or_else(|e| {
        println!("{}", e);
        std::process::exit(1);
    })
}

enum ProgEnum {
    Bls12Program(ir::Prog<Bls12Field>),
    Bn128Program(ir::Prog<Bn128Field>),
}

fn deserialize_prog<R: Read>(mut r: R) -> ProgEnum {
    // Check the magic number, `ZOK`
    let mut magic = [0; 4];
    r.read_exact(&mut magic).unwrap();

    assert_eq!(&magic, ZOKRATES_MAGIC);

    // Check the version, 1
    let mut version = [0; 4];
    r.read_exact(&mut version).unwrap();

    assert_eq!(&version, ZOKRATES_VERSION_1);

    // Check the curve identifier, deserializing accordingly
    let mut curve = [0; 4];
    r.read_exact(&mut curve).unwrap();

    match curve {
        m if m == Bls12Field::id() => {
            ProgEnum::Bls12Program(deserialize_from(&mut r, Infinite).unwrap())
        }
        m if m == Bn128Field::id() => {
            ProgEnum::Bn128Program(deserialize_from(&mut r, Infinite).unwrap())
        }
        _ => unreachable!(),
    }
}

fn serialize_prog<T: Field, W: Write>(prog: &ir::Prog<T>, mut w: W) {
    w.write(ZOKRATES_MAGIC).unwrap();
    w.write(ZOKRATES_VERSION_1).unwrap();
    w.write(&T::id()).unwrap();

    serialize_into(&mut w, prog, Infinite)
        .map_err(|_| "Unable to write data to file.".to_string())
        .unwrap();
}

fn resolve<'a>(
    location: Option<String>,
    source: &'a str,
) -> Result<(BufReader<File>, String, &'a str), io::Error> {
    #[cfg(feature = "github")]
    {
        if is_github_import(source) {
            return github_resolve(location, source);
        };
    }
    fs_resolve(location, source)
}

fn cli_generate_proof<T: Field, P: ProofSystem<T>>(
    program: ir::Prog<T>,
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    println!("Generating proof...");

    // deserialize witness
    let witness_path = Path::new(sub_matches.value_of("witness").unwrap());
    let witness_file = match File::open(&witness_path) {
        Ok(file) => file,
        Err(why) => panic!("couldn't open {}: {}", witness_path.display(), why),
    };

    let witness = ir::Witness::read(witness_file)
        .map_err(|why| format!("could not load witness: {:?}", why))?;

    let pk_path = sub_matches.value_of("provingkey").unwrap();
    let proof_path = sub_matches.value_of("proofpath").unwrap();

    println!(
        "generate-proof successful: {:?}",
        P::generate_proof(program, witness, pk_path, proof_path)
    );
    Ok(())
}

fn cli_export_verifier<T: Field, P: ProofSystem<T>>(
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    let is_abiv2 = sub_matches.value_of("abi").unwrap() == "v2";
    println!("Exporting verifier...");

    // read vk file
    let input_path = Path::new(sub_matches.value_of("input").unwrap());
    let input_file = File::open(&input_path)
        .map_err(|why| format!("couldn't open {}: {}", input_path.display(), why))?;
    let reader = BufReader::new(input_file);

    let verifier = P::export_solidity_verifier(reader, is_abiv2);

    //write output file
    let output_path = Path::new(sub_matches.value_of("output").unwrap());
    let output_file = File::create(&output_path)
        .map_err(|why| format!("couldn't create {}: {}", output_path.display(), why))?;

    let mut writer = BufWriter::new(output_file);

    writer
        .write_all(&verifier.as_bytes())
        .map_err(|_| "Failed writing output to file.".to_string())?;
    println!("Finished exporting verifier.");
    Ok(())
}

fn cli_setup<T: Field, P: ProofSystem<T>>(
    program: ir::Prog<T>,
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    println!("Performing setup...");

    // print deserialized flattened program
    if !sub_matches.is_present("light") {
        println!("{}", program);
    }

    // get paths for proving and verification keys
    let pk_path = sub_matches.value_of("proving-key-path").unwrap();
    let vk_path = sub_matches.value_of("verification-key-path").unwrap();

    // run setup phase
    P::setup(program, pk_path, vk_path);

    Ok(())
}

fn cli_compute<T: Field>(program_ast: ir::Prog<T>, sub_matches: &ArgMatches) -> Result<(), String> {
    println!("Computing witness...");

    // print deserialized flattened program
    if !sub_matches.is_present("light") {
        println!("{}", program_ast);
    }

    let expected_cli_args_count =
        program_ast.public_arguments_count() + program_ast.private_arguments_count();

    // get arguments
    let arguments: Vec<_> = match sub_matches.values_of("arguments") {
        // take inline arguments
        Some(p) => p
            .map(|x| T::try_from_dec_str(x).map_err(|_| x.to_string()))
            .collect(),
        // take stdin arguments
        None => {
            if expected_cli_args_count > 0 {
                let mut stdin = stdin();
                let mut input = String::new();
                match stdin.read_to_string(&mut input) {
                    Ok(_) => {
                        input.retain(|x| x != '\n');
                        input
                            .split(" ")
                            .map(|x| T::try_from_dec_str(x).map_err(|_| x.to_string()))
                            .collect()
                    }
                    Err(_) => Err(String::from("???")),
                }
            } else {
                Ok(vec![])
            }
        }
    }
    .map_err(|e| format!("Could not parse argument: {}", e))?;

    if arguments.len() != expected_cli_args_count {
        Err(format!(
            "Wrong number of arguments. Given: {}, Required: {}.",
            arguments.len(),
            expected_cli_args_count
        ))?
    }

    let witness = program_ast
        .execute(&arguments)
        .map_err(|e| format!("Execution failed: {}", e))?;

    println!("\nWitness: \n\n{}", witness.format_outputs());

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

    let program_flattened: ir::Prog<T> = compile(&mut reader, Some(location), Some(resolve))
        .map_err(|e| format!("Compilation failed:\n\n {}", e))?;

    // number of constraints the flattened program will translate to.
    let num_constraints = program_flattened.constraint_count();

    // serialize flattened program and write to binary file
    let bin_output_file = File::create(&bin_output_path)
        .map_err(|why| format!("couldn't create {}: {}", bin_output_path.display(), why))?;

    let mut writer = BufWriter::new(bin_output_file);

    serialize_prog(&program_flattened, &mut writer);

    if !light {
        // write human-readable output file
        let hr_output_file = File::create(&hr_output_path)
            .map_err(|why| format!("couldn't create {}: {}", hr_output_path.display(), why))?;

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

fn cli() -> Result<(), String> {
    const FLATTENED_CODE_DEFAULT_PATH: &str = "out";
    const VERIFICATION_KEY_DEFAULT_PATH: &str = "verification.key";
    const PROVING_KEY_DEFAULT_PATH: &str = "proving.key";
    const VERIFICATION_CONTRACT_DEFAULT_PATH: &str = "verifier.sol";
    const WITNESS_DEFAULT_PATH: &str = "witness";
    const JSON_PROOF_PATH: &str = "proof.json";
    let default_curve = env::var("ZOKRATES_CURVE").unwrap_or(String::from("bn128"));
    let default_scheme = env::var("ZOKRATES_PROVING_SCHEME").unwrap_or(String::from("g16"));
    let default_solidity_abi = "v1";

    // cli specification using clap library
    let matches = App::new("ZoKrates")
    .setting(AppSettings::SubcommandRequiredElseHelp)
    .version(env!("CARGO_PKG_VERSION"))
    .author("Jacob Eberhardt, Thibaut Schaeffer, Stefan Deml")
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
        ).arg(Arg::with_name("curve")
            .short("c")
            .long("curve")
            .help("Curve to be used in the compilation. Available options are bn128 (default) and bls12_381")
            .takes_value(true)
            .required(false)
            .default_value(&default_curve)
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
        .arg(Arg::with_name("curve")
            .short("c")
            .long("curve")
            .help("Curve to be used in the setup. Available options are bn128 (default) and bls12_381. SHOULD NOT BE REQUIRED")
            .takes_value(true)
            .required(false)
            .default_value(&default_curve)
        )
        .arg(Arg::with_name("proving-scheme")
            .short("s")
            .long("proving-scheme")
            .help("Proving scheme to use in the setup. Available options are G16 (default), PGHR13 and GM17")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(&default_scheme)
        ).arg(Arg::with_name("light")
            .long("light")
            .help("Skip logs and human readable output")
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
        )
        .arg(Arg::with_name("output")
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
            .help("Curve to be used to export the verifier. Available options are bn128 (default) and bls12_381")
            .takes_value(true)
            .required(false)
            .default_value(&default_curve)
        ).arg(Arg::with_name("proving-scheme")
            .short("s")
            .long("proving-scheme")
            .help("Proving scheme to use to export the verifier. Available options are G16 (default), PGHR13 and GM17")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(&default_scheme)
        ).arg(Arg::with_name("abi")
            .short("a")
            .long("abi")
            .help("Flag for setting the version of the ABI Encoder used in the contract. Default is v1.")
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
        ).arg(Arg::with_name("light")
            .long("light")
            .help("Skip logs and human readable output")
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
        ).arg(Arg::with_name("curve")
            .short("c")
            .long("curve")
            .help("Curve to be used in the proof generation. Available options are bn128 (default) and bls12_381. SHOULD NOT BE REQUIRED")
            .takes_value(true)
            .required(false)
            .default_value(&default_curve)
        ).arg(Arg::with_name("proving-scheme")
            .short("s")
            .long("proving-scheme")
            .help("Proving scheme to use to generate the proof. Available options are G16 (default), PGHR13 and GM17")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(&default_scheme)
        )
    )
     .subcommand(SubCommand::with_name("print-proof")
        .about("Prints proof in chosen format [remix, json]")
        .arg(Arg::with_name("proofpath")
            .short("j")
            .long("proofpath")
            .help("Path of the JSON proof file")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(JSON_PROOF_PATH)
        ).arg(Arg::with_name("format")
            .short("f")
            .long("format")
            .value_name("FORMAT")
            .help("Format in which the proof should be printed. [remix, json]")
            .takes_value(true)
            .possible_values(&["remix", "json"])
            .required(true)
        )
    )
    .get_matches();

    match matches.subcommand() {
        ("compile", Some(sub_matches)) => {
            let curve = sub_matches.value_of("curve").unwrap();

            match curve {
                "bn128" => cli_compile::<Bn128Field>(sub_matches)?,
                "bls12_381" => cli_compile::<Bls12Field>(sub_matches)?,
                _ => unimplemented!(),
            }
        }
        ("compute-witness", Some(sub_matches)) => {
            // read compiled program
            let path = Path::new(sub_matches.value_of("input").unwrap());
            let file = File::open(&path)
                .map_err(|why| format!("couldn't open {}: {}", path.display(), why))?;

            let mut reader = BufReader::new(file);

            match deserialize_prog(&mut reader) {
                ProgEnum::Bn128Program(p) => cli_compute(p, sub_matches)?,
                ProgEnum::Bls12Program(p) => cli_compute(p, sub_matches)?,
            }
        }
        ("setup", Some(sub_matches)) => {
            let proof_system = sub_matches.value_of("proving-scheme").unwrap();

            // read compiled program
            let path = Path::new(sub_matches.value_of("input").unwrap());
            let file = File::open(&path)
                .map_err(|why| format!("couldn't open {}: {}", path.display(), why))?;

            let mut reader = BufReader::new(file);

            match (deserialize_prog(&mut reader), proof_system) {
                (ProgEnum::Bn128Program(p), "g16") => cli_setup::<_, G16>(p, sub_matches)?,
                (ProgEnum::Bls12Program(p), "g16") => cli_setup::<_, G16>(p, sub_matches)?,
                _ => unimplemented!(),
            }
        }
        ("export-verifier", Some(sub_matches)) => {
            let curve = sub_matches.value_of("curve").unwrap();
            let proof_system = sub_matches.value_of("proving-scheme").unwrap();

            match (curve, proof_system) {
                ("bn128", "g16") => cli_export_verifier::<Bn128Field, G16>(sub_matches)?,
                _ => unimplemented!(),
            }
        }
        ("generate-proof", Some(sub_matches)) => {
            let proof_system = sub_matches.value_of("proving-scheme").unwrap();

            // read compiled program
            let path = Path::new(sub_matches.value_of("input").unwrap());
            let file = File::open(&path)
                .map_err(|why| format!("couldn't open {}: {}", path.display(), why))?;

            let mut reader = BufReader::new(file);

            match (deserialize_prog(&mut reader), proof_system) {
                (ProgEnum::Bn128Program(p), "g16") => cli_generate_proof::<_, G16>(p, sub_matches)?,
                (ProgEnum::Bls12Program(p), "g16") => cli_generate_proof::<_, G16>(p, sub_matches)?,
                _ => unimplemented!(),
            }
        }
        ("print-proof", Some(sub_matches)) => {
            let format = sub_matches.value_of("format").unwrap();

            let path = Path::new(sub_matches.value_of("proofpath").unwrap());

            let file = File::open(&path)
                .map_err(|why| format!("couldn't open {}: {}", path.display(), why))?;

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

            let _: ir::Prog<Bn128Field> =
                compile(&mut reader, Some(location), Some(resolve)).unwrap();
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

            let program_flattened: ir::Prog<Bn128Field> =
                compile(&mut reader, Some(location), Some(resolve)).unwrap();

            let _ = program_flattened
                .execute(&vec![Bn128Field::from(0)])
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

            let program_flattened: ir::Prog<Bn128Field> =
                compile(&mut reader, Some(location), Some(resolve)).unwrap();

            let _ = program_flattened
                .execute(&vec![Bn128Field::from(0)])
                .unwrap();
        }
    }
}
