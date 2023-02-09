use crate::cli_constants::{self, FLATTENED_CODE_DEFAULT_PATH};
use clap::{App, Arg, ArgMatches, SubCommand};
use serde_json::from_reader;
use std::fs::File;
use std::io::{stdin, Write};
use std::io::{BufReader, Read};
use std::path::Path;
use zokrates_abi::Encode;
use zokrates_ast::ir::{self, ProgEnum};
use zokrates_ast::typed::abi::Abi;
use zokrates_ast::typed::types::GTupleType;
use zokrates_ast::typed::{ConcreteSignature, ConcreteType};
use zokrates_bellperson::nova::{self, NovaField};

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("prove")
        .about("Proves a single step of an incremental computation")
        .arg(Arg::with_name("steps")
            .long("steps")
            .help("The number of steps to execute")
            .takes_value(true)
            .default_value("1"),
    )
        .arg(
            Arg::with_name("input")
                .short("i")
                .long("input")
                .help("Path of the binary")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(FLATTENED_CODE_DEFAULT_PATH),
        )
        .arg(
            Arg::with_name("abi-spec")
                .short("s")
                .long("abi-spec")
                .help("Path of the ABI specification")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(cli_constants::ABI_SPEC_DEFAULT_PATH)
        )
        .arg(
            Arg::with_name("arguments")
                .short("a")
                .long("arguments")
                .help("Arguments for the program's main function, when not using ABI encoding. Expects a space-separated list of field elements like `-a 1 2 3`")
                .takes_value(true)
                .multiple(true) // allows multiple values
                .required(false)
                .conflicts_with("abi")
                .conflicts_with("stdin")
        )
        .arg(
            Arg::with_name("proof-path")
                .short("j")
                .long("proof-path")
                .help("Path of the JSON proof file")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(cli_constants::JSON_PROOF_PATH),
        )
        .arg(
            Arg::with_name("abi")
                .long("abi")
                .help("Use ABI encoding. Arguments are expected as a JSON object as specified at zokrates.github.io/toolbox/abi.html#abi-input-format")
                .conflicts_with("arguments")
                .required(false)
        )
        .arg(
            Arg::with_name("stdin")
                .long("stdin")
                .help("Read arguments from stdin")
                .conflicts_with("arguments")
                .required(false)
        )
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    // read compiled program
    let path = Path::new(sub_matches.value_of("input").unwrap());
    let file =
        File::open(&path).map_err(|why| format!("Could not open `{}`: {}", path.display(), why))?;

    let mut reader = BufReader::new(file);

    match ProgEnum::deserialize(&mut reader)? {
        ProgEnum::PallasProgram(p) => cli_nova_prove_step(p, sub_matches),
        ProgEnum::VestaProgram(p) => cli_nova_prove_step(p, sub_matches),
        _ => Err("Nova is only supported for the following curves: [\"pallas\", \"vesta\"]".into()),
    }
}

fn cli_nova_prove_step<'ast, T: NovaField, I: Iterator<Item = ir::Statement<'ast, T>>>(
    program: ir::ProgIterator<'ast, T, I>,
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    let is_stdin = sub_matches.is_present("stdin");
    let is_abi = sub_matches.is_present("abi");
    let steps_count: usize = sub_matches.value_of("steps").unwrap().parse().unwrap();
    let proof_path = Path::new(sub_matches.value_of("proof-path").unwrap());

    let program = program.collect();

    println!("{}", program);

    println!("Generating public parameters");

    let params = nova::generate_public_parameters(program.clone()).map_err(|e| e.to_string())?;

    // get inputs (right now only for the first step but eventually at each step)

    println!("Reading program arguments");

    if !is_stdin && is_abi {
        return Err("ABI input as inline argument is not supported. Please use `--stdin`.".into());
    }

    let signature = match is_abi {
        true => {
            let path = Path::new(sub_matches.value_of("abi-spec").unwrap());
            let file = File::open(&path)
                .map_err(|why| format!("Could not open {}: {}", path.display(), why))?;
            let mut reader = BufReader::new(file);

            let abi: Abi = from_reader(&mut reader).map_err(|why| why.to_string())?;

            abi.signature()
        }
        false => ConcreteSignature::new()
            .inputs(vec![ConcreteType::FieldElement; program.arguments.len()])
            .output(ConcreteType::Tuple(GTupleType::new(
                vec![ConcreteType::FieldElement; program.return_count],
            ))),
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
                .unwrap_or_else(|| Ok(vec![]))
                .map(Inputs::Raw)
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
                            .map(Inputs::Abi)
                            .map_err(|why| why.to_string())
                    }
                    Err(_) => Err(String::from("???")),
                },
                false => match program.arguments.len() {
                    0 => Ok(Inputs::Raw(vec![])),
                    _ => match stdin.read_to_string(&mut input) {
                        Ok(_) => {
                            input.retain(|x| x != '\n');
                            input
                                .split(' ')
                                .map(|x| T::try_from_dec_str(x).map_err(|_| x.to_string()))
                                .collect::<Result<Vec<_>, _>>()
                                .map(Inputs::Raw)
                        }
                        Err(_) => Err(String::from("???")),
                    },
                },
            }
        }
    }
    .map_err(|e| format!("Could not parse argument: {}", e))?;

    let arguments = arguments.encode();

    let step_privates = vec![vec![T::from(1)]];

    let proof = nova::prove(&params, program, arguments.clone(), step_privates)
        .map_err(|e| format!("Error `{:#?}` during proving", e))?;

    let mut proof_file = File::create(proof_path).unwrap();

    let proof_json = serde_json::to_string_pretty(&proof).unwrap();
    proof_file
        .write(proof_json.as_bytes())
        .map_err(|why| format!("Could not write to {}: {}", proof_path.display(), why))?;

    match proof {
        None => println!("No proof to verify"),
        Some(ref proof) => {
            // verify the recursive SNARK
            println!("Verifying the final proof...");

            let res = nova::verify(&params, proof.clone(), steps_count, arguments);

            match res {
                Ok(_) => {
                    println!("Final proof verified succesfully");
                }
                Err(e) => {
                    println!("Error `{:#?}` while verifying the final proof", e);
                }
            }
        }
    }

    Ok(())
}
