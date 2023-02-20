use crate::cli_constants::{
    self, FLATTENED_CODE_DEFAULT_PATH, NOVA_PUBLIC_INIT, NOVA_STEPS_PRIVATE_INPUTS,
};
use clap::{App, Arg, ArgMatches, SubCommand};
use serde_json::{from_reader, Value};
use std::fs::File;
use std::io::{BufReader, Write};
use std::path::Path;
use zokrates_abi::{parse_value, Encode, Values};
use zokrates_ast::ir::{self, ProgEnum};
use zokrates_ast::typed::abi::Abi;
use zokrates_bellperson::nova::{self, NovaField};

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("prove")
        .about("Proves a many steps of an incremental computation")
        .arg(
            Arg::with_name("init")
                .long("init")
                .help("Path to the initial value of the public input")
                .takes_value(true)
                .default_value(NOVA_PUBLIC_INIT),
        )
        .arg(
            Arg::with_name("steps")
                .long("steps")
                .help("Path to the value of the private input for each step")
                .takes_value(true)
                .default_value(NOVA_STEPS_PRIVATE_INPUTS),
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
                .default_value(cli_constants::ABI_SPEC_DEFAULT_PATH),
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
    let proof_path = Path::new(sub_matches.value_of("proof-path").unwrap());

    let program = program.collect();

    let path = Path::new(sub_matches.value_of("abi-spec").unwrap());
    let file =
        File::open(&path).map_err(|why| format!("Could not open {}: {}", path.display(), why))?;
    let mut reader = BufReader::new(file);

    let abi: Abi = from_reader(&mut reader).map_err(|why| why.to_string())?;

    let signature = abi.signature();

    let init_type = signature.inputs[0].clone();
    let step_type = signature.inputs[1].clone();

    let init = {
        let path = Path::new(sub_matches.value_of("init").unwrap());
        let file = File::open(path).unwrap();
        let reader = BufReader::new(file);

        parse_value(serde_json::from_reader(reader).unwrap(), init_type)
            .unwrap()
            .encode()
    };

    let steps: Vec<_> = {
        let path = Path::new(sub_matches.value_of("steps").unwrap());
        let json_str = std::fs::read_to_string(path).unwrap();

        {
            let values: Value = serde_json::from_str(&json_str).map_err(|e| e.to_string())?;

            match values {
                Value::Array(values) => Ok(Values(
                    values
                        .into_iter()
                        .map(|v| parse_value(v, step_type.clone()))
                        .collect::<Result<_, _>>()
                        .map_err(|e| e.to_string())?,
                )),
                _ => Err(format!("Expected an array of values, found `{}`", values)),
            }
        }
        .unwrap()
        .0
        .into_iter()
        .map(|e| e.encode())
        .collect()
    };

    let step_count = steps.len();

    let params = nova::generate_public_parameters(program.clone()).map_err(|e| e.to_string())?;

    let proof = nova::prove(&params, program, init.clone(), steps)
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

            let res = nova::verify(&params, proof.clone(), step_count, init);

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
