use crate::cli_constants;
use clap::{App, Arg, ArgMatches, SubCommand};
use serde_json::from_reader;
use std::fs::File;
use std::io::{stdin, BufReader, BufWriter, Read};
use std::path::Path;
use zokrates_abi::Encode;
use zokrates_ast::ir::{self, ProgEnum};
use zokrates_ast::typed::{
    abi::Abi,
    types::{ConcreteSignature, ConcreteType, GTupleType},
};
use zokrates_circom::write_witness;
use zokrates_field::Field;

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("compute-witness")
        .about("Calculates a witness for a given constraint system")
        .arg(Arg::with_name("input")
            .short("i")
            .long("input")
            .help("Path of the binary")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(cli_constants::FLATTENED_CODE_DEFAULT_PATH)
        ).arg(Arg::with_name("abi-spec")
        .short("s")
        .long("abi-spec")
        .help("Path of the ABI specification")
        .value_name("FILE")
        .takes_value(true)
        .required(false)
        .default_value(cli_constants::ABI_SPEC_DEFAULT_PATH)
    ).arg(Arg::with_name("output")
        .short("o")
        .long("output")
        .help("Path of the output witness file")
        .value_name("FILE")
        .takes_value(true)
        .required(false)
        .default_value(cli_constants::WITNESS_DEFAULT_PATH)
    ).arg(Arg::with_name("circom-witness")
        .long("circom-witness")
        .help("Path of the output circom witness file")
        .value_name("FILE")
        .takes_value(true)
        .required(false)
        .default_value(cli_constants::CIRCOM_WITNESS_DEFAULT_PATH)
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
    )
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    // read compiled program
    let path = Path::new(sub_matches.value_of("input").unwrap());
    let file =
        File::open(&path).map_err(|why| format!("Could not open {}: {}", path.display(), why))?;

    let mut reader = BufReader::new(file);

    match ProgEnum::deserialize(&mut reader)? {
        ProgEnum::Bn128Program(p) => cli_compute(p, sub_matches),
        ProgEnum::Bls12_377Program(p) => cli_compute(p, sub_matches),
        ProgEnum::Bls12_381Program(p) => cli_compute(p, sub_matches),
        ProgEnum::Bw6_761Program(p) => cli_compute(p, sub_matches),
    }
}

fn cli_compute<T: Field, I: Iterator<Item = ir::Statement<T>>>(
    ir_prog: ir::ProgIterator<T, I>,
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    println!("Computing witness...");

    let verbose = sub_matches.is_present("verbose");
    let is_stdin = sub_matches.is_present("stdin");
    let is_abi = sub_matches.is_present("abi");

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
            .inputs(vec![ConcreteType::FieldElement; ir_prog.arguments.len()])
            .output(ConcreteType::Tuple(GTupleType::new(
                vec![ConcreteType::FieldElement; ir_prog.return_count],
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
                false => match ir_prog.arguments.len() {
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

    let interpreter = zokrates_interpreter::Interpreter::default();

    let public_inputs = ir_prog.public_inputs();

    let witness = interpreter
        .execute_with_log_stream(ir_prog, &arguments.encode(), &mut std::io::stdout())
        .map_err(|e| format!("Execution failed: {}", e))?;

    use zokrates_abi::Decode;

    let results_json_value: serde_json::Value =
        zokrates_abi::Value::decode(witness.return_values(), *signature.output).into_serde_json();

    if verbose {
        println!("\nWitness: \n{}\n", results_json_value);
    }

    // write witness to file
    let output_path = Path::new(sub_matches.value_of("output").unwrap());
    let output_file = File::create(&output_path)
        .map_err(|why| format!("Could not create {}: {}", output_path.display(), why))?;

    let writer = BufWriter::new(output_file);

    witness
        .write(writer)
        .map_err(|why| format!("Could not save witness: {:?}", why))?;

    // write circom witness to file
    let wtns_path = Path::new(sub_matches.value_of("circom-witness").unwrap());
    let wtns_file = File::create(&wtns_path)
        .map_err(|why| format!("Could not create {}: {}", output_path.display(), why))?;

    let mut writer = BufWriter::new(wtns_file);

    write_witness(&mut writer, witness, public_inputs)
        .map_err(|why| format!("Could not save circom witness: {:?}", why))?;

    println!("Witness file written to '{}'", output_path.display());
    Ok(())
}
