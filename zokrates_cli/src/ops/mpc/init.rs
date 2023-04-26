use crate::cli_constants::{FLATTENED_CODE_DEFAULT_PATH, MPC_DEFAULT_PATH};
use clap::{App, Arg, ArgMatches, SubCommand};
use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::path::Path;
use zokrates_ast::ir::{self, ProgEnum};
use zokrates_bellman::Bellman;
use zokrates_field::{BellmanFieldExtensions, Field};
use zokrates_proof_systems::{MpcBackend, MpcScheme, G16};

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("init")
        .about("Initializes a MPC ceremony")
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
            Arg::with_name("radix-path")
                .short("r")
                .long("radix-path")
                .help("Path of the phase1radix2m{n} file")
                .value_name("PATH")
                .takes_value(true)
                .required(true),
        )
        .arg(
            Arg::with_name("output")
                .short("o")
                .long("output")
                .help("Path of the output file")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(MPC_DEFAULT_PATH),
        )
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    // read compiled program
    let path = Path::new(sub_matches.value_of("input").unwrap());
    let file =
        File::open(path).map_err(|why| format!("Could not open `{}`: {}", path.display(), why))?;

    let mut reader = BufReader::new(file);

    match ProgEnum::deserialize(&mut reader)? {
        ProgEnum::Bn128Program(p) => cli_mpc_init::<_, _, G16, Bellman>(p, sub_matches),
        ProgEnum::Bls12_381Program(p) => cli_mpc_init::<_, _, G16, Bellman>(p, sub_matches),
        _ => Err("Current protocol only supports bn128/bls12_381 programs".into()),
    }
}

fn cli_mpc_init<
    'a,
    T: Field + BellmanFieldExtensions,
    I: Iterator<Item = ir::Statement<'a, T>>,
    S: MpcScheme<T>,
    B: MpcBackend<T, S>,
>(
    program: ir::ProgIterator<'a, T, I>,
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    println!("Initializing MPC...");

    let radix_path = Path::new(sub_matches.value_of("radix-path").unwrap());
    let radix_file = File::open(radix_path)
        .map_err(|why| format!("Could not open `{}`: {}", radix_path.display(), why))?;

    let mut radix_reader = BufReader::new(radix_file);

    let output_path = Path::new(sub_matches.value_of("output").unwrap());
    let output_file = File::create(output_path)
        .map_err(|why| format!("Could not create `{}`: {}", output_path.display(), why))?;

    let mut writer = BufWriter::new(output_file);
    B::initialize(program, &mut radix_reader, &mut writer)
        .map_err(|e| format!("Failed to initialize: {}", e))?;

    println!("Parameters written to `{}`", output_path.display());
    Ok(())
}
