use crate::constants::{FLATTENED_CODE_DEFAULT_PATH, MPC_DEFAULT_PATH};
use clap::{App, Arg, ArgMatches, SubCommand};
use phase2::MPCParameters;
use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::path::Path;
use zokrates_core::ir;
use zokrates_core::ir::ProgEnum;
use zokrates_core::proof_system::bellman::Computation;
use zokrates_field::{BellmanFieldExtensions, Field};

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
                .long("radix-dir")
                .help("Path of the directory containing parameters for various 2^m circuit depths (phase1radix2m{0..=m})")
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
        File::open(&path).map_err(|why| format!("Could not open `{}`: {}", path.display(), why))?;

    let mut reader = BufReader::new(file);

    match ProgEnum::deserialize(&mut reader)? {
        ProgEnum::Bn128Program(p) => cli_mpc_init(p, sub_matches),
        ProgEnum::Bls12_381Program(p) => cli_mpc_init(p, sub_matches),
        _ => Err("Current protocol only supports bn128/bls12_381 programs".into()),
    }
}

fn cli_mpc_init<T: Field + BellmanFieldExtensions>(
    ir_prog: ir::Prog<T>,
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    println!("Initializing MPC...");

    let radix_path = Path::new(sub_matches.value_of("radix-path").unwrap());
    let radix_file = File::open(radix_path)
        .map_err(|why| format!("Could not open `{}`: {}", radix_path.display(), why))?;

    let mut radix_reader = BufReader::with_capacity(1024 * 1024, radix_file);

    let circuit = Computation::without_witness(ir_prog);
    let params = MPCParameters::new(circuit, &mut radix_reader).unwrap();

    let output_path = Path::new(sub_matches.value_of("output").unwrap());
    let output_file = File::create(&output_path)
        .map_err(|why| format!("Could not create `{}`: {}", output_path.display(), why))?;

    println!("Writing initial parameters to `{}`", output_path.display());

    let mut writer = BufWriter::new(output_file);
    params.write(&mut writer).map_err(|e| e.to_string())?;

    Ok(())
}
