use crate::constants::{FLATTENED_CODE_DEFAULT_PATH, MPC_DEFAULT_PATH};
use clap::{App, Arg, ArgMatches, SubCommand};
use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::path::Path;
use zokrates_core::ir;
use zokrates_core::ir::ProgEnum;
use zokrates_core::proof_system::bellman::Computation;
use zokrates_field::Bn128Field;

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("init")
        .about("Initialize MPC phase 2 ceremony")
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
            Arg::with_name("radix-dir")
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
        _ => unimplemented!(),
    }
}

fn cli_mpc_init(ir_prog: ir::Prog<Bn128Field>, sub_matches: &ArgMatches) -> Result<(), String> {
    println!("Initializing MPC...");

    let radix_dir = Path::new(sub_matches.value_of("radix-dir").unwrap());
    let circuit = Computation::without_witness(ir_prog);
    let params = phase2::parameters::MPCParameters::new(
        circuit,
        true,
        &radix_dir
            .to_path_buf()
            .into_os_string()
            .into_string()
            .unwrap(),
    )
    .unwrap();

    let output_path = Path::new(sub_matches.value_of("output").unwrap());
    let output_file = File::create(&output_path)
        .map_err(|why| format!("Could not create `{}`: {}", output_path.display(), why))?;

    println!("Writing initial parameters to `{}`", output_path.display());

    let mut writer = BufWriter::new(output_file);
    params.write(&mut writer).map_err(|e| e.to_string())?;

    Ok(())
}
