use crate::cli_constants::{FLATTENED_CODE_DEFAULT_PATH, NOVA_PARAMS_DEFAULT_PATH};
use clap::{App, Arg, ArgMatches, SubCommand};
use std::fs::File;
use std::io::BufReader;
use std::path::Path;
use zokrates_ast::ir::{self, ProgEnum};
use zokrates_bellperson::nova::{self, NovaField};

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("setup")
        .about("Performs a nova setup for a given constraint system")
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
            Arg::with_name("output")
                .short("o")
                .long("output")
                .help("Path of the generated public parameters")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(NOVA_PARAMS_DEFAULT_PATH),
        )
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    // read compiled program
    let path = Path::new(sub_matches.value_of("input").unwrap());
    let file =
        File::open(path).map_err(|why| format!("Could not open {}: {}", path.display(), why))?;

    let mut reader = BufReader::new(file);

    match ProgEnum::deserialize(&mut reader)? {
        ProgEnum::PallasProgram(p) => cli_nova_setup(p, sub_matches),
        ProgEnum::VestaProgram(p) => cli_nova_setup(p, sub_matches),
        _ => Err("Nova is only supported for the following curves: [\"pallas\", \"vesta\"]".into()),
    }
}

fn cli_nova_setup<'ast, T: NovaField, I: Iterator<Item = ir::Statement<'ast, T>>>(
    program: ir::ProgIterator<'ast, T, I>,
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    println!("Generating public parameters...");

    let program = program.collect();
    let params_path = Path::new(sub_matches.value_of("output").unwrap());

    let params_file = File::create(params_path)
        .map_err(|why| format!("Could not create {}: {}", params_path.display(), why))?;

    let params = nova::generate_public_parameters(&program).map_err(|e| e.to_string())?;

    // write public parameters
    serde_cbor::to_writer(params_file, &params)
        .map_err(|why| format!("Could not write to {}: {}", params_path.display(), why))?;

    println!("Public parameters written to '{}'", params_path.display());

    Ok(())
}
