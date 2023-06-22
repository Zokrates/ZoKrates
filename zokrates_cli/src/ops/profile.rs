use crate::cli_constants::FLATTENED_CODE_DEFAULT_PATH;
use clap::{App, Arg, ArgMatches, SubCommand};
use std::fs::File;
use std::io::BufReader;
use std::path::Path;
use zokrates_ast::ir::{self, ProgEnum};
use zokrates_field::Field;
use zokrates_profiler::profile;

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("profile")
        .about("Profiles a compiled program, indicating which parts of the source yield the most constraints")
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
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    // read compiled program
    let path = Path::new(sub_matches.value_of("input").unwrap());
    let file =
        File::open(path).map_err(|why| format!("Could not open `{}`: {}", path.display(), why))?;

    let mut reader = BufReader::new(file);

    match ProgEnum::deserialize(&mut reader)? {
        ProgEnum::Bn128Program(p) => cli_profile(p, sub_matches),
        ProgEnum::Bls12_377Program(p) => cli_profile(p, sub_matches),
        ProgEnum::Bls12_381Program(p) => cli_profile(p, sub_matches),
        ProgEnum::Bw6_761Program(p) => cli_profile(p, sub_matches),
        ProgEnum::PallasProgram(p) => cli_profile(p, sub_matches),
        ProgEnum::VestaProgram(p) => cli_profile(p, sub_matches),
    }
}

fn cli_profile<'ast, T: Field, I: Iterator<Item = ir::Statement<'ast, T>>>(
    ir_prog: ir::ProgIterator<'ast, T, I>,
    _: &ArgMatches,
) -> Result<(), String> {
    let module_map = ir_prog.module_map.clone();

    let heat_map = profile(ir_prog);

    println!("{}", heat_map.display(&module_map));

    Ok(())
}
