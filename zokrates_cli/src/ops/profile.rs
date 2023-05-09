use crate::cli_constants::FLATTENED_CODE_DEFAULT_PATH;
use clap::{App, Arg, ArgMatches, SubCommand};
use std::fs::File;
use std::io::BufReader;
use std::path::Path;
use zokrates_ast::ir::{self, ProgHeader, ProgIterator};
use zokrates_field::*;
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

    let header = ProgHeader::read(&mut reader).map_err(|e| e.to_string())?;

    match header.curve_id {
        #[cfg(feature = "bn128")]
        name if name == Bn128Field::id() => {
            cli_profile::<Bn128Field, _>(ProgIterator::read(reader, &header), sub_matches)
        }
        #[cfg(feature = "bls12_377")]
        name if name == Bls12_377Field::id() => {
            cli_profile::<Bls12_377Field, _>(ProgIterator::read(reader, &header), sub_matches)
        }
        #[cfg(feature = "bls12_381")]
        name if name == Bls12_381Field::id() => {
            cli_profile::<Bls12_381Field, _>(ProgIterator::read(reader, &header), sub_matches)
        }
        #[cfg(feature = "bw6_761")]
        name if name == Bw6_761Field::id() => {
            cli_profile::<Bw6_761Field, _>(ProgIterator::read(reader, &header), sub_matches)
        }
        #[cfg(feature = "pallas")]
        name if name == PallasField::id() => {
            cli_profile::<PallasField, _>(ProgIterator::read(reader, &header), sub_matches)
        }
        #[cfg(feature = "vesta")]
        name if name == VestaField::id() => {
            cli_profile::<VestaField, _>(ProgIterator::read(reader, &header), sub_matches)
        }
        _ => unreachable!(),
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
