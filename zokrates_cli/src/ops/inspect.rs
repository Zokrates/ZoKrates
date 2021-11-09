use crate::constants::FLATTENED_CODE_DEFAULT_PATH;
use clap::{App, Arg, ArgMatches, SubCommand};
use fallible_iterator::FallibleIterator;
use std::fs::File;
use std::io::{BufReader, Write};
use std::path::{Path, PathBuf};
use zokrates_core::ir;
use zokrates_core::ir::ProgEnum;
use zokrates_field::Field;

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("inspect")
        .about("Outputs a compiled program to a file in a human readable format")
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
        File::open(&path).map_err(|why| format!("Could not open {}: {}", path.display(), why))?;

    let mut reader = BufReader::new(file);

    match ProgEnum::deserialize(&mut reader)? {
        ProgEnum::Bn128Program(p) => cli_inspect(p, sub_matches),
        ProgEnum::Bls12_377Program(p) => cli_inspect(p, sub_matches),
        ProgEnum::Bls12_381Program(p) => cli_inspect(p, sub_matches),
        ProgEnum::Bw6_761Program(p) => cli_inspect(p, sub_matches),
    }
}

fn cli_inspect<T: Field, I: FallibleIterator<Item = ir::Statement<T>, Error = ()>>(
    ir_prog: ir::ProgIterator<T, I>,
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    let output_path = PathBuf::from(sub_matches.value_of("input").unwrap()).with_extension("ztf");
    let mut output_file = File::create(&output_path).unwrap();

    println!("collect!");

    let ir_prog: ir::Prog<T> = ir_prog.collect().unwrap();

    println!("done collecting!");

    output_file
        .write(format!("{}", ir_prog).as_bytes())
        .map_err(|why| format!("Could not save ztf: {:?}", why))?;

    println!("ztf file written to '{}'", output_path.display());
    Ok(())
}
