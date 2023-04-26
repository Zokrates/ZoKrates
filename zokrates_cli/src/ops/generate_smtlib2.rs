use crate::cli_constants::{FLATTENED_CODE_DEFAULT_PATH, SMTLIB2_DEFAULT_PATH};
use clap::{App, Arg, ArgMatches, SubCommand};
use std::fs::File;
use std::io::{BufReader, Write};
use std::path::Path;
use zokrates_ast::ir::{self, smtlib2::SMTLib2Display, ProgEnum};
use zokrates_field::Field;

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("generate-smtlib2")
        .about("Outputs the constraint system in the SMTLib2 format")
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
                .help("Path of the output file")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(SMTLIB2_DEFAULT_PATH),
        )
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    // read compiled program
    let path = Path::new(sub_matches.value_of("input").unwrap());
    let file =
        File::open(path).map_err(|why| format!("Could not open {}: {}", path.display(), why))?;

    let mut reader = BufReader::new(file);

    match ProgEnum::deserialize(&mut reader)? {
        ProgEnum::Bn128Program(p) => cli_smtlib2(p, sub_matches),
        ProgEnum::Bls12_377Program(p) => cli_smtlib2(p, sub_matches),
        ProgEnum::Bls12_381Program(p) => cli_smtlib2(p, sub_matches),
        ProgEnum::Bw6_761Program(p) => cli_smtlib2(p, sub_matches),
        ProgEnum::PallasProgram(p) => cli_smtlib2(p, sub_matches),
        ProgEnum::VestaProgram(p) => cli_smtlib2(p, sub_matches),
    }
}

fn cli_smtlib2<'a, T: Field, I: Iterator<Item = ir::Statement<'a, T>>>(
    ir_prog: ir::ProgIterator<'a, T, I>,
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    println!("Generating SMTLib2...");

    let output_path = Path::new(sub_matches.value_of("output").unwrap());
    let mut output_file = File::create(output_path).unwrap();

    let ir_prog = ir_prog.collect();

    output_file
        .write(format!("{}", SMTLib2Display(&ir_prog)).as_bytes())
        .map_err(|why| format!("Could not save smtlib2: {:?}", why))?;

    println!("SMTLib2 file written to '{}'", output_path.display());
    Ok(())
}
