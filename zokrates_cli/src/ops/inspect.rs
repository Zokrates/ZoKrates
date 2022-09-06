use crate::cli_constants::FLATTENED_CODE_DEFAULT_PATH;
use clap::{App, Arg, ArgMatches, SubCommand};
use std::fs::File;
use std::io::{BufReader, BufWriter, Write};
use std::path::{Path, PathBuf};
use zokrates_ast::ir::{self, ProgEnum};
use zokrates_field::Field;

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("inspect")
        .about("Inspects a compiled program")
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
            Arg::with_name("ztf")
                .long("ztf")
                .help("Writes human readable output (ztf) to a file")
                .required(false),
        )
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    // read compiled program
    let path = Path::new(sub_matches.value_of("input").unwrap());
    let file =
        File::open(&path).map_err(|why| format!("Could not open `{}`: {}", path.display(), why))?;

    let mut reader = BufReader::new(file);

    match ProgEnum::deserialize(&mut reader)? {
        ProgEnum::Bn128Program(p) => cli_inspect(p, sub_matches),
        ProgEnum::Bls12_377Program(p) => cli_inspect(p, sub_matches),
        ProgEnum::Bls12_381Program(p) => cli_inspect(p, sub_matches),
        ProgEnum::Bw6_761Program(p) => cli_inspect(p, sub_matches),
    }
}

fn cli_inspect<T: Field, I: Iterator<Item = ir::Statement<T>>>(
    ir_prog: ir::ProgIterator<T, I>,
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    let ir_prog: ir::Prog<T> = ir_prog.collect();

    let curve = format!("{:<17} {}", "curve:", T::name());
    let constraint_count = format!("{:<17} {}", "constraint_count:", ir_prog.constraint_count());

    if sub_matches.is_present("ztf") {
        let output_path =
            PathBuf::from(sub_matches.value_of("input").unwrap()).with_extension("ztf");

        let output_file = File::create(&output_path).unwrap();
        let mut w = BufWriter::new(output_file);

        writeln!(w, "# {}", curve)
            .and(writeln!(w, "# {}", constraint_count))
            .and(write!(w, "{}", ir_prog))
            .map_err(|why| format!("Could not write to `{}`: {}", output_path.display(), why))?;

        w.flush()
            .map_err(|why| format!("Failed to flush the buffer: {}", why))?;

        println!("ztf file written to '{}'", output_path.display());
    }

    Ok(())
}
