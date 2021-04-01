use crate::constants;
use crate::helpers::CurveParameter;
use clap::{App, Arg, ArgMatches, SubCommand};
use std::convert::TryFrom;
use std::fs::File;
use std::io::{BufReader, Read};
use std::path::{Path, PathBuf};
use zokrates_core::compile::{check, CompileError};
use zokrates_field::{Bls12_377Field, Bls12_381Field, Bn128Field, Bw6_761Field, Field};
use zokrates_fs_resolver::FileSystemResolver;

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("check")
        .about("Checks a program for errors")
        .arg(
            Arg::with_name("input")
                .short("i")
                .long("input")
                .help("Path of the source code")
                .value_name("FILE")
                .takes_value(true)
                .required(true),
        )
        .arg(
            Arg::with_name("stdlib-path")
                .long("stdlib-path")
                .help("Path to the standard library")
                .value_name("PATH")
                .takes_value(true)
                .required(false)
                .env("ZOKRATES_STDLIB")
                .default_value(constants::DEFAULT_STDLIB_PATH.as_str()),
        )
        .arg(
            Arg::with_name("curve")
                .short("c")
                .long("curve")
                .help("Curve to be used in the compilation")
                .takes_value(true)
                .required(false)
                .possible_values(constants::CURVES)
                .default_value(constants::BN128),
        )
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    let curve = CurveParameter::try_from(sub_matches.value_of("curve").unwrap())?;
    match curve {
        CurveParameter::Bn128 => cli_check::<Bn128Field>(sub_matches),
        CurveParameter::Bls12_377 => cli_check::<Bls12_377Field>(sub_matches),
        CurveParameter::Bls12_381 => cli_check::<Bls12_381Field>(sub_matches),
        CurveParameter::Bw6_761 => cli_check::<Bw6_761Field>(sub_matches),
    }
}

fn cli_check<T: Field>(sub_matches: &ArgMatches) -> Result<(), String> {
    println!("Checking {}\n", sub_matches.value_of("input").unwrap());
    let path = PathBuf::from(sub_matches.value_of("input").unwrap());

    let file = File::open(path.clone())
        .map_err(|why| format!("Could not open {}: {}", path.display(), why))?;

    let mut reader = BufReader::new(file);
    let mut source = String::new();
    reader.read_to_string(&mut source).unwrap();

    let fmt_error = |e: &CompileError| {
        let file = e.file().canonicalize().unwrap();
        format!(
            "{}:{}",
            file.strip_prefix(std::env::current_dir().unwrap())
                .unwrap_or_else(|_| file.as_path())
                .display(),
            e.value()
        )
    };

    let stdlib_path = sub_matches.value_of("stdlib-path").unwrap();
    match Path::new(stdlib_path).exists() {
        true => Ok(()),
        _ => Err(format!(
            "Invalid standard library source path: {}",
            stdlib_path
        )),
    }?;

    let resolver = FileSystemResolver::with_stdlib_root(stdlib_path);
    let _ = check::<T, _>(source, path, Some(&resolver)).map_err(|e| {
        format!(
            "Check failed:\n\n{}",
            e.0.iter()
                .map(|e| fmt_error(e))
                .collect::<Vec<_>>()
                .join("\n\n")
        )
    })?;

    println!("Program checked, no errors found.");

    Ok(())
}
