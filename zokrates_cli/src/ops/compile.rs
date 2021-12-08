use crate::constants;
use crate::helpers::CurveParameter;
use clap::{App, Arg, ArgMatches, SubCommand};
use serde_json::to_writer_pretty;
use std::convert::TryFrom;
use std::fs::File;
use std::io::{BufReader, BufWriter, Read};
use std::path::{Path, PathBuf};
use typed_arena::Arena;
use zokrates_core::compile::{compile, CompileConfig, CompileError};
use zokrates_field::{Bls12_377Field, Bls12_381Field, Bn128Field, Bw6_761Field, Field};
use zokrates_fs_resolver::FileSystemResolver;

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("compile")
        .about("Compiles into a runnable constraint system")
        .arg(Arg::with_name("input")
            .short("i")
            .long("input")
            .help("Path of the source code")
            .value_name("FILE")
            .takes_value(true)
            .required(true)
        ).arg(Arg::with_name("stdlib-path")
        .long("stdlib-path")
        .help("Path to the standard library")
        .value_name("PATH")
        .takes_value(true)
        .required(false)
        .env("ZOKRATES_STDLIB")
        .default_value(constants::DEFAULT_STDLIB_PATH.as_str())
    ).arg(Arg::with_name("abi-spec")
        .short("s")
        .long("abi-spec")
        .help("Path of the ABI specification")
        .value_name("FILE")
        .takes_value(true)
        .required(false)
        .default_value(constants::ABI_SPEC_DEFAULT_PATH)
    ).arg(Arg::with_name("output")
        .short("o")
        .long("output")
        .help("Path of the output binary")
        .value_name("FILE")
        .takes_value(true)
        .required(false)
        .default_value(constants::FLATTENED_CODE_DEFAULT_PATH)
    ).arg(Arg::with_name("curve")
        .short("c")
        .long("curve")
        .help("Curve to be used in the compilation")
        .takes_value(true)
        .required(false)
        .possible_values(constants::CURVES)
        .default_value(constants::BN128)
    ).arg(Arg::with_name("isolate-branches")
        .long("isolate-branches")
        .help("Isolate the execution of branches: a panic in a branch only makes the program panic if this branch is being logically executed")
        .required(false)
    )
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    let curve = CurveParameter::try_from(sub_matches.value_of("curve").unwrap())?;
    match curve {
        CurveParameter::Bn128 => cli_compile::<Bn128Field>(sub_matches),
        CurveParameter::Bls12_377 => cli_compile::<Bls12_377Field>(sub_matches),
        CurveParameter::Bls12_381 => cli_compile::<Bls12_381Field>(sub_matches),
        CurveParameter::Bw6_761 => cli_compile::<Bw6_761Field>(sub_matches),
    }
}

fn cli_compile<T: Field>(sub_matches: &ArgMatches) -> Result<(), String> {
    println!("Compiling {}\n", sub_matches.value_of("input").unwrap());
    let path = PathBuf::from(sub_matches.value_of("input").unwrap());
    let bin_output_path = Path::new(sub_matches.value_of("output").unwrap());
    let abi_spec_path = Path::new(sub_matches.value_of("abi-spec").unwrap());

    log::debug!("Load entry point file {}", path.display());

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

    let config =
        CompileConfig::default().isolate_branches(sub_matches.is_present("isolate-branches"));

    let resolver = FileSystemResolver::with_stdlib_root(stdlib_path);

    log::debug!("Compile");

    let arena = Arena::new();

    let artifacts =
        compile::<T, _>(source, path, Some(&resolver), config, &arena).map_err(|e| {
            format!(
                "Compilation failed:\n\n{}",
                e.0.iter()
                    .map(|e| fmt_error(e))
                    .collect::<Vec<_>>()
                    .join("\n\n")
            )
        })?;

    let (program_flattened, abi) = artifacts.into_inner();

    // serialize flattened program and write to binary file
    log::debug!("Serialize program");
    let bin_output_file = File::create(&bin_output_path)
        .map_err(|why| format!("Could not create {}: {}", bin_output_path.display(), why))?;

    let mut writer = BufWriter::new(bin_output_file);

    match program_flattened.serialize(&mut writer) {
        Ok(_) => {
            // serialize ABI spec and write to JSON file
            log::debug!("Serialize ABI");
            let abi_spec_file = File::create(&abi_spec_path)
                .map_err(|why| format!("Could not create {}: {}", abi_spec_path.display(), why))?;

            let mut writer = BufWriter::new(abi_spec_file);
            to_writer_pretty(&mut writer, &abi)
                .map_err(|_| "Unable to write data to file.".to_string())?;

            println!("Compiled code written to '{}'", bin_output_path.display());
            Ok(())
        }
        Err(e) => {
            // something wrong happened, clean up
            std::fs::remove_file(bin_output_path).unwrap();
            Err(e.to_string())
        }
    }
}
