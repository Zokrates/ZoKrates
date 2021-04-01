use crate::constants;
use crate::helpers::CurveParameter;
use clap::{App, Arg, ArgMatches, SubCommand};
use serde_json::to_writer_pretty;
use std::convert::TryFrom;
use std::fs::File;
use std::io::{BufReader, BufWriter, Read, Write};
use std::path::{Path, PathBuf};
use zokrates_core::compile::{compile, CompilationArtifacts, CompileConfig, CompileError};
use zokrates_field::{Bls12_377Field, Bls12_381Field, Bn128Field, Bw6_761Field, Field};
use zokrates_fs_resolver::FileSystemResolver;

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("compile")
        .about("Compiles into flattened conditions. Produces two files: human-readable '.ztf' file for debugging and binary file")
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
    ).arg(Arg::with_name("allow-unconstrained-variables")
        .long("allow-unconstrained-variables")
        .help("Allow unconstrained variables by inserting dummy constraints")
        .required(false)
    ).arg(Arg::with_name("ztf")
        .long("ztf")
        .help("Write human readable output (ztf)")
        .required(false)
    )
    .arg(Arg::with_name("light") // TODO: deprecated, should be removed
        .long("light")
        .required(false)
        .overrides_with_all(&["ztf", "verbose"])
        .hidden(true)
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
    // TODO: remove the warning once light flag is removed entirely
    if sub_matches.is_present("light") {
        println!(
            "Warning: the --light flag is deprecated and will be removed in a coming release.\n\
            Terminal output is now off by default and can be activated with the --verbose flag.\n\
            Human-readable output file (ztf) is now off by default and can be activated with the --ztf flag.\n"
        )
    }

    println!("Compiling {}\n", sub_matches.value_of("input").unwrap());
    let path = PathBuf::from(sub_matches.value_of("input").unwrap());
    let bin_output_path = Path::new(sub_matches.value_of("output").unwrap());
    let abi_spec_path = Path::new(sub_matches.value_of("abi-spec").unwrap());
    let hr_output_path = bin_output_path.to_path_buf().with_extension("ztf");

    let file = File::open(path.clone())
        .map_err(|why| format!("Could not open {}: {}", path.display(), why))?;

    let mut reader = BufReader::new(file);
    let mut source = String::new();
    reader.read_to_string(&mut source).unwrap();

    let fmt_error = |e: &CompileError| {
        let file = e.file().canonicalize().unwrap();
        format!(
            "{}: {}",
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

    let config = CompileConfig {
        allow_unconstrained_variables: sub_matches.is_present("allow-unconstrained-variables"),
    };

    let resolver = FileSystemResolver::with_stdlib_root(stdlib_path);
    let artifacts: CompilationArtifacts<T> = compile(source, path, Some(&resolver), &config)
        .map_err(|e| {
            format!(
                "Compilation failed:\n\n{}",
                e.0.iter()
                    .map(|e| fmt_error(e))
                    .collect::<Vec<_>>()
                    .join("\n\n")
            )
        })?;

    let program_flattened = artifacts.prog();

    // number of constraints the flattened program will translate to.
    let num_constraints = program_flattened.constraint_count();

    // serialize flattened program and write to binary file
    let bin_output_file = File::create(&bin_output_path)
        .map_err(|why| format!("Could not create {}: {}", bin_output_path.display(), why))?;

    let mut writer = BufWriter::new(bin_output_file);

    program_flattened.serialize(&mut writer);

    // serialize ABI spec and write to JSON file
    let abi_spec_file = File::create(&abi_spec_path)
        .map_err(|why| format!("Could not create {}: {}", abi_spec_path.display(), why))?;

    let abi = artifacts.abi();

    let mut writer = BufWriter::new(abi_spec_file);
    to_writer_pretty(&mut writer, &abi).map_err(|_| "Unable to write data to file.".to_string())?;

    if sub_matches.is_present("verbose") {
        // debugging output
        println!("Compiled program:\n{}", program_flattened);
    }

    println!("Compiled code written to '{}'", bin_output_path.display());

    if sub_matches.is_present("ztf") {
        // write human-readable output file
        let hr_output_file = File::create(&hr_output_path)
            .map_err(|why| format!("Could not create {}: {}", hr_output_path.display(), why))?;

        let mut hrofb = BufWriter::new(hr_output_file);
        writeln!(&mut hrofb, "{}", program_flattened)
            .map_err(|_| "Unable to write data to file".to_string())?;
        hrofb
            .flush()
            .map_err(|_| "Unable to flush buffer".to_string())?;

        println!("Human readable code to '{}'", hr_output_path.display());
    }

    println!("Number of constraints: {}", num_constraints);
    Ok(())
}
