//
// @file bin.rs
// @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
// @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
// @date 2017

#[macro_use]
extern crate lazy_static;

mod constants;
mod helpers;
mod ops;

use clap::{App, AppSettings, Arg};
use ops::*;

fn main() {
    cli().unwrap_or_else(|e| {
        println!("{}", e);
        std::process::exit(1);
    })
}

fn cli() -> Result<(), String> {
    // cli specification using clap library
    let matches = App::new("ZoKrates")
        .setting(AppSettings::SubcommandRequiredElseHelp)
        .version(env!("CARGO_PKG_VERSION"))
        .author("Jacob Eberhardt, Thibaut Schaeffer, Stefan Deml, Darko Macesic")
        .about("Supports generation of zkSNARKs from high level language code including Smart Contracts for proof verification on the Ethereum Blockchain.\n'I know that I show nothing!'")
        .arg(Arg::with_name("verbose")
            .long("verbose")
            .help("Verbose mode")
            .required(false)
            .global(true)
        )
        .subcommands(vec![
            compile::subcommand(),
            check::subcommand(),
            compute_witness::subcommand(),
            #[cfg(any(feature = "bellman", feature = "ark", feature = "libsnark"))]
            setup::subcommand(),
            export_verifier::subcommand(),
            #[cfg(any(feature = "bellman", feature = "ark", feature = "libsnark"))]
            generate_proof::subcommand(),
            print_proof::subcommand(),
            #[cfg(any(feature = "bellman", feature = "ark", feature = "libsnark"))]
            verify::subcommand()])
        .get_matches();

    match matches.subcommand() {
        ("compile", Some(sub_matches)) => compile::exec(sub_matches)?,
        ("check", Some(sub_matches)) => check::exec(sub_matches)?,
        ("compute-witness", Some(sub_matches)) => compute_witness::exec(sub_matches)?,
        #[cfg(any(feature = "bellman", feature = "ark", feature = "libsnark"))]
        ("setup", Some(sub_matches)) => setup::exec(sub_matches)?,
        ("export-verifier", Some(sub_matches)) => export_verifier::exec(sub_matches)?,
        #[cfg(any(feature = "bellman", feature = "ark", feature = "libsnark"))]
        ("generate-proof", Some(sub_matches)) => generate_proof::exec(sub_matches)?,
        ("print-proof", Some(sub_matches)) => print_proof::exec(sub_matches)?,
        #[cfg(any(feature = "bellman", feature = "ark", feature = "libsnark"))]
        ("verify", Some(sub_matches)) => verify::exec(sub_matches)?,
        _ => unreachable!(),
    };

    Ok(())
}

#[cfg(test)]
mod tests {
    extern crate glob;
    use self::glob::glob;

    use std::fs::File;
    use std::io::{BufReader, Read};
    use std::string::String;
    use zokrates_core::compile::{compile, CompilationArtifacts, CompileConfig};
    use zokrates_core::ir;
    use zokrates_field::Bn128Field;
    use zokrates_fs_resolver::FileSystemResolver;

    #[test]
    fn compile_examples() {
        let builder = std::thread::Builder::new().stack_size(8388608);

        builder
            .spawn(|| {
                for p in glob("./examples/**/*").expect("Failed to read glob pattern") {
                    let path = match p {
                        Ok(x) => x,
                        Err(why) => panic!("Error: {:?}", why),
                    };

                    if !path.is_file() {
                        continue;
                    }

                    assert!(path.extension().expect("extension expected") == "zok");

                    let should_error = path.to_str().unwrap().contains("compile_errors");

                    println!("Testing {:?}", path);

                    let file = File::open(path.clone()).unwrap();

                    let mut reader = BufReader::new(file);

                    let mut source = String::new();
                    reader.read_to_string(&mut source).unwrap();

                    let stdlib = std::fs::canonicalize("../zokrates_stdlib/stdlib").unwrap();
                    let resolver = FileSystemResolver::with_stdlib_root(stdlib.to_str().unwrap());
                    let res = compile::<Bn128Field, _>(
                        source,
                        path,
                        Some(&resolver),
                        &CompileConfig::default(),
                    );
                    assert_eq!(res.is_err(), should_error);
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn execute_examples_ok() {
        //these examples should compile and run
        for p in glob("./examples/test*").expect("Failed to read glob pattern") {
            let path = match p {
                Ok(x) => x,
                Err(why) => panic!("Error: {:?}", why),
            };
            println!("Testing {:?}", path);

            let file = File::open(path.clone()).unwrap();

            let mut reader = BufReader::new(file);
            let mut source = String::new();
            reader.read_to_string(&mut source).unwrap();

            let stdlib = std::fs::canonicalize("../zokrates_stdlib/stdlib").unwrap();
            let resolver = FileSystemResolver::with_stdlib_root(stdlib.to_str().unwrap());

            let artifacts: CompilationArtifacts<Bn128Field> =
                compile(source, path, Some(&resolver), &CompileConfig::default()).unwrap();

            let interpreter = ir::Interpreter::default();

            let _ = interpreter
                .execute(&artifacts.prog(), &[Bn128Field::from(0)])
                .unwrap();
        }
    }

    #[test]
    fn execute_examples_err() {
        //these examples should compile but not run
        for p in glob("./examples/runtime_errors/*").expect("Failed to read glob pattern") {
            let path = match p {
                Ok(x) => x,
                Err(why) => panic!("Error: {:?}", why),
            };
            println!("Testing {:?}", path);

            let file = File::open(path.clone()).unwrap();

            let mut reader = BufReader::new(file);
            let mut source = String::new();
            reader.read_to_string(&mut source).unwrap();

            let stdlib = std::fs::canonicalize("../zokrates_stdlib/stdlib").unwrap();
            let resolver = FileSystemResolver::with_stdlib_root(stdlib.to_str().unwrap());

            let artifacts: CompilationArtifacts<Bn128Field> =
                compile(source, path, Some(&resolver), &CompileConfig::default()).unwrap();

            let interpreter = ir::Interpreter::default();

            let res = interpreter.execute(&artifacts.prog(), &[Bn128Field::from(0)]);

            assert!(res.is_err());
        }
    }
}
