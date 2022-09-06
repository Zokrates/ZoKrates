#![feature(panic_info_message)]
#![feature(backtrace)]
//
// @file bin.rs
// @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
// @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
// @date 2017

#[macro_use]
extern crate lazy_static;

mod cli_constants;
mod ops;

use clap::{App, AppSettings, Arg};
use ops::*;

fn main() {
    // set a custom panic hook
    std::panic::set_hook(Box::new(panic_hook));

    env_logger::init();

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
            inspect::subcommand(),
            check::subcommand(),
            compute_witness::subcommand(),
            #[cfg(feature = "ark")]
            universal_setup::subcommand(),
            #[cfg(feature = "bellman")]
            mpc::subcommand(),
            #[cfg(any(feature = "bellman", feature = "ark"))]
            setup::subcommand(),
            export_verifier::subcommand(),
            #[cfg(any(feature = "bellman", feature = "ark"))]
            generate_proof::subcommand(),
            generate_smtlib2::subcommand(),
            print_proof::subcommand(),
            #[cfg(any(feature = "bellman", feature = "ark"))]
            verify::subcommand()])
        .get_matches();

    match matches.subcommand() {
        ("compile", Some(sub_matches)) => compile::exec(sub_matches),
        ("inspect", Some(sub_matches)) => inspect::exec(sub_matches),
        ("check", Some(sub_matches)) => check::exec(sub_matches),
        ("compute-witness", Some(sub_matches)) => compute_witness::exec(sub_matches),
        #[cfg(feature = "ark")]
        ("universal-setup", Some(sub_matches)) => universal_setup::exec(sub_matches),
        #[cfg(feature = "bellman")]
        ("mpc", Some(sub_matches)) => mpc::exec(sub_matches),
        #[cfg(any(feature = "bellman", feature = "ark"))]
        ("setup", Some(sub_matches)) => setup::exec(sub_matches),
        ("export-verifier", Some(sub_matches)) => export_verifier::exec(sub_matches),
        #[cfg(any(feature = "bellman", feature = "ark"))]
        ("generate-proof", Some(sub_matches)) => generate_proof::exec(sub_matches),
        ("generate-smtlib2", Some(sub_matches)) => generate_smtlib2::exec(sub_matches),
        ("print-proof", Some(sub_matches)) => print_proof::exec(sub_matches),
        #[cfg(any(feature = "bellman", feature = "ark"))]
        ("verify", Some(sub_matches)) => verify::exec(sub_matches),
        _ => unreachable!(),
    }
}

fn panic_hook(pi: &std::panic::PanicInfo) {
    let location = pi
        .location()
        .map(|l| format!("({})", l))
        .unwrap_or_default();

    let message = pi
        .message()
        .map(|m| format!("{}", m))
        .or_else(|| pi.payload().downcast_ref::<&str>().map(|p| p.to_string()));

    if let Some(s) = message {
        println!("{} {}", s, location);
    } else {
        println!("The compiler unexpectedly panicked {}", location);
    }

    #[cfg(debug_assertions)]
    {
        use std::backtrace::{Backtrace, BacktraceStatus};
        let backtrace = Backtrace::capture();

        if backtrace.status() == BacktraceStatus::Captured {
            println!("rust backtrace:\n{}", backtrace);
        }
    }

    println!("This is unexpected, please submit a full bug report at https://github.com/Zokrates/ZoKrates/issues");
}

#[cfg(test)]
mod tests {
    extern crate glob;
    use self::glob::glob;

    use std::fs::File;
    use std::io::{BufReader, Read};
    use std::string::String;
    use typed_arena::Arena;
    use zokrates_core::compile::{compile, CompilationArtifacts, CompileConfig};
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

                    let extension = path.extension();

                    // we can ignore scripts (`*.sh˙) and files with no extension
                    if ["", "sh"].contains(
                        &extension
                            .map(|e| e.to_str().unwrap_or_default())
                            .unwrap_or_default(),
                    ) {
                        continue;
                    }

                    println!("Testing {:?}", path);
                    assert_eq!(path.extension().expect("extension expected"), "zok");

                    let should_error = path.to_str().unwrap().contains("compile_errors");

                    let file = File::open(path.clone()).unwrap();

                    let mut reader = BufReader::new(file);

                    let mut source = String::new();
                    reader.read_to_string(&mut source).unwrap();

                    let stdlib = std::fs::canonicalize("../zokrates_stdlib/stdlib").unwrap();
                    let resolver = FileSystemResolver::with_stdlib_root(stdlib.to_str().unwrap());

                    let arena = Arena::new();

                    let res = compile::<Bn128Field, _>(
                        source,
                        path,
                        Some(&resolver),
                        CompileConfig::default(),
                        &arena,
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
            assert_eq!(path.extension().expect("extension expected"), "zok");

            let file = File::open(path.clone()).unwrap();

            let mut reader = BufReader::new(file);
            let mut source = String::new();
            reader.read_to_string(&mut source).unwrap();

            let stdlib = std::fs::canonicalize("../zokrates_stdlib/stdlib").unwrap();
            let resolver = FileSystemResolver::with_stdlib_root(stdlib.to_str().unwrap());

            let arena = Arena::new();

            let artifacts: CompilationArtifacts<Bn128Field, _> = compile(
                source,
                path,
                Some(&resolver),
                CompileConfig::default(),
                &arena,
            )
            .unwrap();

            let interpreter = zokrates_interpreter::Interpreter::default();

            let _ = interpreter
                .execute(artifacts.prog(), &[Bn128Field::from(0)])
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
            assert_eq!(path.extension().expect("extension expected"), "zok");

            let file = File::open(path.clone()).unwrap();

            let mut reader = BufReader::new(file);
            let mut source = String::new();
            reader.read_to_string(&mut source).unwrap();

            let stdlib = std::fs::canonicalize("../zokrates_stdlib/stdlib").unwrap();
            let resolver = FileSystemResolver::with_stdlib_root(stdlib.to_str().unwrap());

            let arena = Arena::new();

            let artifacts: CompilationArtifacts<Bn128Field, _> = compile(
                source,
                path,
                Some(&resolver),
                CompileConfig::default(),
                &arena,
            )
            .unwrap();

            let interpreter = zokrates_interpreter::Interpreter::default();

            let res = interpreter.execute(artifacts.prog(), &[Bn128Field::from(0)]);

            assert!(res.is_err());
        }
    }
}
