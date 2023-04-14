use crate::cli_constants::{FLATTENED_CODE_DEFAULT_PATH, MPC_DEFAULT_PATH};
use clap::{App, Arg, ArgMatches, SubCommand};
use std::fs::File;
use std::io::BufReader;
use std::path::Path;
use zokrates_ast::ir::{self, ProgEnum};
use zokrates_bellman::Bellman;
use zokrates_field::{BellmanFieldExtensions, Field};
use zokrates_proof_systems::{MpcBackend, MpcScheme, G16};

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("verify")
        .about("Verifies correctness of MPC parameters, given a circuit instance")
        .arg(
            Arg::with_name("input")
                .short("i")
                .long("input")
                .help("Path of the MPC parameters")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(MPC_DEFAULT_PATH),
        )
        .arg(
            Arg::with_name("circuit")
                .short("c")
                .long("circuit")
                .help("Path of the circuit binary")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(FLATTENED_CODE_DEFAULT_PATH),
        )
        .arg(
            Arg::with_name("radix-path")
                .short("r")
                .long("radix-dir")
                .help("Path to the radix file containing parameters for a circuit depth of 2^n (phase1radix2m{n})")
                .value_name("PATH")
                .takes_value(true)
                .required(true),
        )
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    // read compiled program
    let path = Path::new(sub_matches.value_of("circuit").unwrap());
    let file =
        File::open(path).map_err(|why| format!("Could not open `{}`: {}", path.display(), why))?;

    let mut reader = BufReader::new(file);

    match ProgEnum::deserialize(&mut reader)? {
        ProgEnum::Bn128Program(p) => cli_mpc_verify::<_, _, G16, Bellman>(p, sub_matches),
        ProgEnum::Bls12_381Program(p) => cli_mpc_verify::<_, _, G16, Bellman>(p, sub_matches),
        _ => Err("Current protocol only supports bn128/bls12_381 programs".into()),
    }
}

fn cli_mpc_verify<
    'a,
    T: Field + BellmanFieldExtensions,
    I: Iterator<Item = ir::Statement<'a, T>>,
    S: MpcScheme<T>,
    B: MpcBackend<T, S>,
>(
    program: ir::ProgIterator<'a, T, I>,
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    println!("Verifying contributions...");

    let path = Path::new(sub_matches.value_of("input").unwrap());
    let file =
        File::open(path).map_err(|why| format!("Could not open `{}`: {}", path.display(), why))?;

    let reader = BufReader::new(file);

    let radix_path = Path::new(sub_matches.value_of("radix-path").unwrap());
    let radix_file = File::open(radix_path)
        .map_err(|why| format!("Could not open `{}`: {}", radix_path.display(), why))?;

    let mut radix_reader = BufReader::new(radix_file);

    let result = B::verify(reader, program, &mut radix_reader)
        .map_err(|e| format!("Verification failed: {}", e))?;

    let contribution_count = result.len();
    println!(
        "\nTranscript contains {} contribution{}:",
        contribution_count,
        if contribution_count != 1 { "s" } else { "" }
    );

    for (i, hash) in result.iter().enumerate() {
        print!("{}: ", i);
        for b in hash.iter() {
            print!("{:02x}", b);
        }
        println!();
    }

    println!("\nContributions verified");
    Ok(())
}
