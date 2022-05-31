use crate::cli_constants;
use clap::{App, Arg, ArgMatches, SubCommand};
use std::convert::TryFrom;
use std::fs::File;
use std::io::{BufReader, Write};
use std::path::Path;
#[cfg(feature = "ark")]
use zokrates_ark::Ark;
use zokrates_ast::ir::{self, ProgEnum};
#[cfg(feature = "bellman")]
use zokrates_bellman::Bellman;
use zokrates_common::constants;
use zokrates_common::helpers::*;
use zokrates_field::Field;
#[cfg(any(feature = "bellman", feature = "ark"))]
use zokrates_proof_systems::*;

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("setup")
        .about("Performs a trusted setup for a given constraint system")
        .arg(
            Arg::with_name("input")
                .short("i")
                .long("input")
                .help("Path of the binary")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(cli_constants::FLATTENED_CODE_DEFAULT_PATH),
        )
        .arg(
            Arg::with_name("proving-key-path")
                .short("p")
                .long("proving-key-path")
                .help("Path of the generated proving key file")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(cli_constants::PROVING_KEY_DEFAULT_PATH),
        )
        .arg(
            Arg::with_name("verification-key-path")
                .short("v")
                .long("verification-key-path")
                .help("Path of the generated verification key file")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(cli_constants::VERIFICATION_KEY_DEFAULT_PATH),
        )
        .arg(
            Arg::with_name("backend")
                .short("b")
                .long("backend")
                .help("Backend to use")
                .takes_value(true)
                .required(false)
                .possible_values(cli_constants::BACKENDS)
                .default_value(constants::BELLMAN),
        )
        .arg(
            Arg::with_name("proving-scheme")
                .short("s")
                .long("proving-scheme")
                .help("Proving scheme to use in the setup")
                .takes_value(true)
                .required(false)
                .possible_values(cli_constants::SCHEMES)
                .default_value(constants::G16),
        )
        .arg(
            Arg::with_name("universal-setup-path")
                .short("u")
                .long("universal-setup-path")
                .help("Path of the universal setup file for universal schemes")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(cli_constants::UNIVERSAL_SETUP_DEFAULT_PATH),
        )
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    // read compiled program
    let path = Path::new(sub_matches.value_of("input").unwrap());
    let file =
        File::open(&path).map_err(|why| format!("Couldn't open {}: {}", path.display(), why))?;

    let mut reader = BufReader::new(file);
    let prog = ProgEnum::deserialize(&mut reader)?;

    let parameters = Parameters::try_from((
        sub_matches.value_of("backend").unwrap(),
        prog.curve(),
        sub_matches.value_of("proving-scheme").unwrap(),
    ))?;

    match parameters {
        #[cfg(feature = "bellman")]
        Parameters(BackendParameter::Bellman, _, SchemeParameter::G16) => match prog {
            ProgEnum::Bn128Program(p) => {
                cli_setup_non_universal::<_, _, G16, Bellman>(p, sub_matches)
            }
            ProgEnum::Bls12_381Program(p) => {
                cli_setup_non_universal::<_, _, G16, Bellman>(p, sub_matches)
            }
            _ => unreachable!(),
        },
        #[cfg(feature = "ark")]
        Parameters(BackendParameter::Ark, _, SchemeParameter::G16) => match prog {
            ProgEnum::Bn128Program(p) => cli_setup_non_universal::<_, _, G16, Ark>(p, sub_matches),
            ProgEnum::Bls12_381Program(p) => {
                cli_setup_non_universal::<_, _, G16, Ark>(p, sub_matches)
            }
            ProgEnum::Bls12_377Program(p) => {
                cli_setup_non_universal::<_, _, G16, Ark>(p, sub_matches)
            }
            ProgEnum::Bw6_761Program(p) => {
                cli_setup_non_universal::<_, _, G16, Ark>(p, sub_matches)
            }
        },
        #[cfg(feature = "ark")]
        Parameters(BackendParameter::Ark, _, SchemeParameter::GM17) => match prog {
            ProgEnum::Bn128Program(p) => cli_setup_non_universal::<_, _, GM17, Ark>(p, sub_matches),
            ProgEnum::Bls12_381Program(p) => {
                cli_setup_non_universal::<_, _, GM17, Ark>(p, sub_matches)
            }
            ProgEnum::Bls12_377Program(p) => {
                cli_setup_non_universal::<_, _, GM17, Ark>(p, sub_matches)
            }
            ProgEnum::Bw6_761Program(p) => {
                cli_setup_non_universal::<_, _, GM17, Ark>(p, sub_matches)
            }
        },
        #[cfg(feature = "ark")]
        Parameters(BackendParameter::Ark, _, SchemeParameter::MARLIN) => {
            let setup_path = Path::new(sub_matches.value_of("universal-setup-path").unwrap());
            let setup_file = File::open(&setup_path)
                .map_err(|why| format!("Couldn't open {}: {}\nExpected an universal setup, make sure `zokrates universal-setup` was run`", setup_path.display(), why))?;

            let mut reader = BufReader::new(setup_file);

            let mut setup = vec![];
            use std::io::Read;

            reader
                .read_to_end(&mut setup)
                .map_err(|_| "Cannot read universal setup".to_string())?;

            match prog {
                ProgEnum::Bn128Program(p) => {
                    cli_setup_universal::<_, _, Marlin, Ark>(p, setup, sub_matches)
                }
                ProgEnum::Bls12_381Program(p) => {
                    cli_setup_universal::<_, _, Marlin, Ark>(p, setup, sub_matches)
                }
                ProgEnum::Bls12_377Program(p) => {
                    cli_setup_universal::<_, _, Marlin, Ark>(p, setup, sub_matches)
                }
                ProgEnum::Bw6_761Program(p) => {
                    cli_setup_universal::<_, _, Marlin, Ark>(p, setup, sub_matches)
                }
            }
        }
        _ => unreachable!(),
    }
}

fn cli_setup_non_universal<
    T: Field,
    I: Iterator<Item = ir::Statement<T>>,
    S: NonUniversalScheme<T>,
    B: NonUniversalBackend<T, S>,
>(
    program: ir::ProgIterator<T, I>,
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    println!("Performing setup...");

    // get paths for proving and verification keys
    let pk_path = Path::new(sub_matches.value_of("proving-key-path").unwrap());
    let vk_path = Path::new(sub_matches.value_of("verification-key-path").unwrap());

    // run setup phase
    let keypair = B::setup(program);

    // write verification key
    let mut vk_file = File::create(vk_path)
        .map_err(|why| format!("Could not create {}: {}", vk_path.display(), why))?;
    vk_file
        .write_all(
            serde_json::to_string_pretty(&TaggedVerificationKey::<T, S>::new(keypair.vk))
                .unwrap()
                .as_bytes(),
        )
        .map_err(|why| format!("Could not write to {}: {}", vk_path.display(), why))?;

    println!("Verification key written to '{}'", vk_path.display());

    // write proving key
    let mut pk_file = File::create(pk_path)
        .map_err(|why| format!("Could not create {}: {}", pk_path.display(), why))?;
    pk_file
        .write_all(keypair.pk.as_ref())
        .map_err(|why| format!("Could not write to {}: {}", pk_path.display(), why))?;

    println!("Proving key written to '{}'", pk_path.display());
    println!("Setup completed");

    Ok(())
}

fn cli_setup_universal<
    T: Field,
    I: Iterator<Item = ir::Statement<T>>,
    S: UniversalScheme<T>,
    B: UniversalBackend<T, S>,
>(
    program: ir::ProgIterator<T, I>,
    srs: Vec<u8>,
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    println!("Performing setup...");

    // get paths for proving and verification keys
    let pk_path = Path::new(sub_matches.value_of("proving-key-path").unwrap());
    let vk_path = Path::new(sub_matches.value_of("verification-key-path").unwrap());

    // run setup phase
    let keypair = B::setup(srs, program)?;

    // write verification key
    let mut vk_file = File::create(vk_path)
        .map_err(|why| format!("Could not create {}: {}", vk_path.display(), why))?;
    vk_file
        .write_all(
            serde_json::to_string_pretty(&TaggedVerificationKey::<T, S>::new(keypair.vk))
                .unwrap()
                .as_bytes(),
        )
        .map_err(|why| format!("Could not write to {}: {}", vk_path.display(), why))?;

    println!("Verification key written to '{}'", vk_path.display());

    // write proving key
    let mut pk_file = File::create(pk_path)
        .map_err(|why| format!("Could not create {}: {}", pk_path.display(), why))?;
    pk_file
        .write_all(keypair.pk.as_ref())
        .map_err(|why| format!("Could not write to {}: {}", pk_path.display(), why))?;

    println!("Proving key written to '{}'", pk_path.display());
    println!("Setup completed");

    Ok(())
}
