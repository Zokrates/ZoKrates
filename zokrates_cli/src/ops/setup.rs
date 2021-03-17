use crate::constants;
use crate::helpers::*;
use clap::{App, Arg, ArgMatches, SubCommand};
use std::convert::TryFrom;
use std::fs::File;
use std::io::{BufReader, Write};
use std::path::Path;
use zokrates_core::ir;
use zokrates_core::ir::ProgEnum;
#[cfg(feature = "ark")]
use zokrates_core::proof_system::ark::Ark;
#[cfg(feature = "bellman")]
use zokrates_core::proof_system::bellman::Bellman;
#[cfg(feature = "libsnark")]
use zokrates_core::proof_system::libsnark::Libsnark;
#[cfg(any(feature = "bellman", feature = "ark", feature = "libsnark"))]
use zokrates_core::proof_system::*;
use zokrates_field::Field;

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
                .default_value(constants::FLATTENED_CODE_DEFAULT_PATH),
        )
        .arg(
            Arg::with_name("proving-key-path")
                .short("p")
                .long("proving-key-path")
                .help("Path of the generated proving key file")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(constants::PROVING_KEY_DEFAULT_PATH),
        )
        .arg(
            Arg::with_name("verification-key-path")
                .short("v")
                .long("verification-key-path")
                .help("Path of the generated verification key file")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(constants::VERIFICATION_KEY_DEFAULT_PATH),
        )
        .arg(
            Arg::with_name("backend")
                .short("b")
                .long("backend")
                .help("Backend to use")
                .takes_value(true)
                .required(false)
                .possible_values(constants::BACKENDS)
                .default_value(constants::BELLMAN),
        )
        .arg(
            Arg::with_name("proving-scheme")
                .short("s")
                .long("proving-scheme")
                .help("Proving scheme to use in the setup")
                .takes_value(true)
                .required(false)
                .possible_values(constants::SCHEMES)
                .default_value(constants::G16),
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
        match prog {
            ProgEnum::Bn128Program(_) => constants::BN128,
            ProgEnum::Bls12_377Program(_) => constants::BLS12_377,
            ProgEnum::Bls12_381Program(_) => constants::BLS12_381,
            ProgEnum::Bw6_761Program(_) => constants::BW6_761,
        },
        sub_matches.value_of("proving-scheme").unwrap(),
    ))?;

    match parameters {
        #[cfg(feature = "bellman")]
        Parameters(BackendParameter::Bellman, _, SchemeParameter::G16) => match prog {
            ProgEnum::Bn128Program(p) => cli_setup::<_, G16, Bellman>(p, sub_matches),
            ProgEnum::Bls12_381Program(p) => cli_setup::<_, G16, Bellman>(p, sub_matches),
            _ => unreachable!(),
        },
        #[cfg(feature = "ark")]
        Parameters(BackendParameter::Ark, _, SchemeParameter::GM17) => match prog {
            ProgEnum::Bls12_377Program(p) => cli_setup::<_, GM17, Ark>(p, sub_matches),
            ProgEnum::Bw6_761Program(p) => cli_setup::<_, GM17, Ark>(p, sub_matches),
            ProgEnum::Bn128Program(p) => cli_setup::<_, GM17, Ark>(p, sub_matches),
            _ => unreachable!(),
        },
        #[cfg(feature = "libsnark")]
        Parameters(BackendParameter::Libsnark, CurveParameter::Bn128, SchemeParameter::GM17) => {
            match prog {
                ProgEnum::Bn128Program(p) => cli_setup::<_, GM17, Libsnark>(p, sub_matches),
                _ => unreachable!(),
            }
        }
        #[cfg(feature = "libsnark")]
        Parameters(BackendParameter::Libsnark, CurveParameter::Bn128, SchemeParameter::PGHR13) => {
            match prog {
                ProgEnum::Bn128Program(p) => cli_setup::<_, PGHR13, Libsnark>(p, sub_matches),
                _ => unreachable!(),
            }
        }
        _ => unreachable!(),
    }
}

fn cli_setup<T: Field, S: Scheme<T>, B: Backend<T, S>>(
    program: ir::Prog<T>,
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    println!("Performing setup...");

    // print deserialized flattened program if in verbose mode
    if sub_matches.is_present("verbose") {
        println!("{}", program);
    }

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
            serde_json::to_string_pretty(&keypair.vk)
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
