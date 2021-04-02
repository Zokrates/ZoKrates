use crate::constants;
use crate::helpers::*;
use clap::{App, Arg, ArgMatches, SubCommand};
use std::convert::TryFrom;
use std::fs::File;
use std::io::BufReader;
use std::path::Path;
#[cfg(feature = "ark")]
use zokrates_core::proof_system::ark::Ark;
#[cfg(feature = "bellman")]
use zokrates_core::proof_system::bellman::Bellman;
#[cfg(feature = "libsnark")]
use zokrates_core::proof_system::libsnark::Libsnark;
#[cfg(any(feature = "bellman", feature = "ark", feature = "libsnark"))]
use zokrates_core::proof_system::*;
use zokrates_field::{Bls12_377Field, Bls12_381Field, Bn128Field, Bw6_761Field, Field};

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("verify")
        .about("Verifies a given proof with the given verification key")
        .arg(Arg::with_name("proof-path")
            .short("j")
            .long("proof-path")
            .help("Path of the JSON proof file")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(constants::JSON_PROOF_PATH)
        ).arg(Arg::with_name("verification-key-path")
        .short("v")
        .long("verification-key-path")
        .help("Path of the generated verification key file")
        .value_name("FILE")
        .takes_value(true)
        .required(false)
        .default_value(constants::VERIFICATION_KEY_DEFAULT_PATH)
    ).arg(Arg::with_name("backend")
        .short("b")
        .long("backend")
        .help("Backend to use")
        .takes_value(true)
        .required(false)
        .possible_values(constants::BACKENDS)
        .default_value(constants::BELLMAN)
    ).arg(Arg::with_name("proving-scheme")
        .short("s")
        .long("proving-scheme")
        .help("Proving scheme to use in the setup. Available options are G16 (default), PGHR13 and GM17")
        .value_name("FILE")
        .takes_value(true)
        .required(false)
        .default_value(constants::G16)
    ).arg(Arg::with_name("curve")
        .short("c")
        .long("curve")
        .help("Curve to be used in the verification")
        .takes_value(true)
        .required(false)
        .possible_values(constants::CURVES)
        .default_value(constants::BN128)
    )
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    let parameters = Parameters::try_from((
        sub_matches.value_of("backend").unwrap(),
        sub_matches.value_of("curve").unwrap(),
        sub_matches.value_of("proving-scheme").unwrap(),
    ))?;

    match parameters {
        #[cfg(feature = "bellman")]
        Parameters(BackendParameter::Bellman, CurveParameter::Bn128, SchemeParameter::G16) => {
            cli_verify::<Bn128Field, G16, Bellman>(sub_matches)
        }
        #[cfg(feature = "bellman")]
        Parameters(BackendParameter::Bellman, CurveParameter::Bls12_381, SchemeParameter::G16) => {
            cli_verify::<Bls12_381Field, G16, Bellman>(sub_matches)
        }
        #[cfg(feature = "ark")]
        Parameters(BackendParameter::Ark, CurveParameter::Bls12_377, SchemeParameter::GM17) => {
            cli_verify::<Bls12_377Field, GM17, Ark>(sub_matches)
        }
        #[cfg(feature = "ark")]
        Parameters(BackendParameter::Ark, CurveParameter::Bw6_761, SchemeParameter::GM17) => {
            cli_verify::<Bw6_761Field, GM17, Ark>(sub_matches)
        }
        #[cfg(feature = "ark")]
        Parameters(BackendParameter::Ark, CurveParameter::Bn128, SchemeParameter::GM17) => {
            cli_verify::<Bn128Field, GM17, Ark>(sub_matches)
        }
        #[cfg(feature = "libsnark")]
        Parameters(BackendParameter::Libsnark, CurveParameter::Bn128, SchemeParameter::GM17) => {
            cli_verify::<Bn128Field, GM17, Libsnark>(sub_matches)
        }
        #[cfg(feature = "libsnark")]
        Parameters(BackendParameter::Libsnark, CurveParameter::Bn128, SchemeParameter::PGHR13) => {
            cli_verify::<Bn128Field, PGHR13, Libsnark>(sub_matches)
        }
        _ => unreachable!(),
    }
}

fn cli_verify<T: Field, S: Scheme<T>, B: Backend<T, S>>(
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    let vk_path = Path::new(sub_matches.value_of("verification-key-path").unwrap());
    let vk_file = File::open(&vk_path)
        .map_err(|why| format!("Could not open {}: {}", vk_path.display(), why))?;

    let vk_reader = BufReader::new(vk_file);
    let vk = serde_json::from_reader(vk_reader)
        .map_err(|why| format!("Could not deserialize verification key: {}", why))?;

    let proof_path = Path::new(sub_matches.value_of("proof-path").unwrap());
    let proof_file = File::open(&proof_path)
        .map_err(|why| format!("Could not open {}: {}", proof_path.display(), why))?;

    let proof_reader = BufReader::new(proof_file);
    let proof = serde_json::from_reader(proof_reader)
        .map_err(|why| format!("Could not deserialize proof: {}", why))?;

    println!("Performing verification...");
    println!(
        "{}",
        match B::verify(vk, proof) {
            true => "PASSED",
            false => "FAILED",
        }
    );

    Ok(())
}
