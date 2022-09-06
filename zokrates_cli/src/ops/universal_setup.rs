use crate::cli_constants;
use clap::{App, Arg, ArgMatches, SubCommand};
use std::convert::TryFrom;
use std::fs::File;
use std::io::Write;
use std::path::Path;
#[cfg(feature = "ark")]
use zokrates_ark::Ark;
use zokrates_common::constants;
use zokrates_common::helpers::*;
use zokrates_field::{Bls12_377Field, Bls12_381Field, Bn128Field, Bw6_761Field, Field};
#[cfg(any(feature = "bellman", feature = "ark"))]
use zokrates_proof_systems::*;

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("universal-setup")
        .about("Performs the universal phase of a trusted setup")
        .arg(
            Arg::with_name("curve")
                .short("c")
                .long("curve")
                .help("Curve to be used in the universal setup")
                .takes_value(true)
                .required(false)
                .possible_values(cli_constants::CURVES)
                .default_value(constants::BN128),
        )
        .arg(
            Arg::with_name("universal-setup-path")
                .short("u")
                .long("universal-setup-path")
                .help("Path of the generated universal setup file")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(cli_constants::UNIVERSAL_SETUP_DEFAULT_PATH),
        )
        .arg(
            Arg::with_name("proving-scheme")
                .short("s")
                .long("proving-scheme")
                .help("Proving scheme to use in the setup")
                .takes_value(true)
                .required(false)
                .possible_values(cli_constants::UNIVERSAL_SCHEMES)
                .default_value(constants::MARLIN),
        )
        .arg(
            Arg::with_name("size")
                .short("n")
                .long("size")
                .help("Size of the trusted setup passed as an exponent. For example, 8 for 2**8")
                .takes_value(true)
                .required(false)
                .default_value(cli_constants::UNIVERSAL_SETUP_DEFAULT_SIZE),
        )
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    let parameters = Parameters::try_from((
        constants::ARK,
        sub_matches.value_of("curve").unwrap(),
        sub_matches.value_of("proving-scheme").unwrap(),
    ))?;

    match parameters {
        #[cfg(feature = "ark")]
        Parameters(BackendParameter::Ark, CurveParameter::Bn128, SchemeParameter::MARLIN) => {
            cli_universal_setup::<Bn128Field, Marlin, Ark>(sub_matches)
        }
        #[cfg(feature = "ark")]
        Parameters(BackendParameter::Ark, CurveParameter::Bls12_381, SchemeParameter::MARLIN) => {
            cli_universal_setup::<Bls12_381Field, Marlin, Ark>(sub_matches)
        }
        #[cfg(feature = "ark")]
        Parameters(BackendParameter::Ark, CurveParameter::Bls12_377, SchemeParameter::MARLIN) => {
            cli_universal_setup::<Bls12_377Field, Marlin, Ark>(sub_matches)
        }
        #[cfg(feature = "ark")]
        Parameters(BackendParameter::Ark, CurveParameter::Bw6_761, SchemeParameter::MARLIN) => {
            cli_universal_setup::<Bw6_761Field, Marlin, Ark>(sub_matches)
        }
        _ => unreachable!(),
    }
}

fn cli_universal_setup<T: Field, S: UniversalScheme<T>, B: UniversalBackend<T, S>>(
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    println!("Performing setup...");

    // get paths for the universal setup
    let u_path = Path::new(sub_matches.value_of("universal-setup-path").unwrap());

    // get the size of the setup
    let size = sub_matches.value_of("size").unwrap();
    let size = size
        .parse::<u32>()
        .map_err(|_| format!("Universal setup size {} is invalid", size))?;

    // run universal setup phase
    let setup = B::universal_setup(size);

    // write proving key
    let mut u_file = File::create(u_path)
        .map_err(|why| format!("Could not create {}: {}", u_path.display(), why))?;
    u_file
        .write_all(setup.as_ref())
        .map_err(|why| format!("Could not write to {}: {}", u_path.display(), why))?;

    println!("Universal setup written to '{}'", u_path.display());
    println!("Universal setup completed");

    Ok(())
}
