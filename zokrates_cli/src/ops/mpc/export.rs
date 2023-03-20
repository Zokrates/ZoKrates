use crate::cli_constants;
use clap::{App, Arg, ArgMatches, SubCommand};
use std::fs::File;
use std::io::{BufReader, Write};
use std::path::Path;
use zokrates_bellman::Bellman;
use zokrates_common::constants::{BLS12_381, BN128};
use zokrates_field::{BellmanFieldExtensions, Bls12_381Field, Bn128Field, Field};
use zokrates_proof_systems::{MpcBackend, MpcScheme, TaggedVerificationKey, G16};

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("export")
        .about("Exports keys from MPC parameters")
        .arg(
            Arg::with_name("input")
                .short("i")
                .long("input")
                .help("Path of the MPC parameters")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(cli_constants::MPC_DEFAULT_PATH),
        )
        .arg(
            Arg::with_name("curve")
                .short("c")
                .long("curve")
                .help("Curve used in the ceremony")
                .takes_value(true)
                .required(false)
                .possible_values(&[BN128, BLS12_381])
                .default_value(BN128),
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
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    match sub_matches.value_of("curve").unwrap() {
        BN128 => cli_mpc_export::<Bn128Field, G16, Bellman>(sub_matches),
        BLS12_381 => cli_mpc_export::<Bls12_381Field, G16, Bellman>(sub_matches),
        _ => unreachable!(),
    }
}

pub fn cli_mpc_export<T: Field + BellmanFieldExtensions, S: MpcScheme<T>, B: MpcBackend<T, S>>(
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    let path = Path::new(sub_matches.value_of("input").unwrap());
    let file =
        File::open(path).map_err(|why| format!("Could not open `{}`: {}", path.display(), why))?;

    let mut reader = BufReader::new(file);

    println!("Exporting keys from `{}`...", path.display());

    let keypair =
        B::export_keypair(&mut reader).map_err(|e| format!("Could not export keypair: {}", e))?;

    let pk_path = Path::new(sub_matches.value_of("proving-key-path").unwrap());
    let vk_path = Path::new(sub_matches.value_of("verification-key-path").unwrap());

    // write verification key
    let mut vk_file = File::create(vk_path)
        .map_err(|why| format!("Could not create `{}`: {}", vk_path.display(), why))?;
    vk_file
        .write_all(
            serde_json::to_string_pretty(&TaggedVerificationKey::<T, S>::new(keypair.vk))
                .unwrap()
                .as_bytes(),
        )
        .map_err(|why| format!("Could not write to `{}`: {}", vk_path.display(), why))?;

    println!("Verification key written to `{}`", vk_path.display());

    // write proving key
    let mut pk_file = File::create(pk_path)
        .map_err(|why| format!("Could not create `{}`: {}", pk_path.display(), why))?;
    pk_file
        .write_all(keypair.pk.as_ref())
        .map_err(|why| format!("Could not write to `{}`: {}", pk_path.display(), why))?;

    println!("Proving key written to `{}`", pk_path.display());

    Ok(())
}
