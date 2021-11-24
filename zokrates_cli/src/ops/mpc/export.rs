use crate::constants::{MPC_DEFAULT_PATH, PROVING_KEY_DEFAULT_PATH, VERIFICATION_KEY_DEFAULT_PATH};
use clap::{App, Arg, ArgMatches, SubCommand};
use std::fs::File;
use std::io::{BufReader, Write};
use std::path::Path;
use zokrates_core::proof_system::bellman::groth16::serialization::parameters_to_verification_key;
use zokrates_field::{BellmanFieldExtensions, Bn128Field};
use zokrates_mpc::groth16::parameters::MPCParameters;

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
                .default_value(MPC_DEFAULT_PATH),
        )
        .arg(
            Arg::with_name("proving-key-path")
                .short("p")
                .long("proving-key-path")
                .help("Path of the generated proving key file")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(PROVING_KEY_DEFAULT_PATH),
        )
        .arg(
            Arg::with_name("verification-key-path")
                .short("v")
                .long("verification-key-path")
                .help("Path of the generated verification key file")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(VERIFICATION_KEY_DEFAULT_PATH),
        )
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    let path = Path::new(sub_matches.value_of("input").unwrap());
    let file =
        File::open(&path).map_err(|why| format!("Could not open `{}`: {}", path.display(), why))?;

    let reader = BufReader::new(file);
    let mpc_params =
        MPCParameters::<<Bn128Field as BellmanFieldExtensions>::BellmanEngine>::read(reader, true)
            .map_err(|why| format!("Could not read `{}`: {}", path.display(), why))?;

    println!("Exporting keys from `{}`...", path.display());

    let params = mpc_params.get_params();

    let mut pk: Vec<u8> = Vec::new();
    params.write(&mut pk).unwrap();

    let vk = parameters_to_verification_key::<Bn128Field>(params);

    let pk_path = Path::new(sub_matches.value_of("proving-key-path").unwrap());
    let vk_path = Path::new(sub_matches.value_of("verification-key-path").unwrap());

    // write verification key
    let mut vk_file = File::create(vk_path)
        .map_err(|why| format!("Could not create `{}`: {}", vk_path.display(), why))?;
    vk_file
        .write_all(serde_json::to_string_pretty(&vk).unwrap().as_bytes())
        .map_err(|why| format!("Could not write to `{}`: {}", vk_path.display(), why))?;

    println!("Verification key written to `{}`", vk_path.display());

    // write proving key
    let mut pk_file = File::create(pk_path)
        .map_err(|why| format!("Could not create `{}`: {}", pk_path.display(), why))?;
    pk_file
        .write_all(pk.as_ref())
        .map_err(|why| format!("Could not write to `{}`: {}", pk_path.display(), why))?;

    println!("Proving key written to `{}`", pk_path.display());

    Ok(())
}