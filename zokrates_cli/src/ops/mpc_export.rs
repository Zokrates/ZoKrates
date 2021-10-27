use crate::constants::{MPC_DEFAULT_PATH, PROVING_KEY_DEFAULT_PATH, VERIFICATION_KEY_DEFAULT_PATH};
use clap::{App, Arg, ArgMatches, SubCommand};
use phase2::parameters::MPCParameters;
use std::fs::File;
use std::io::{BufReader, Write};
use std::path::Path;
use zokrates_core::proof_system::bellman::{parse_g1, parse_g2};
use zokrates_core::proof_system::groth16::VerificationKey;
use zokrates_field::Bn128Field;

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("mpc-export")
        .about("Export keys from MPC parameters")
        .arg(
            Arg::with_name("input")
                .short("i")
                .long("input")
                .help("Path of the MPC params")
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
    cli_mpc_export(sub_matches)
}

fn cli_mpc_export(sub_matches: &ArgMatches) -> Result<(), String> {
    println!("Exporting keypair...");

    let path = Path::new(sub_matches.value_of("input").unwrap());
    let file =
        File::open(&path).map_err(|why| format!("Could not open {}: {}", path.display(), why))?;

    let reader = BufReader::new(file);
    let mpc_params = MPCParameters::read(reader, true)
        .map_err(|why| format!("Could not read {}: {}", path.display(), why))?;

    let params = mpc_params.get_params();

    let mut pk: Vec<u8> = Vec::new();
    params.write(&mut pk).unwrap();

    let vk = VerificationKey {
        alpha: parse_g1::<Bn128Field>(&params.vk.alpha_g1),
        beta: parse_g2::<Bn128Field>(&params.vk.beta_g2),
        gamma: parse_g2::<Bn128Field>(&params.vk.gamma_g2),
        delta: parse_g2::<Bn128Field>(&params.vk.delta_g2),
        gamma_abc: params
            .vk
            .ic
            .iter()
            .map(|g1| parse_g1::<Bn128Field>(g1))
            .collect(),
    };

    let pk_path = Path::new(sub_matches.value_of("proving-key-path").unwrap());
    let vk_path = Path::new(sub_matches.value_of("verification-key-path").unwrap());

    // write verification key
    let mut vk_file = File::create(vk_path)
        .map_err(|why| format!("Could not create {}: {}", vk_path.display(), why))?;
    vk_file
        .write_all(serde_json::to_string_pretty(&vk).unwrap().as_bytes())
        .map_err(|why| format!("Could not write to {}: {}", vk_path.display(), why))?;

    println!("Verification key written to {}", vk_path.display());

    // write proving key
    let mut pk_file = File::create(pk_path)
        .map_err(|why| format!("Could not create {}: {}", pk_path.display(), why))?;
    pk_file
        .write_all(pk.as_ref())
        .map_err(|why| format!("Could not write to {}: {}", pk_path.display(), why))?;

    println!("Proving key written to {}", pk_path.display());
    println!("Trusted setup completed");

    Ok(())
}
