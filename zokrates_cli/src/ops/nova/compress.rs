use crate::cli_constants::{self, JSON_NOVA_RUNNING_INSTANCE};
use clap::{App, Arg, ArgMatches, SubCommand};

use zokrates_field::PallasField;

use std::io::BufReader;
use std::path::Path;
use std::{fs::File, io::Write};

use zokrates_bellperson::nova::{self, NovaField, RecursiveSNARKWithStepCount};

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("compress")
        .about("Compresses an instance to a Spartan SNARK")
        .arg(
            Arg::with_name("input")
                .long("i")
                .help("Path to the running instance")
                .takes_value(true)
                .default_value(JSON_NOVA_RUNNING_INSTANCE),
        )
        .arg(
            Arg::with_name("params-path")
                .short("p")
                .long("params-path")
                .help("Path of the nova public parameters")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(cli_constants::NOVA_PARAMS_DEFAULT_PATH),
        )
        .arg(
            Arg::with_name("proof-path")
                .short("j")
                .long("proof-path")
                .help("Path of the JSON proof file")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(cli_constants::JSON_PROOF_PATH),
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
    let path = Path::new(sub_matches.value_of("input").unwrap());
    let file =
        File::open(path).map_err(|why| format!("Could not open {}: {}", path.display(), why))?;

    let reader = BufReader::new(file);
    let instance: RecursiveSNARKWithStepCount<PallasField> =
        serde_json::from_reader(reader).unwrap();

    cli_nova_compress::<PallasField>(instance, sub_matches)
}

fn cli_nova_compress<T: NovaField>(
    instance: RecursiveSNARKWithStepCount<T>,
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    let params_path = Path::new(sub_matches.value_of("params-path").unwrap());
    let params_file = File::open(params_path)
        .map_err(|why| format!("Could not open {}: {}", params_path.display(), why))?;

    let params_reader = BufReader::new(params_file);
    let params = serde_cbor::from_reader(params_reader)
        .map_err(|why| format!("Could not deserialize {}: {}", params_path.display(), why))?;

    let proof_path = Path::new(sub_matches.value_of("proof-path").unwrap());
    let verification_key_path = Path::new(sub_matches.value_of("verification-key-path").unwrap());

    let (proof, vk) = nova::compress(&params, instance);

    let proof_json = serde_json::to_string_pretty(&proof).unwrap();

    let mut proof_file = File::create(proof_path)
        .map_err(|why| format!("Could not create {}: {}", proof_path.display(), why))?;

    proof_file
        .write(proof_json.as_bytes())
        .map_err(|why| format!("Could not write to {}: {}", proof_path.display(), why))?;

    println!("Compressed SNARK written to '{}'", proof_path.display());

    let verification_key_json = serde_json::to_string_pretty(&vk).unwrap();

    let mut verification_key_file = File::create(verification_key_path).map_err(|why| {
        format!(
            "Could not create {}: {}",
            verification_key_path.display(),
            why
        )
    })?;

    verification_key_file
        .write(verification_key_json.as_bytes())
        .map_err(|why| {
            format!(
                "Could not write to {}: {}",
                verification_key_path.display(),
                why
            )
        })?;

    println!(
        "Verification key written to '{}'",
        verification_key_path.display()
    );

    Ok(())
}
