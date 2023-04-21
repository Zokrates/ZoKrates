use crate::cli_constants::{self, NOVA_PUBLIC_INIT};
use clap::{App, Arg, ArgMatches, SubCommand};
use serde_json::from_reader;
use std::fs::File;
use std::io::BufReader;
use std::path::Path;
use zokrates_abi::{parse_value, Encode};

use zokrates_ast::typed::abi::Abi;
use zokrates_bellperson::nova::{
    self, CompressedSNARK, NovaField, RecursiveSNARKWithStepCount, VerifierKey,
};
use zokrates_field::PallasField;

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("verify")
        .about("Verifies a Nova compressed proof")
        .arg(
            Arg::with_name("init")
                .long("init")
                .help("Path to the initial value of the public input")
                .takes_value(true)
                .default_value(NOVA_PUBLIC_INIT),
        )
        .arg(
            Arg::with_name("proof-path")
                .short("j")
                .long("proof-path")
                .help("Path of the JSON compressed proof path")
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
        .arg(
            Arg::with_name("instance-path")
                .long("instance-path")
                .help("Path of the JSON running instance file")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(cli_constants::JSON_NOVA_RUNNING_INSTANCE),
        )
        .arg(
            Arg::with_name("abi-spec")
                .short("s")
                .long("abi-spec")
                .help("Path of the ABI specification")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(cli_constants::ABI_SPEC_DEFAULT_PATH),
        )
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    let proof_path = sub_matches.value_of("proof-path").unwrap();

    let proof_file =
        File::open(proof_path).map_err(|why| format!("Could not open {}: {}", proof_path, why))?;

    let proof_reader = BufReader::new(proof_file);

    let verification_key_path = sub_matches.value_of("verification-key-path").unwrap();

    let verification_key_file = File::open(verification_key_path)
        .map_err(|why| format!("Could not open {}: {}", verification_key_path, why))?;

    let verification_key_reader = BufReader::new(verification_key_file);

    let proof: CompressedSNARK<PallasField> = serde_json::from_reader(proof_reader).unwrap();
    let vk: VerifierKey<PallasField> = serde_json::from_reader(verification_key_reader).unwrap();

    cli_nova_verify(proof, vk, sub_matches)
}

fn cli_nova_verify<'ast, T: NovaField>(
    proof: CompressedSNARK<'ast, T>,
    vk: VerifierKey<'ast, T>,
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    let path = Path::new(sub_matches.value_of("abi-spec").unwrap());
    let file =
        File::open(path).map_err(|why| format!("Could not open {}: {}", path.display(), why))?;

    let mut reader = BufReader::new(file);

    let abi: Abi = from_reader(&mut reader).map_err(|why| why.to_string())?;
    let signature = abi.signature();

    let init_type = signature.inputs[0].clone();

    let init = {
        let path = Path::new(sub_matches.value_of("init").unwrap());
        let file = File::open(path).unwrap();
        let reader = BufReader::new(file);

        parse_value(serde_json::from_reader(reader).unwrap(), init_type)
            .unwrap()
            .encode()
    };

    let instance_path = Path::new(sub_matches.value_of("instance-path").unwrap());
    let instance: RecursiveSNARKWithStepCount<'ast, T> =
        serde_json::from_reader(BufReader::new(File::open(instance_path).unwrap())).unwrap();
    let steps = instance.steps;

    if nova::verify_compressed(&proof, &vk, init, steps) {
        println!("Compressed proof succesfully verified");
    } else {
        eprintln!("Compressed proof verification failed");
    }

    Ok(())
}
