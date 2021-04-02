use crate::constants;
use crate::helpers::{CurveParameter, SchemeParameter};
use clap::{App, Arg, ArgMatches, SubCommand};
use std::convert::TryFrom;
use std::fs::File;
use std::io::{BufReader, BufWriter, Write};
use std::path::Path;
use zokrates_core::proof_system::*;
use zokrates_field::Bn128Field;

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("export-verifier")
        .about("Exports a verifier as Solidity smart contract")
        .arg(
            Arg::with_name("input")
                .short("i")
                .long("input")
                .help("Path of the verifier")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(constants::VERIFICATION_KEY_DEFAULT_PATH),
        )
        .arg(
            Arg::with_name("output")
                .short("o")
                .long("output")
                .help("Path of the output file")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(constants::VERIFICATION_CONTRACT_DEFAULT_PATH),
        )
        .arg(
            Arg::with_name("curve")
                .short("c")
                .long("curve")
                .help("Curve to be used to export the verifier")
                .takes_value(true)
                .required(false)
                .possible_values(constants::CURVES)
                .default_value(constants::BN128),
        )
        .arg(
            Arg::with_name("proving-scheme")
                .short("s")
                .long("proving-scheme")
                .help("Proving scheme to use to export the verifier")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .possible_values(constants::SCHEMES)
                .default_value(constants::G16),
        )
        .arg(
            Arg::with_name("solidity-abi")
                .short("a")
                .long("solidity-abi")
                .help("Flag for setting the version of the ABI Encoder used in the contract")
                .takes_value(true)
                .possible_values(&["v1", "v2"])
                .default_value("v1")
                .required(false),
        )
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    let curve = sub_matches.value_of("curve").unwrap();
    let scheme = sub_matches.value_of("proving-scheme").unwrap();

    let curve_parameter = CurveParameter::try_from(curve)?;
    let scheme_parameter = SchemeParameter::try_from(scheme)?;

    match (curve_parameter, scheme_parameter) {
        (CurveParameter::Bn128, SchemeParameter::G16) => {
            cli_export_verifier::<Bn128Field, G16>(sub_matches)
        }
        (CurveParameter::Bn128, SchemeParameter::GM17) => {
            cli_export_verifier::<Bn128Field, GM17>(sub_matches)
        }
        (CurveParameter::Bn128, SchemeParameter::PGHR13) => {
            cli_export_verifier::<Bn128Field, PGHR13>(sub_matches)
        }
        _ => Err(format!("Could not export verifier with given parameters (curve: {}, scheme: {}): not supported", curve, scheme))
    }
}

fn cli_export_verifier<T: SolidityCompatibleField, S: SolidityCompatibleScheme<T>>(
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    println!("Exporting verifier...");

    // read vk file
    let input_path = Path::new(sub_matches.value_of("input").unwrap());
    let input_file = File::open(&input_path)
        .map_err(|why| format!("Could not open {}: {}", input_path.display(), why))?;
    let reader = BufReader::new(input_file);

    let vk = serde_json::from_reader(reader)
        .map_err(|why| format!("Could not deserialize verification key: {}", why))?;

    let abi = SolidityAbi::from(sub_matches.value_of("solidity-abi").unwrap())?;

    let verifier = S::export_solidity_verifier(vk, abi);

    //write output file
    let output_path = Path::new(sub_matches.value_of("output").unwrap());
    let output_file = File::create(&output_path)
        .map_err(|why| format!("Could not create {}: {}", output_path.display(), why))?;

    let mut writer = BufWriter::new(output_file);

    writer
        .write_all(&verifier.as_bytes())
        .map_err(|_| "Failed writing output to file".to_string())?;

    println!("Verifier exported to '{}'", output_path.display());
    Ok(())
}
