use crate::cli_constants;
use clap::{App, Arg, ArgMatches, SubCommand};
use std::convert::TryFrom;
use std::fs::File;
use std::io::{BufReader, BufWriter, Write};
use std::path::Path;
use zokrates_bellman::plonk_proving_scheme::Plonk;
use zokrates_common::helpers::{CurveParameter, SchemeParameter};
use zokrates_field::Bn128Field;
use zokrates_proof_systems::*;

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("export-verifier")
        .about("Exports a verifier as Solidity smart contract")
        .arg(
            Arg::with_name("input")
                .short("i")
                .long("input")
                .help("Path of the verification key")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(cli_constants::VERIFICATION_KEY_DEFAULT_PATH),
        )
        .arg(
            Arg::with_name("output")
                .short("o")
                .long("output")
                .help("Path of the output file")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(cli_constants::VERIFICATION_CONTRACT_DEFAULT_PATH),
        )
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    let vk_path = Path::new(sub_matches.value_of("input").unwrap());
    let vk_file = File::open(&vk_path)
        .map_err(|why| format!("Could not open {}: {}", vk_path.display(), why))?;

    // deserialize vk to JSON
    let vk_reader = BufReader::new(vk_file);
    let vk: serde_json::Value = serde_json::from_reader(vk_reader)
        .map_err(|why| format!("Could not deserialize verification key: {}", why))?;

    // extract curve and scheme parameters
    let vk_curve = vk
        .get("curve")
        .ok_or_else(|| "Field `curve` not found in verification key".to_string())?
        .as_str()
        .ok_or_else(|| "`curve` should be a string".to_string())?;
    let vk_scheme = vk
        .get("scheme")
        .ok_or_else(|| "Field `scheme` not found in verification key".to_string())?
        .as_str()
        .ok_or_else(|| "`scheme` should be a string".to_string())?;

    let curve_parameter = CurveParameter::try_from(vk_curve)?;
    let scheme_parameter = SchemeParameter::try_from(vk_scheme)?;

    match (curve_parameter, scheme_parameter) {
        (CurveParameter::Bn128, SchemeParameter::G16) => {
            cli_export_verifier::<Bn128Field, G16>(sub_matches, vk)
        }
        (CurveParameter::Bn128, SchemeParameter::GM17) => {
            cli_export_verifier::<Bn128Field, GM17>(sub_matches, vk)
        }
        (CurveParameter::Bn128, SchemeParameter::MARLIN) => {
            cli_export_verifier::<Bn128Field, Marlin>(sub_matches, vk)
        }
        (CurveParameter::Bn128, SchemeParameter::PLONK) => {
            cli_export_verifier::<Bn128Field, Plonk>(sub_matches, vk)
        }
        (curve_parameter, scheme_parameter) => Err(format!("Could not export verifier with given parameters (curve: {}, scheme: {}): not supported", curve_parameter, scheme_parameter))
    }
}

fn cli_export_verifier<T: SolidityCompatibleField, S: SolidityCompatibleScheme<T>>(
    sub_matches: &ArgMatches,
    vk: serde_json::Value,
) -> Result<(), String> {
    println!("Exporting verifier...");

    let vk = serde_json::from_value(vk).map_err(|why| format!("{}", why))?;

    let verifier = S::export_solidity_verifier(vk);

    //write output file
    let output_path = Path::new(sub_matches.value_of("output").unwrap());
    let output_file = File::create(&output_path)
        .map_err(|why| format!("Could not create {}: {}", output_path.display(), why))?;

    let mut writer = BufWriter::new(output_file);

    writer
        .write_all(verifier.as_bytes())
        .map_err(|_| "Failed writing output to file".to_string())?;

    println!("Verifier exported to '{}'", output_path.display());
    Ok(())
}
