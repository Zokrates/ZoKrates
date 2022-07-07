use crate::cli_constants::JSON_PROOF_PATH;
use clap::{App, Arg, ArgMatches, SubCommand};
use std::convert::TryInto;
use std::fs::File;
use std::io::BufReader;
use std::path::Path;
use zokrates_common::helpers::{CurveParameter, SchemeParameter};
use zokrates_field::Bn128Field;
use zokrates_proof_systems::{
    Marlin, Proof, SolidityCompatibleField, SolidityCompatibleScheme, G16, GM17,
};

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("print-proof")
        .about("Prints proof in the chosen format")
        .arg(
            Arg::with_name("proof-path")
                .short("j")
                .long("proof-path")
                .help("Path of the JSON proof file")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(JSON_PROOF_PATH),
        )
        .arg(
            Arg::with_name("format")
                .short("f")
                .long("format")
                .value_name("FORMAT")
                .help("Format in which the proof should be printed")
                .takes_value(true)
                .possible_values(&["remix", "json"])
                .required(true)
                .default_value("remix"),
        )
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    let proof_path = Path::new(sub_matches.value_of("proof-path").unwrap());
    let proof_file = File::open(&proof_path)
        .map_err(|why| format!("Could not open {}: {}", proof_path.display(), why))?;

    // deserialize proof to JSON
    let proof_reader = BufReader::new(proof_file);
    let proof: serde_json::Value = serde_json::from_reader(proof_reader)
        .map_err(|why| format!("Could not deserialize proof: {}", why))?;

    // extract curve and scheme parameters from both
    let curve = proof
        .get("curve")
        .ok_or_else(|| "Field `curve` not found in proof".to_string())?
        .as_str()
        .ok_or_else(|| "`curve` should be a string".to_string())?;
    let scheme = proof
        .get("scheme")
        .ok_or_else(|| "Field `scheme` not found in proof".to_string())?
        .as_str()
        .ok_or_else(|| "`scheme` should be a string".to_string())?;

    let parameters: (CurveParameter, SchemeParameter) =
        (curve.try_into().unwrap(), scheme.try_into().unwrap());

    match parameters {
        (CurveParameter::Bn128, SchemeParameter::G16) => {
            cli_print_proof::<Bn128Field, G16>(sub_matches, proof)
        }
        (CurveParameter::Bn128, SchemeParameter::GM17) => {
            cli_print_proof::<Bn128Field, GM17>(sub_matches, proof)
        }
        (CurveParameter::Bn128, SchemeParameter::MARLIN) => {
            cli_print_proof::<Bn128Field, Marlin>(sub_matches, proof)
        }
        _ => Err(format!("Could not print proof with given parameters (curve: {}, scheme: {}): only bn128 is supported", curve, scheme))
    }
}

fn cli_print_proof<T: SolidityCompatibleField, S: SolidityCompatibleScheme<T>>(
    sub_matches: &ArgMatches,
    proof: serde_json::Value,
) -> Result<(), String> {
    let format = sub_matches.value_of("format").unwrap();

    let proof: Proof<T, S> = serde_json::from_value(proof).map_err(|why| format!("{:?}", why))?;

    let inputs = serde_json::to_value(&proof.inputs).unwrap();

    let res = S::Proof::from(proof.proof);
    let proof_object = serde_json::to_value(&res).unwrap();

    match format {
        "json" => {
            print!("{}", proof_object);
            print!(",");
            print!("{}", inputs);
            println!();
        }
        "remix" => {
            print!(
                "[{}]",
                proof_object
                    .as_object()
                    .unwrap()
                    .iter()
                    .map(|(_, value)| value.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            if !proof.inputs.is_empty() {
                print!(",");
                print!("{}", inputs);
            }
            println!();
        }
        _ => unreachable!(),
    }

    Ok(())
}
