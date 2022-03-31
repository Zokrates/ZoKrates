use crate::constants::{self, JSON_PROOF_PATH};
use crate::helpers::{CurveParameter, SchemeParameter};
use clap::{App, Arg, ArgMatches, SubCommand};
use serde_json::Value;
use std::convert::TryInto;
use std::fs::File;
use std::path::Path;
use zokrates_core::proof_system::{
    marlin, Backend, Marlin, Proof, Scheme, SolidityCompatibleField, SolidityCompatibleScheme, G16,
    GM17, PGHR13,
};
use zokrates_field::{Bls12_381Field, Bn128Field, Field};

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
                .required(true),
        )
        .arg(
            Arg::with_name("proving-scheme")
                .short("s")
                .long("proving-scheme")
                .help("Proving scheme to use in the setup. Available options are G16 (default), PGHR13 and GM17")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(constants::G16)
        )
        .arg(
            Arg::with_name("curve")
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
    let curve = sub_matches.value_of("curve").unwrap();
    let scheme = sub_matches.value_of("proving-scheme").unwrap();

    let parameters: (CurveParameter, SchemeParameter) =
        (curve.try_into().unwrap(), scheme.try_into().unwrap());

    println!(
        "Printing proof at location {:?} using proving scheme {:?} and curve {:?}",
        sub_matches
            .values_of("proof-path")
            .clone()
            .unwrap()
            .next()
            .unwrap(),
        parameters.1,
        parameters.0
    );

    match parameters {
        (CurveParameter::Bn128, SchemeParameter::PGHR13) => {
            cli_print_proof::<Bn128Field, PGHR13>(sub_matches)
        }
        (CurveParameter::Bn128, SchemeParameter::G16) => {
            cli_print_proof::<Bn128Field, G16>(sub_matches)
        }
        (CurveParameter::Bn128, SchemeParameter::GM17) => {
            cli_print_proof::<Bn128Field, GM17>(sub_matches)
        }
        (CurveParameter::Bn128, SchemeParameter::MARLIN) => {
            cli_print_proof::<Bn128Field, Marlin>(sub_matches)
        }
        _ => Err(format!("Could not print proof with given parameters (curve: {}, scheme: {}): only bn128 is supported", curve, scheme))
    }
}

fn cli_print_proof<T: SolidityCompatibleField, S: SolidityCompatibleScheme<T>>(
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    let format = sub_matches.value_of("format").unwrap();
    let path = Path::new(sub_matches.value_of("proof-path").unwrap());

    let file =
        File::open(&path).map_err(|why| format!("Couldn't open {}: {}", path.display(), why))?;

    let proof: Proof<T, S> = serde_json::from_reader(file).map_err(|why| format!("{:?}", why))?;

    let inputs = serde_json::to_value(&proof.inputs).unwrap();

    let res = S::Proof::from(proof.proof);
    let proof_object = serde_json::to_value(&res).unwrap();

    match format {
        "json" => {
            println!("~~~~~~~~ Copy the output below for valid ABIv2 format ~~~~~~~~");
            println!();
            print!("{}", inputs);
            print!(",");
            println!("{}", proof_object);
            println!();
            println!("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~");
        }
        "remix" => {
            println!("~~~~~~~~ Copy the output below for valid ABIv1 format ~~~~~~~~");
            println!();

            for (_, value) in proof_object.as_object().unwrap().iter() {
                print!("{}", value);
                print!(",");
            }

            println!("{}", inputs);
            println!();
            println!("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~");
        }
        _ => unreachable!(),
    }

    Ok(())
}
