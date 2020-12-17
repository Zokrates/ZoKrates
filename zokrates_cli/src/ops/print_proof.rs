use crate::constants::JSON_PROOF_PATH;
use clap::{App, Arg, ArgMatches, SubCommand};
use serde_json::Value;
use std::fs::File;
use std::path::Path;

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
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    let format = sub_matches.value_of("format").unwrap();
    let path = Path::new(sub_matches.value_of("proof-path").unwrap());

    let file =
        File::open(&path).map_err(|why| format!("Couldn't open {}: {}", path.display(), why))?;

    let proof_object: Value = serde_json::from_reader(file).map_err(|why| format!("{:?}", why))?;

    match format {
        "json" => {
            println!("~~~~~~~~ Copy the output below for valid ABIv2 format ~~~~~~~~");
            println!();
            print!("{}", proof_object["proof"]);
            print!(",");
            println!("{}", proof_object["inputs"]);
            println!();
            println!("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~");
        }
        "remix" => {
            println!("~~~~~~~~ Copy the output below for valid ABIv1 format ~~~~~~~~");
            println!();

            for (_, value) in proof_object["proof"].as_object().unwrap().iter() {
                print!("{}", value);
                print!(",");
            }

            println!("{}", proof_object["inputs"]);
            println!();
            println!("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~");
        }
        _ => unreachable!(),
    }

    Ok(())
}
