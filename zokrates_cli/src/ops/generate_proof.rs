use crate::constants;
use crate::helpers::*;
use clap::{App, Arg, ArgMatches, SubCommand};
use std::convert::TryFrom;
use std::fs::File;
use std::io::{BufReader, Read, Write};
use std::path::Path;
use zokrates_core::ir;
use zokrates_core::ir::ProgEnum;
#[cfg(feature = "ark")]
use zokrates_core::proof_system::ark::Ark;
#[cfg(feature = "bellman")]
use zokrates_core::proof_system::bellman::Bellman;
#[cfg(feature = "libsnark")]
use zokrates_core::proof_system::libsnark::Libsnark;
#[cfg(any(feature = "bellman", feature = "ark", feature = "libsnark"))]
use zokrates_core::proof_system::*;
use zokrates_field::Field;

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("generate-proof")
        .about("Calculates a proof for a given constraint system and witness")
        .arg(
            Arg::with_name("witness")
                .short("w")
                .long("witness")
                .help("Path of the witness file")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(constants::WITNESS_DEFAULT_PATH),
        )
        .arg(
            Arg::with_name("proving-key-path")
                .short("p")
                .long("proving-key-path")
                .help("Path of the proving key file")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(constants::PROVING_KEY_DEFAULT_PATH),
        )
        .arg(
            Arg::with_name("proof-path")
                .short("j")
                .long("proof-path")
                .help("Path of the JSON proof file")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(constants::JSON_PROOF_PATH),
        )
        .arg(
            Arg::with_name("input")
                .short("i")
                .long("input")
                .help("Path of the binary")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(constants::FLATTENED_CODE_DEFAULT_PATH),
        )
        .arg(
            Arg::with_name("backend")
                .short("b")
                .long("backend")
                .help("Backend to use")
                .takes_value(true)
                .required(false)
                .possible_values(constants::BACKENDS)
                .default_value(constants::BELLMAN),
        )
        .arg(
            Arg::with_name("proving-scheme")
                .short("s")
                .long("proving-scheme")
                .help("Proving scheme to use to generate the proof")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .possible_values(constants::SCHEMES)
                .default_value(constants::G16),
        )
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    let program_path = Path::new(sub_matches.value_of("input").unwrap());
    let program_file = File::open(&program_path)
        .map_err(|why| format!("Could not open {}: {}", program_path.display(), why))?;

    let mut reader = BufReader::new(program_file);
    let prog = ProgEnum::deserialize(&mut reader)?;

    let parameters = Parameters::try_from((
        sub_matches.value_of("backend").unwrap(),
        match prog {
            ProgEnum::Bn128Program(_) => constants::BN128,
            ProgEnum::Bls12_381Program(_) => constants::BLS12_381,
            ProgEnum::Bls12_377Program(_) => constants::BLS12_377,
            ProgEnum::Bw6_761Program(_) => constants::BW6_761,
        },
        sub_matches.value_of("proving-scheme").unwrap(),
    ))?;

    match parameters {
        #[cfg(feature = "bellman")]
        Parameters(BackendParameter::Bellman, _, SchemeParameter::G16) => match prog {
            ProgEnum::Bn128Program(p) => cli_generate_proof::<_, G16, Bellman>(p, sub_matches),
            ProgEnum::Bls12_381Program(p) => cli_generate_proof::<_, G16, Bellman>(p, sub_matches),
            _ => unreachable!(),
        },
        #[cfg(feature = "ark")]
        Parameters(BackendParameter::Ark, _, SchemeParameter::GM17) => match prog {
            ProgEnum::Bls12_377Program(p) => cli_generate_proof::<_, GM17, Ark>(p, sub_matches),
            ProgEnum::Bw6_761Program(p) => cli_generate_proof::<_, GM17, Ark>(p, sub_matches),
            ProgEnum::Bn128Program(p) => cli_generate_proof::<_, GM17, Ark>(p, sub_matches),
            _ => unreachable!(),
        },
        #[cfg(feature = "libsnark")]
        Parameters(BackendParameter::Libsnark, CurveParameter::Bn128, SchemeParameter::GM17) => {
            match prog {
                ProgEnum::Bn128Program(p) => {
                    cli_generate_proof::<_, GM17, Libsnark>(p, sub_matches)
                }
                _ => unreachable!(),
            }
        }
        #[cfg(feature = "libsnark")]
        Parameters(BackendParameter::Libsnark, CurveParameter::Bn128, SchemeParameter::PGHR13) => {
            match prog {
                ProgEnum::Bn128Program(p) => {
                    cli_generate_proof::<_, PGHR13, Libsnark>(p, sub_matches)
                }
                _ => unreachable!(),
            }
        }
        _ => unreachable!(),
    }
}

fn cli_generate_proof<T: Field, S: Scheme<T>, B: Backend<T, S>>(
    program: ir::Prog<T>,
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    println!("Generating proof...");

    // deserialize witness
    let witness_path = Path::new(sub_matches.value_of("witness").unwrap());
    let witness_file = match File::open(&witness_path) {
        Ok(file) => file,
        Err(why) => panic!("Could not open {}: {}", witness_path.display(), why),
    };

    let witness = ir::Witness::read(witness_file)
        .map_err(|why| format!("Could not load witness: {:?}", why))?;

    let pk_path = Path::new(sub_matches.value_of("proving-key-path").unwrap());
    let proof_path = Path::new(sub_matches.value_of("proof-path").unwrap());

    let pk_file = File::open(&pk_path)
        .map_err(|why| format!("Could not open {}: {}", pk_path.display(), why))?;

    let mut pk: Vec<u8> = Vec::new();
    let mut pk_reader = BufReader::new(pk_file);
    pk_reader
        .read_to_end(&mut pk)
        .map_err(|why| format!("Could not read {}: {}", pk_path.display(), why))?;

    let proof = B::generate_proof(program, witness, pk);
    let mut proof_file = File::create(proof_path).unwrap();

    let proof = serde_json::to_string_pretty(&proof).unwrap();
    proof_file
        .write(proof.as_bytes())
        .map_err(|why| format!("Could not write to {}: {}", proof_path.display(), why))?;

    if sub_matches.is_present("verbose") {
        println!("Proof:\n{}", proof);
    }

    println!("Proof written to '{}'", proof_path.display());
    Ok(())
}
