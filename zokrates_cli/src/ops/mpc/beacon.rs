use crate::cli_constants::MPC_DEFAULT_PATH;
use clap::{App, Arg, ArgMatches, SubCommand};
use rand_0_8::{rngs::StdRng, SeedableRng};
use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::path::Path;
use zokrates_bellman::Bellman;
use zokrates_common::constants::{BLS12_381, BN128};
use zokrates_field::{BellmanFieldExtensions, Bls12_381Field, Bn128Field, Field};
use zokrates_proof_systems::{MpcBackend, MpcScheme, G16};

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("beacon")
        .about("Applies a random beacon")
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
            Arg::with_name("curve")
                .short("c")
                .long("curve")
                .help("Curve used in the ceremony")
                .takes_value(true)
                .required(false)
                .possible_values(&[BN128, BLS12_381])
                .default_value(BN128),
        )
        .arg(
            Arg::with_name("hash")
                .short("h")
                .long("hash")
                .help("Hash used for the beacon")
                .takes_value(true)
                .required(true),
        )
        .arg(
            Arg::with_name("iterations")
                .short("n")
                .long("iterations")
                .help("Number of hash iterations")
                .takes_value(true)
                .required(true),
        )
        .arg(
            Arg::with_name("output")
                .short("o")
                .long("output")
                .help("Path of the output file")
                .value_name("FILE")
                .takes_value(true)
                .required(false)
                .default_value(MPC_DEFAULT_PATH),
        )
}

pub fn exec(sub_matches: &ArgMatches) -> Result<(), String> {
    match sub_matches.value_of("curve").unwrap() {
        BN128 => cli_mpc_beacon::<Bn128Field, G16, Bellman>(sub_matches),
        BLS12_381 => cli_mpc_beacon::<Bls12_381Field, G16, Bellman>(sub_matches),
        _ => unreachable!(),
    }
}

fn cli_mpc_beacon<T: Field + BellmanFieldExtensions, S: MpcScheme<T>, B: MpcBackend<T, S>>(
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    let path = Path::new(sub_matches.value_of("input").unwrap());
    let file =
        File::open(path).map_err(|why| format!("Could not open `{}`: {}", path.display(), why))?;

    let mut reader = BufReader::new(file);

    let beacon_hash = sub_matches.value_of("hash").unwrap();
    let num_iterations: usize = sub_matches.value_of("iterations").unwrap().parse().unwrap();

    if !(10..=63).contains(&num_iterations) {
        return Err("Number of hash iterations should be in the [10, 63] range".to_string());
    }

    println!("Creating a beacon RNG");

    // Create an RNG based on the outcome of the random beacon
    let mut rng = {
        use byteorder::ReadBytesExt;
        use sha2::{Digest, Sha256};

        // The hash used for the beacon
        let mut cur_hash = hex::decode(beacon_hash)
            .map_err(|_| "Beacon hash should be in hexadecimal format".to_string())?;

        if cur_hash.len() != 32 {
            return Err("Beacon hash should be 32 bytes long".to_string());
        }

        // Performs 2^n hash iterations over it
        let n: usize = num_iterations;

        for i in 0..(1u64 << n) {
            // Print 1024 of the interstitial states
            // so that verification can be
            // parallelized
            if i % (1u64 << (n - 10)) == 0 {
                print!("{}: ", i);
                for b in cur_hash.iter() {
                    print!("{:02x}", b);
                }
                println!();
            }

            cur_hash = Sha256::digest(&cur_hash).to_vec();
        }

        print!("Final result of beacon: ");
        for b in cur_hash.iter() {
            print!("{:02x}", b);
        }
        println!("\n");

        let mut digest = &cur_hash[..];

        let mut seed = [0u8; 32];
        for e in &mut seed {
            *e = digest.read_u8().unwrap();
        }

        StdRng::from_seed(seed)
    };

    let output_path = Path::new(sub_matches.value_of("output").unwrap());
    let output_file = File::create(output_path)
        .map_err(|why| format!("Could not create `{}`: {}", output_path.display(), why))?;

    let mut writer = BufWriter::new(output_file);

    println!("Contributing to `{}`...", path.display());
    let hash = B::contribute(&mut reader, &mut rng, &mut writer)
        .map_err(|e| format!("Failed to contribute: {}", e))?;

    println!("The BLAKE2b hash of your contribution is:\n");
    for line in hash.chunks(16) {
        print!("\t");
        for section in line.chunks(4) {
            for b in section {
                print!("{:02x}", b);
            }
            print!(" ");
        }
        println!();
    }

    println!(
        "\nYour contribution has been written to `{}`",
        output_path.display()
    );

    Ok(())
}
