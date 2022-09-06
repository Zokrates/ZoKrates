use crate::cli_constants::MPC_DEFAULT_PATH;
use clap::{App, Arg, ArgMatches, SubCommand};
use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::path::Path;
use zokrates_bellman::Bellman;
use zokrates_common::constants::{BLS12_381, BN128};
use zokrates_field::{BellmanFieldExtensions, Bls12_381Field, Bn128Field, Field};
use zokrates_proof_systems::{MpcBackend, MpcScheme, G16};

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("contribute")
        .about("Contributes to a ceremony")
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
            Arg::with_name("entropy")
                .short("e")
                .long("entropy")
                .help("User provided randomness")
                .takes_value(true)
                .required(false),
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
        BN128 => cli_mpc_contribute::<Bn128Field, G16, Bellman>(sub_matches),
        BLS12_381 => cli_mpc_contribute::<Bls12_381Field, G16, Bellman>(sub_matches),
        _ => unreachable!(),
    }
}

pub fn cli_mpc_contribute<
    T: Field + BellmanFieldExtensions,
    S: MpcScheme<T>,
    B: MpcBackend<T, S>,
>(
    sub_matches: &ArgMatches,
) -> Result<(), String> {
    let path = Path::new(sub_matches.value_of("input").unwrap());
    let file =
        File::open(&path).map_err(|why| format!("Could not open `{}`: {}", path.display(), why))?;

    let mut reader = BufReader::new(file);
    let entropy = sub_matches.value_of("entropy").unwrap();

    // Create an RNG based on a mixture of system randomness and user provided randomness
    let mut rng = {
        use blake2::{Blake2b, Digest};
        use byteorder::{BigEndian, ReadBytesExt};
        use rand_0_4::chacha::ChaChaRng;
        use rand_0_4::{OsRng, Rng, SeedableRng};

        let h = {
            let mut system_rng = OsRng::new().unwrap();
            let mut h = Blake2b::default();

            // Gather 1024 bytes of entropy from the system
            for _ in 0..1024 {
                let r: u8 = system_rng.gen();
                h.input(&[r]);
            }

            // Hash it all up to make a seed
            h.input(&entropy.as_bytes());
            h.result()
        };

        let mut digest = &h[..];

        // Interpret the first 32 bytes of the digest as 8 32-bit words
        let mut seed = [0u32; 8];
        for e in &mut seed {
            *e = digest.read_u32::<BigEndian>().unwrap();
        }

        ChaChaRng::from_seed(&seed)
    };

    let output_path = Path::new(sub_matches.value_of("output").unwrap());
    let output_file = File::create(&output_path)
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
