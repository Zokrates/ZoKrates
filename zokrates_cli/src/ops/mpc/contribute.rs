use crate::constants::MPC_DEFAULT_PATH;
use clap::{App, Arg, ArgMatches, SubCommand};
use phase2::parameters::MPCParameters;
use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::path::Path;

pub fn subcommand() -> App<'static, 'static> {
    SubCommand::with_name("contribute")
        .about("Contribute to an MPC ceremony")
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
    let path = Path::new(sub_matches.value_of("input").unwrap());
    let file =
        File::open(&path).map_err(|why| format!("Could not open `{}`: {}", path.display(), why))?;

    let reader = BufReader::new(file);
    let mut params = MPCParameters::read(reader, true)
        .map_err(|why| format!("Could not read `{}`: {}", path.display(), why))?;

    let entropy = sub_matches.value_of("entropy").unwrap();

    // Create an RNG based on a mixture of system randomness and user provided randomness
    let mut rng = {
        use blake2::{Blake2b, Digest};
        use byteorder::{BigEndian, ReadBytesExt};
        use rand::chacha::ChaChaRng;
        use rand::{OsRng, Rng, SeedableRng};

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

    println!("Contributing to `{}`...", path.display());
    let zero: u32 = 0;
    let hash = params.contribute(&mut rng, &zero);
    println!("Contribution hash: {}", hex::encode(hash));

    let output_path = Path::new(sub_matches.value_of("output").unwrap());
    let output_file = File::create(&output_path)
        .map_err(|why| format!("Could not create `{}`: {}", output_path.display(), why))?;

    println!(
        "Your contribution has been written to `{}`",
        output_path.display()
    );

    let mut writer = BufWriter::new(output_file);
    params.write(&mut writer).map_err(|e| e.to_string())?;

    Ok(())
}
