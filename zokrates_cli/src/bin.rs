//
// @file bin.rs
// @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
// @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
// @date 2017

extern crate clap;
extern crate bincode;
extern crate regex;
extern crate zokrates_core;
extern crate zokrates_fs_resolver;

use std::fs::File;
use std::path::{Path, PathBuf};
use std::io::{BufWriter, Write, BufReader, BufRead, stdin};
use std::collections::HashMap;
use std::string::String;
use zokrates_core::compile::compile;
use zokrates_core::field::{Field, FieldPrime};
use zokrates_core::r1cs::{r1cs_program};
use zokrates_core::flat_absy::FlatProg;
use clap::{App, AppSettings, Arg, SubCommand};
#[cfg(feature = "libsnark")]
use zokrates_core::libsnark::{setup, generate_proof};
use bincode::{serialize_into, deserialize_from , Infinite};
use regex::Regex;
use zokrates_core::verification::CONTRACT_TEMPLATE;
use zokrates_fs_resolver::resolve as fs_resolve;

fn main() {
    const FLATTENED_CODE_DEFAULT_PATH: &str = "out";
    const VERIFICATION_KEY_DEFAULT_PATH: &str = "verification.key";
    const PROVING_KEY_DEFAULT_PATH: &str = "proving.key";
    const VERIFICATION_CONTRACT_DEFAULT_PATH: &str = "verifier.sol";
    const WITNESS_DEFAULT_PATH: &str = "witness";
    const VARIABLES_INFORMATION_KEY_DEFAULT_PATH: &str = "variables.inf";

    // cli specification using clap library
    let matches = App::new("ZoKrates")
    .setting(AppSettings::SubcommandRequiredElseHelp)
    .version("0.2")
    .author("Jacob Eberhardt, Dennis Kuhnert")
    .about("Supports generation of zkSNARKs from high level language code including Smart Contracts for proof verification on the Ethereum Blockchain.\n'I know that I show nothing!'")
    .subcommand(SubCommand::with_name("compile")
        .about("Compiles into flattened conditions. Produces two files: human-readable '.code' file and binary file")
        .arg(Arg::with_name("input")
            .short("i")
            .long("input")
            .help("path of source code file to compile.")
            .value_name("FILE")
            .takes_value(true)
            .required(true)
        ).arg(Arg::with_name("output")
            .short("o")
            .long("output")
            .help("output file path.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(FLATTENED_CODE_DEFAULT_PATH)
        ).arg(Arg::with_name("optimized")
            .long("optimized")
            .help("perform optimization.")
            .required(false)
        ).arg(Arg::with_name("light")
            .long("light")
            .help("Skip logs and human readable output")
            .required(false)
        ).arg(Arg::with_name("gadgets")
            .long("gadgets")
            .help("include libsnark gadgets such as sha256")
            .required(false)
        )
     )
    .subcommand(SubCommand::with_name("setup")
        .about("Performs a trusted setup for a given constraint system.")
        .arg(Arg::with_name("input")
            .short("i")
            .long("input")
            .help("path of compiled code.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(FLATTENED_CODE_DEFAULT_PATH)
        )
        .arg(Arg::with_name("proving-key-path")
            .short("p")
            .long("proving-key-path")
            .help("Path of the generated proving key file.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(PROVING_KEY_DEFAULT_PATH)
        )
        .arg(Arg::with_name("verification-key-path")
            .short("v")
            .long("verification-key-path")
            .help("Path of the generated verification key file.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(VERIFICATION_KEY_DEFAULT_PATH)
        )
        .arg(Arg::with_name("meta-information")
            .short("m")
            .long("meta-information")
            .help("Path of file containing meta information for variable transformation.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(VARIABLES_INFORMATION_KEY_DEFAULT_PATH)
        )
    )
    .subcommand(SubCommand::with_name("export-verifier")
        .about("Exports a verifier as Solidity smart contract.")
        .arg(Arg::with_name("input")
            .short("i")
            .long("input")
            .help("path of verifier.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(VERIFICATION_KEY_DEFAULT_PATH)
        )
        .arg(Arg::with_name("output")
            .short("o")
            .long("output")
            .help("output file path.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(VERIFICATION_CONTRACT_DEFAULT_PATH)
        )
    )
    .subcommand(SubCommand::with_name("compute-witness")
        .about("Calculates a witness for a given constraint system, i.e., a variable assignment which satisfies all constraints. Private inputs are specified interactively.")
        .arg(Arg::with_name("input")
            .short("i")
            .long("input")
            .help("path of compiled code.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(FLATTENED_CODE_DEFAULT_PATH)
        ).arg(Arg::with_name("output")
            .short("o")
            .long("output")
            .help("output file path.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(WITNESS_DEFAULT_PATH)
        ).arg(Arg::with_name("arguments")
            .short("a")
            .long("arguments")
            .help("Arguments for the program's main method. Space separated list.")
            .takes_value(true)
            .multiple(true) // allows multiple values
            .required(false)
        ).arg(Arg::with_name("interactive")
            .long("interactive")
            .help("enter private inputs interactively.")
            .required(false)
        )
    )
    .subcommand(SubCommand::with_name("generate-proof")
        .about("Calculates a proof for a given constraint system and witness.")
        .arg(Arg::with_name("witness")
            .short("w")
            .long("witness")
            .help("Path of witness file.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(WITNESS_DEFAULT_PATH)
        ).arg(Arg::with_name("provingkey")
            .short("p")
            .long("provingkey")
            .help("Path of proving key file.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(PROVING_KEY_DEFAULT_PATH)
        ).arg(Arg::with_name("meta-information")
            .short("i")
            .long("meta-information")
            .help("Path of file containing meta information for variable transformation.")
            .value_name("FILE")
            .takes_value(true)
            .required(false)
            .default_value(VARIABLES_INFORMATION_KEY_DEFAULT_PATH)
        )
    )
    .get_matches();

    match matches.subcommand() {
        ("compile", Some(sub_matches)) => {
            println!("Compiling {}", sub_matches.value_of("input").unwrap());

            let path = PathBuf::from(sub_matches.value_of("input").unwrap());

            let location = path.parent().unwrap().to_path_buf().into_os_string().into_string().unwrap();

            let should_optimize = sub_matches.occurrences_of("optimized") > 0;

            let should_include_gadgets = sub_matches.occurrences_of("gadgets") > 0;

            let light = sub_matches.occurrences_of("light") > 0;

            let bin_output_path = Path::new(sub_matches.value_of("output").unwrap());

            let hr_output_path = bin_output_path.to_path_buf().with_extension("code");

            let file = File::open(path.clone()).unwrap();

            let mut reader = BufReader::new(file);
            
            let program_flattened: FlatProg<FieldPrime> = match compile(&mut reader, Some(location), Some(fs_resolve), should_optimize, should_include_gadgets) {
                Ok(p) => p,
                Err(why) => panic!("Compilation failed: {}", why)
            };

            // number of constraints the flattened program will translate to.
            let num_constraints = &program_flattened.functions
            .iter()
            .find(|x| x.id == "main")
            .unwrap().statements.len();

            // serialize flattened program and write to binary file
            let mut bin_output_file = match File::create(&bin_output_path) {
                Ok(file) => file,
                Err(why) => panic!("couldn't create {}: {}", bin_output_path.display(), why),
            };

            serialize_into(&mut bin_output_file, &program_flattened, Infinite).expect("Unable to write data to file.");

            if !light {
                // write human-readable output file
                let hr_output_file = match File::create(&hr_output_path) {
                    Ok(file) => file,
                    Err(why) => panic!("couldn't create {}: {}", hr_output_path.display(), why),
                };

                let mut hrofb = BufWriter::new(hr_output_file);
                write!(&mut hrofb, "{}\n", program_flattened).expect("Unable to write data to file.");
                hrofb.flush().expect("Unable to flush buffer.");
            }

            if !light {
                // debugging output
                println!("Compiled program:\n{}", program_flattened);
            }

            println!("Compiled code written to '{}'", bin_output_path.display());

            if !light {
                println!("Human readable code to '{}'", hr_output_path.display());
            }

            println!("Number of constraints: {}", num_constraints);
        }
        ("compute-witness", Some(sub_matches)) => {
            println!("Computing witness for:");

            // read compiled program
            let path = Path::new(sub_matches.value_of("input").unwrap());
            let mut file = match File::open(&path) {
                Ok(file) => file,
                Err(why) => panic!("couldn't open {}: {}", path.display(), why),
            };

            let program_ast: FlatProg<FieldPrime> = match deserialize_from(&mut file, Infinite) {
                Ok(x) => x,
                Err(why) => {
                    println!("{:?}", why);
                    std::process::exit(1);
                }
            };

            let main_flattened = program_ast
                .functions
                .iter()
                .find(|x| x.id == "main")
                .unwrap();

            // print deserialized flattened program
            println!("{}", main_flattened);

            // validate #arguments
            let mut cli_arguments: Vec<FieldPrime> = Vec::new();
            match sub_matches.values_of("arguments"){
                Some(p) => {
                    let arg_strings: Vec<&str> = p.collect();
                    cli_arguments = arg_strings.into_iter().map(|x| FieldPrime::from(x)).collect();
                },
                None => {
                }
            }

            // handle interactive and non-interactive modes
            let is_interactive = sub_matches.occurrences_of("interactive") > 0;

            // in interactive mode, only public inputs are expected
            let expected_cli_args_count = main_flattened.arguments.iter().filter(|x| !(x.private && is_interactive)).count();

            if cli_arguments.len() != expected_cli_args_count {
                println!("Wrong number of arguments. Given: {}, Required: {}.", cli_arguments.len(), expected_cli_args_count);
                std::process::exit(1);
            }

            let mut cli_arguments_iter = cli_arguments.into_iter();
            let arguments = main_flattened.arguments.clone().into_iter().map(|x| {
                match x.private && is_interactive {
                    // private inputs are passed interactively when the flag is present
                    true => {
                        println!("Please enter a value for {:?}:", x.id);
                        let mut input = String::new();
                        let stdin = stdin();
                        stdin
                            .lock()
                            .read_line(&mut input)
                            .expect("Did not enter a correct String");
                        FieldPrime::from(input.trim())
                    }
                    // otherwise, they are taken from the CLI arguments
                    false => {
                        match cli_arguments_iter.next() {
                            Some(x) => x,
                            None => {
                                std::process::exit(1);
                            }
                        }
                    }
                }
            }).collect();

            let witness_map = main_flattened.get_witness(arguments).unwrap();

            println!("\nWitness: \n\n{}", witness_map
                .iter()
                .filter_map(|(variable, value)| match variable {
                    variable if variable.is_output() => Some(format!("{} {}", variable, value)),
                    _ => None
                }).collect::<Vec<String>>().join("\n"));

            // write witness to file
            let output_path = Path::new(sub_matches.value_of("output").unwrap());
            let output_file = match File::create(&output_path) {
                Ok(file) => file,
                Err(why) => panic!("couldn't create {}: {}", output_path.display(), why),
            };
            let mut bw = BufWriter::new(output_file);
            for (var, val) in &witness_map {
                write!(&mut bw, "{} {}\n", var, val.to_dec_string()).expect("Unable to write data to file.");
            }
            bw.flush().expect("Unable to flush buffer.");
        }
        ("setup", Some(sub_matches)) => {
            println!("Performing setup...");

            let path = Path::new(sub_matches.value_of("input").unwrap());
            let mut file = match File::open(&path) {
                Ok(file) => file,
                Err(why) => panic!("couldn't open {}: {}", path.display(), why),
            };

            let program_ast: FlatProg<FieldPrime> = match deserialize_from(&mut file, Infinite) {
                Ok(x) => x,
                Err(why) => {
                    println!("{:?}", why);
                    std::process::exit(1);
                }
            };

            let main_flattened = program_ast
                .functions
                .iter()
                .find(|x| x.id == "main")
                .unwrap();

            // print deserialized flattened program
            println!("{}", main_flattened);

            // transform to R1CS
            let (variables, private_inputs_offset, a, b, c) = r1cs_program(&program_ast);

            // write variables meta information to file
            let var_inf_path = Path::new(sub_matches.value_of("meta-information").unwrap());
            let var_inf_file = match File::create(&var_inf_path) {
                Ok(file) => file,
                Err(why) => panic!("couldn't open {}: {}", var_inf_path.display(), why),
            };
            let mut bw = BufWriter::new(var_inf_file);
                write!(&mut bw, "Private inputs offset:\n{}\n", private_inputs_offset).expect("Unable to write data to file.");
                write!(&mut bw, "R1CS variable order:\n").expect("Unable to write data to file.");
            for var in &variables {
                write!(&mut bw, "{} ", var).expect("Unable to write data to file.");
            }
            write!(&mut bw, "\n").expect("Unable to write data to file.");
            bw.flush().expect("Unable to flush buffer.");


            // get paths for proving and verification keys
            let pk_path = sub_matches.value_of("proving-key-path").unwrap();
            let vk_path = sub_matches.value_of("verification-key-path").unwrap();

            let public_inputs_indices = main_flattened.arguments.iter().enumerate()
                .filter_map(|(index, x)| match x.private {
                    true => None,
                    false => Some(index),
                });

            let public_inputs = public_inputs_indices
                .map(|i| main_flattened.signature.inputs[i].get_primitive_count())
                .fold(0, |acc, e| acc + e);

            let outputs = main_flattened.signature.outputs.iter().map(|t| t.get_primitive_count())
                .fold(0, |acc, e| acc + e);

            let num_inputs = public_inputs + outputs;

            // run setup phase
            #[cfg(feature="libsnark")]{
                // number of inputs in the zkSNARK sense, i.e., input variables + output variables
                println!("setup successful: {:?}", setup(variables, a, b, c, num_inputs, pk_path, vk_path));
            }
        }
        ("export-verifier", Some(sub_matches)) => {
            println!("Exporting verifier...");
            // read vk file
            let input_path = Path::new(sub_matches.value_of("input").unwrap());
            let input_file = match File::open(&input_path) {
                Ok(input_file) => input_file,
                Err(why) => panic!("couldn't open {}: {}", input_path.display(), why),
            };
            let reader = BufReader::new(input_file);
            let mut lines = reader.lines();

            let mut template_text = String::from(CONTRACT_TEMPLATE);
            let ic_template = String::from("vk.IC[index] = Pairing.G1Point(points);");      //copy this for each entry

            //replace things in template
            let vk_regex = Regex::new(r#"(<%vk_[^i%]*%>)"#).unwrap();
            let vk_ic_len_regex = Regex::new(r#"(<%vk_ic_length%>)"#).unwrap();
            let vk_ic_index_regex = Regex::new(r#"index"#).unwrap();
            let vk_ic_points_regex = Regex::new(r#"points"#).unwrap();
            let vk_ic_repeat_regex = Regex::new(r#"(<%vk_ic_pts%>)"#).unwrap();
            let vk_input_len_regex = Regex::new(r#"(<%vk_input_length%>)"#).unwrap();

            for _ in 0..7 {
                let current_line: String = lines.next().expect("Unexpected end of file in verification key!").unwrap();
                let current_line_split: Vec<&str> = current_line.split("=").collect();
                assert_eq!(current_line_split.len(), 2);
                template_text = vk_regex.replace(template_text.as_str(), current_line_split[1].trim()).into_owned();
            }

            let current_line: String = lines.next().expect("Unexpected end of file in verification key!").unwrap();
            let current_line_split: Vec<&str> = current_line.split("=").collect();
            assert_eq!(current_line_split.len(), 2);
            let ic_count: i32 = current_line_split[1].trim().parse().unwrap();

            template_text = vk_ic_len_regex.replace(template_text.as_str(), format!("{}", ic_count).as_str()).into_owned();
            template_text = vk_input_len_regex.replace(template_text.as_str(), format!("{}", ic_count-1).as_str()).into_owned();

            let mut ic_repeat_text = String::new();
            for x in 0..ic_count {
                let mut curr_template = ic_template.clone();
                let current_line: String = lines.next().expect("Unexpected end of file in verification key!").unwrap();
                let current_line_split: Vec<&str> = current_line.split("=").collect();
                assert_eq!(current_line_split.len(), 2);
                curr_template = vk_ic_index_regex.replace(curr_template.as_str(), format!("{}", x).as_str()).into_owned();
                curr_template = vk_ic_points_regex.replace(curr_template.as_str(), current_line_split[1].trim()).into_owned();
                ic_repeat_text.push_str(curr_template.as_str());
                if x < ic_count - 1 {
                    ic_repeat_text.push_str("\n        ");
                }
            }
            template_text = vk_ic_repeat_regex.replace(template_text.as_str(), ic_repeat_text.as_str()).into_owned();

            //write output file
            let output_path = Path::new(sub_matches.value_of("output").unwrap());
            let mut output_file = match File::create(&output_path) {
                Ok(file) => file,
                Err(why) => panic!("couldn't create {}: {}", output_path.display(), why),
            };
            output_file.write_all(&template_text.as_bytes()).expect("Failed writing output to file.");
            println!("Finished exporting verifier.");
        }
        ("generate-proof", Some(sub_matches)) => {
            println!("Generating proof...");

            // deserialize witness
            let witness_path = Path::new(sub_matches.value_of("witness").unwrap());
            let witness_file = match File::open(&witness_path) {
                Ok(file) => file,
                Err(why) => panic!("couldn't open {}: {}", witness_path.display(), why),
            };

            let reader = BufReader::new(witness_file);
            let mut lines = reader.lines();
            let mut witness_map = HashMap::new();

            loop {
                match lines.next() {
                    Some(Ok(ref x)) => {
                        let pairs: Vec<&str> = x.split_whitespace().collect();
                        witness_map.insert(pairs[0].to_string(),FieldPrime::from_dec_string(pairs[1].to_string()));
                    },
                    None => break,
                    Some(Err(err)) => panic!("Error reading witness: {}", err),
                }
            }

            // determine variable order
            let var_inf_path = Path::new(sub_matches.value_of("meta-information").unwrap());
            let var_inf_file = match File::open(&var_inf_path) {
                Ok(file) => file,
                Err(why) => panic!("couldn't open {}: {}", var_inf_path.display(), why),
            };
            let var_reader = BufReader::new(var_inf_file);
            let mut var_lines = var_reader.lines();

            // get private inputs offset
            let private_inputs_offset;
            if let Some(Ok(ref o)) = var_lines.nth(1){ // consumes first 2 lines
                private_inputs_offset = o.parse().expect("Failed parsing private inputs offset");
            } else {
                panic!("Error reading private inputs offset");
            }

            // get variables vector
            let mut variables: Vec<String> = Vec::new();
            if let Some(Ok(ref v)) = var_lines.nth(1){
                let iter = v.split_whitespace();
                for i in iter {
                        variables.push(i.to_string());
                }
            } else {
                panic!("Error reading variables.");
            }

            println!("Using Witness: {:?}", witness_map);

            let witness: Vec<_> = variables.iter().map(|x| witness_map[x].clone()).collect();

            // split witness into public and private inputs at offset
            let mut public_inputs: Vec<_>= witness.clone();
            let private_inputs: Vec<_> = public_inputs.split_off(private_inputs_offset);

            println!("Public inputs: {:?}", public_inputs);
            println!("Private inputs: {:?}", private_inputs);

            let pk_path = sub_matches.value_of("provingkey").unwrap();

            // run libsnark
            #[cfg(feature="libsnark")]{
                println!("generate-proof successful: {:?}", generate_proof(pk_path, public_inputs, private_inputs));
            }

        }
        _ => unimplemented!(), // Either no subcommand or one not tested for...
    }

}

#[cfg(test)]
mod tests {
    extern crate glob;
    use super::*;
    use self::glob::glob;

    #[test]
    fn examples() {
        for p in glob("./examples/**/*.code").expect("Failed to read glob pattern") {
            let path = match p {
                Ok(x) => x,
                Err(why) => panic!("Error: {:?}", why),
            };

            if path.to_str().unwrap().contains("error") {
                continue
            }

            println!("Testing {:?}", path);

            let file = File::open(path.clone()).unwrap();

            let mut reader = BufReader::new(file);
            let location = path.parent().unwrap().to_path_buf().into_os_string().into_string().unwrap();

            let program_flattened: FlatProg<FieldPrime> =
                compile(&mut reader, Some(location), Some(fs_resolve), true, false).unwrap();

            let (..) = r1cs_program(&program_flattened);
        }
    }

    #[test]
    fn examples_with_input_success() {
        //these examples should compile and run
        for p in glob("./examples/test*.code").expect("Failed to read glob pattern") {
            let path = match p {
                Ok(x) => x,
                Err(why) => panic!("Error: {:?}", why),
            };
            println!("Testing {:?}", path);

            let file = File::open(path.clone()).unwrap();

            let location = path.parent().unwrap().to_path_buf().into_os_string().into_string().unwrap();

            let mut reader = BufReader::new(file);

            let program_flattened: FlatProg<FieldPrime> =

            compile(&mut reader, Some(location), Some(fs_resolve), true, false).unwrap();

            let (..) = r1cs_program(&program_flattened);
            let _ = program_flattened.get_witness(vec![FieldPrime::from(0)]).unwrap();
        }
    }

    #[test]
    fn examples_with_input_failure() {
        //these examples should compile but not run
        for p in glob("./examples/runtime_errors/*.code").expect("Failed to read glob pattern") {
            let path = match p {
                Ok(x) => x,
                Err(why) => panic!("Error: {:?}", why),
            };
            println!("Testing {:?}", path);

            let file = File::open(path.clone()).unwrap();

            let location = path.parent().unwrap().to_path_buf().into_os_string().into_string().unwrap();

            let mut reader = BufReader::new(file);

            let program_flattened: FlatProg<FieldPrime> =

            compile(&mut reader, Some(location), Some(fs_resolve), true, false).unwrap();

            let (..) = r1cs_program(&program_flattened);

            let result = std::panic::catch_unwind(|| {
                let _ = program_flattened.get_witness(vec![FieldPrime::from(0)]).unwrap();
            });
            assert!(result.is_err());
        }
    }
}
