//
// @file main.rs
// @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
// @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
// @date 2017

#![feature(box_patterns, box_syntax)]

#[macro_use]
extern crate lazy_static;
extern crate num;
extern crate clap; // cli

mod absy;
mod parser;
mod flatten;
mod r1cs;
mod field;
#[cfg(not(feature="nolibsnark"))]
mod libsnark;

use std::fs::File;
use std::path::Path;
use std::io::{Write, BufWriter};
use field::{Field, FieldPrime};
use absy::Prog;
use parser::parse_program;
use flatten::Flattener;
use r1cs::r1cs_program;
use clap::{Arg, App, AppSettings, SubCommand};
#[cfg(not(feature="nolibsnark"))]
use libsnark::run_libsnark;

fn main() {

    // cli specification using clap library
    let matches = App::new("zkc")
    .setting(AppSettings::SubcommandRequiredElseHelp)
    .version("0.1")
    .author("Jacob Eberhardt, Dennis Kuhnert")
    .about("Supports generation of zkSNARKs from high level language code including Smart Contracts for proof verification on the Ethereum Blockchain.")
    .subcommand(SubCommand::with_name("compile")
                                    .about("Compiles into flattened conditions.")
                                    .arg(Arg::with_name("input")
                                        .short("i")
                                        .help("path of source code file to compile.")
                                        .takes_value(true)
                                        .required(true)
                                    ).arg(Arg::with_name("output")
                                        .short("o")
                                        .help("output file path.")
                                        .takes_value(true)
                                        .required(false)
                                        .default_value("out.code")
                                    )
                                 )
    .subcommand(SubCommand::with_name("setup")
        .about("Performs a trusted setup for a given constraint system."))
    .subcommand(SubCommand::with_name("export-verifier")
        .about("Exports a verifier as Solidity smart contract."))
    .subcommand(SubCommand::with_name("compute-witness")
        .about("Calculates a witness for a given constraint system, i.e., a variable assignment which satisfies all constraints. Interactive if underspecified."))
    .subcommand(SubCommand::with_name("generate-proof")
        .about("Calculates a proof for a given constraint system and witness."))
    .subcommand(SubCommand::with_name("deploy-verifier")
        .about("Deploys Solidity verification code to an Ethereum network."))
    .get_matches();

    //println!("matches: {:?}", matches);

    match matches.subcommand() {
        ("compile", Some(sub_matches)) =>{

            println!("Compiling {}", sub_matches.value_of("input").unwrap());

            let path = Path::new(sub_matches.value_of("input").unwrap());
            let file = match File::open(&path) {
                Ok(file) => file,
                Err(why) => panic!("couldn't open {}: {}", path.display(), why),
            };

            let program_ast: Prog<FieldPrime> = match parse_program(file) {
                Ok(x) => x,
                Err(why) => {
                    println!("{:?}", why);
                    std::process::exit(1);
                },
            };

            // debugging output
            println!("uncompiled program:\n{}", program_ast);

            let program_flattened = Flattener::new(FieldPrime::get_required_bits()).flatten_program(program_ast);

            let output_path = Path::new(sub_matches.value_of("output").unwrap());
            let mut output_file = match File::create(&output_path) {
                Ok(file) => file,
                Err(why) => panic!("couldn't create {}: {}", output_path.display(), why),
            };

            let mut ofb = BufWriter::new(output_file);
            write!(&mut ofb, "{}\n", program_flattened).expect("Unable to write data to file.");
            ofb.flush();

            println!("Compiled code written to {}", sub_matches.value_of("output").unwrap());

            // debugging output
            println!("compiled program:\n{}", program_flattened);
        },
        ("compute-witness", Some(sub_matches)) => {
            println!("Computing witness...");
        },
        ("setup", Some(sub_matches)) => {
            println!("Performing setup...");
        },
        ("export-verifier", Some(sub_matches)) => {
            println!("Exporting verifier...");
        },
        ("generate-proof", Some(sub_matches)) => {
            println!("Generating proof...");
        },
        ("deploy-verifier", Some(sub_matches)) => {
            println!("Deploying verifier...");
            // use https://github.com/tomusdrw/rust-web3 for blockchain interaction
            // and https://doc.rust-lang.org/std/process/struct.Command.html for solc
        }
        _ => {unimplemented!()}, // Either no subcommand or one not tested for...
    }


    // let (variables, a, b, c) = r1cs_program(&program_flattened);
    // println!("variables {:?}", variables);
    // println!("A");
    // for x in &a {
    //     println!("{:?}", x);
    // }
    // println!("B");
    // for x in &b {
    //     println!("{:?}", x);
    // }
    // println!("C");
    // for x in &c {
    //     println!("{:?}", x);
    // }
    //
    // // calculate witness if wanted
    // if args.len() < 3 {
    //     std::process::exit(0);
    // }
    //
    // // check #inputs
    // let inputs: Vec<FieldPrime> = args[2].split_whitespace().map(|x| FieldPrime::from(x)).collect();
    // let args_provided = &program_flattened.functions.iter().find(|x| x.id=="main").unwrap().arguments;
    // assert!(inputs.len() == args_provided.len(),"Wrong number of arguments provided for main function. Provided: {}, Expected: {}.", inputs.len(), args_provided.len());
    // println!("inputs {:?}", inputs);
    //
    // // generate wittness
    // let witness_map = program_flattened.get_witness(inputs);
    // println!("witness_map {:?}", witness_map);
    // match witness_map.get("~out") {
    //     Some(out) => println!("~out: {}", out),
    //     None => println!("~out not found")
    // }
    // let witness: Vec<_> = variables.iter().map(|x| witness_map[x].clone()).collect();
    // println!("witness {:?}", witness);
    //
    // // run libsnark
    // #[cfg(not(feature="nolibsnark"))]{
    //     // number of inputs in the zkSNARK sense, i.e., input variables + output variables
    //     let num_inputs = args_provided.len() + 1; //currently exactly one output variable
    //     println!("run_libsnark = {:?}", run_libsnark(variables, a, b, c, witness, num_inputs));
    // }
}

#[cfg(test)]
mod tests {
    extern crate glob;
    use super::*;
    use num::Zero;
    use self::glob::glob;

    #[test]
    fn examples() {
        for p in glob("./examples/*.code").expect("Failed to read glob pattern") {
            let path = match p {
                Ok(x) => x,
                Err(why) => panic!("Error: {:?}", why),
            };
            println!("Testing {:?}", path);
            let file = match File::open(&path) {
                Ok(file) => file,
                Err(why) => panic!("couldn't open {:?}: {}", path, why),
            };

            let program_ast = match parse_program::<FieldPrime>(file) {
                Ok(x) => x,
                Err(why) => panic!("Error: {:?}", why),
            };
            let program_flattened = Flattener::new(FieldPrime::get_required_bits()).flatten_program(program_ast);
            let (..) = r1cs_program(&program_flattened);
        }
    }

    #[test]
    fn examples_with_input() {
        for p in glob("./examples/test*.code").expect("Failed to read glob pattern") {
            let path = match p {
                Ok(x) => x,
                Err(why) => panic!("Error: {:?}", why),
            };
            println!("Testing {:?}", path);
            let file = match File::open(&path) {
                Ok(file) => file,
                Err(why) => panic!("couldn't open {:?}: {}", path, why),
            };

            let program_ast = match parse_program::<FieldPrime>(file) {
                Ok(x) => x,
                Err(why) => panic!("Error: {:?}", why),
            };
            let program_flattened = Flattener::new(FieldPrime::get_required_bits()).flatten_program(program_ast);
            let (..) = r1cs_program(&program_flattened);
            let _ = program_flattened.get_witness(vec![FieldPrime::zero()]);
        }
    }
}
