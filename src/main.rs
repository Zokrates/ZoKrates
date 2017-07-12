//
// @file main.rs
// @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
// @date 2017

#![feature(box_patterns, box_syntax)]

#[macro_use]
extern crate lazy_static;
extern crate num;

mod absy;
mod parser;
mod flatten;
mod r1cs;
mod field;
#[cfg(not(feature="nolibsnark"))]
mod libsnark;

use std::fs::File;
use std::path::Path;
use field::{Field, FieldPrime};
use parser::parse_program;
use flatten::Flattener;
use r1cs::r1cs_program;
#[cfg(not(feature="nolibsnark"))]
use libsnark::run_libsnark;

fn main() {
    let args: Vec<_> = std::env::args().collect();
    assert!(args.len() == 2 || args.len() == 3);

    let path = Path::new(&args[1]);
    let file = match File::open(&path) {
        Ok(file) => file,
        Err(why) => panic!("couldn't open {}: {}", path.display(), why),
    };

    let program_ast = match parse_program(file) {
        Ok(x) => x,
        Err(why) => {
            println!("{:?}", why);
            std::process::exit(1);
        },
    };
    println!("program:\n{}", program_ast);
    let program_flattened = Flattener::new(FieldPrime::get_required_bits()).flatten_program(program_ast);
    println!("flattened:\n{}", program_flattened);
    let (variables, a, b, c) = r1cs_program(&program_flattened);
    println!("variables {:?}", variables);
    println!("A");
    for x in &a {
        println!("{:?}", x);
    }
    println!("B");
    for x in &b {
        println!("{:?}", x);
    }
    println!("C");
    for x in &c {
        println!("{:?}", x);
    }

    // calculate witness if wanted
    if args.len() < 3 {
        std::process::exit(0);
    }

    // check #inputs
    let inputs: Vec<FieldPrime> = args[2].split_whitespace().map(|x| FieldPrime::from(x)).collect();
    let args_provided = &program_flattened.functions.iter().find(|x| x.id=="main").unwrap().arguments;
    assert!(inputs.len() == args_provided.len(),"Wrong number of arguments provided for main function. Provided: {}, Expected: {}.", inputs.len(), args_provided.len());
    println!("inputs {:?}", inputs);

    // generate wittness
    let witness_map = program_flattened.get_witness(inputs);
    println!("witness_map {:?}", witness_map);
    match witness_map.get("~out") {
        Some(out) => println!("~out: {}", out),
        None => println!("~out not found")
    }
    let witness: Vec<_> = variables.iter().map(|x| witness_map[x].clone()).collect();
    println!("witness {:?}", witness);

    // run libsnark
    #[cfg(not(feature="nolibsnark"))]
    // number of inputs in the zkSNARK sense, i.e., input variables + output variables
    let num_inputs = args_provided.len() + 1; //currently exactly one output variable
    println!("run_libsnark = {:?}", run_libsnark(variables, a, b, c, witness, num_inputs));
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
