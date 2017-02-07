#![feature(box_patterns, box_syntax)]
/**
 * @file main.rs
 * @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
 * @date 2017
 */

mod absy;
mod parser;
mod flatten;
mod r1cs;
#[cfg(not(feature="nolibsnark"))]
mod libsnark;

use std::fs::File;
use std::path::Path;
use parser::parse_program;
use flatten::flatten_program;
use r1cs::*;
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
    let program_flattened = flatten_program(program_ast);
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
    let inputs: Vec<i32> = args[2].split_whitespace().flat_map(|x| x.parse::<i32>()).collect();
    assert!(inputs.len() == program_flattened.arguments.len());
    println!("inputs {:?}", inputs);
    let witness_map = program_flattened.get_witness(inputs);
    println!("witness_map {:?}", witness_map);
    let witness: Vec<_> = variables.iter().map(|x| witness_map[x]).collect();
    println!("witness {:?}", witness);
    #[cfg(not(feature="nolibsnark"))]
    println!("run_libsnark = {:?}", run_libsnark(variables, a, b, c, witness));
}
