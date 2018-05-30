//! Representation of a function that can run in any context (for example in libsnark)
//!
//! @file lambda.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use field::Field;
use absy::*;
use std::collections::{BTreeMap};
use parameter::Parameter;

#[derive(Serialize, Deserialize, Clone, PartialEq, Debug)]
pub struct Zokrates<T: Field> {
	pub function: Function<T>
}

impl<T: Field> Zokrates<T> {
	pub fn new(id: String, expr: Expression<T>, args: Vec<Parameter>) -> Zokrates<T> {
		Zokrates {
			function: Function {
				id: "_internal_".to_string(),
				statements: vec![Statement::Return(ExpressionList {
					expressions: vec![expr]
				})],
				return_count: 1,
				arguments: args
			}
		}
	}
}

impl<T: Field> Executable<T> for Zokrates<T> {
	fn get_signature(&self) -> (usize, usize) {
		(self.function.arguments.len(), self.function.return_count)
	}
	fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, ()> {
		assert!(self.function.statements.len() == 1);
		let mut witness = BTreeMap::new();
        witness.insert("~one".to_string(), T::one());
        for (i, arg) in self.function.arguments.iter().enumerate() {
            witness.insert(arg.id.to_string(), inputs[i].clone());
        }
		match self.function.statements[0] {
			Statement::Return(ref list) => {
				println!("{:?}", list);
                for (i, val) in list.expressions.iter().enumerate() {
                    let s = val.solve(&mut witness);
                    witness.insert(format!("~out_{}", i).to_string(), s);
                }

                println!("{:?}", witness);


                // witness is now full, only keep outputs
                Ok(witness.into_iter().filter_map(|(k, v)| {
                	match k.contains("~out_") {
                		true => Some(v),
                		_ => None
                	}
                }).collect())
            },
			_ => panic!("Zokrates directive should have exactly one Return statement and nothing else")
		}
	}
}

pub trait Executable<T: Field> {
	fn get_signature(&self) -> (usize, usize);
	fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, ()>;
}