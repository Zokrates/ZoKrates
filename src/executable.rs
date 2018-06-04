//! Representation of a function that can run in any context (for example in libsnark)
//!
//! @file lambda.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use libsnark::*;
use field::Field;
use std::collections::{BTreeMap};
use r1cs;
use serde_json;
use standard;

#[derive(Serialize, Deserialize, Clone, PartialEq, Debug)]
pub struct Sha256Libsnark {
}

impl<T: Field> Executable<T> for Sha256Libsnark {
	fn get_signature(&self) -> (usize, usize) {
		(512, 256)
	}
	fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, ()> {
		assert!(inputs.len() == 512);
		let witness: standard::Witness = serde_json::from_str(&get_sha256_witness(inputs)).unwrap();
		Ok(witness.TestVariables.iter().map(|&i| T::from(i)).collect())
	}
}

pub trait Executable<T: Field> {
	fn get_signature(&self) -> (usize, usize);
	fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, ()>;
}

mod tests {
	use super::*;
	use field::FieldPrime;

	#[test]
	fn execute_sha() {
		let sha = Sha256Libsnark { };
		let r = sha.execute(&[0; 512].iter().map(|&i| FieldPrime::from(i)).collect());
		println!("{:?}", r);
	}
}