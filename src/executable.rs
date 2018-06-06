//! Representation of a function that can run in any context (for example in libsnark)
//!
//! @file lambda.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use libsnark::*;
use field::Field;
use serde_json;
use standard;

#[derive(Serialize, Deserialize, Clone, PartialEq, Debug)]
pub struct Sha256Libsnark {
	input_count: usize,
	output_count: usize
}

impl Sha256Libsnark {
	pub fn new(input_count: usize, output_count: usize) -> Sha256Libsnark {
		Sha256Libsnark {
			input_count,
			output_count
		}
	}
}

impl<T: Field> Executable<T> for Sha256Libsnark {
	fn get_signature(&self) -> (usize, usize) {
		(self.input_count, self.output_count)
	}
	fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, String> {
		let (expected_input_count, expected_output_count) = (self as &Executable<T>).get_signature();
		assert!(inputs.len() == expected_input_count);
		let witness: standard::Witness = serde_json::from_str(&get_sha256_witness(inputs)).unwrap();
		let res: Vec<T> = witness.variables.iter().map(|&i| T::from(i)).collect();

		match res.len() {
			l if l == expected_output_count => Ok(res),
			_ => {
				Err(format!("invalid witness size: is {} but should be {}", res.len(), expected_output_count).to_string())
			}
		}
	}
}

pub trait Executable<T: Field> {
	fn get_signature(&self) -> (usize, usize);
	fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, String>;
}

#[cfg(test)]
mod tests {
	use field::FieldPrime;
	use super::*;

	#[test]
	fn execute_sha() {
		let sha = Sha256Libsnark::new(512, 50354);
		let r = sha.execute(&[0; 512].iter().map(|&i| FieldPrime::from(i)).collect());
		println!("{:?}", r);
	}
}