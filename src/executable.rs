//! Representation of a function that can run in any context (for example in libsnark)
//!
//! @file lambda.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use field::Field;
use std::collections::{BTreeMap};

#[derive(Serialize, Deserialize, Clone, PartialEq, Debug)]
pub struct Sha256Libsnark {
	
}

impl<T: Field> Executable<T> for Sha256Libsnark {
	fn get_signature(&self) -> (usize, usize) {
		(512, 256)
	}
	fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, ()> {
		Ok(vec![T::from(0); 256])
	}
}

pub trait Executable<T: Field> {
	fn get_signature(&self) -> (usize, usize);
	fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, ()>;
}