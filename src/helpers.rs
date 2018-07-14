use std::fmt;
use field::{Field};

#[cfg(not(feature = "nolibsnark"))]
use libsnark::*;

use serde_json;
use standard;

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub struct DirectiveStatement {
	pub inputs: Vec<String>,
	pub outputs: Vec<String>,
	pub helper: Helper
}

impl fmt::Display for DirectiveStatement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    	write!(f, "# {} = {}({})", self.outputs.join(", "), self.helper, self.inputs.join(", "))
    }
}

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub enum Helper {
	LibsnarkGadget(LibsnarkGadgetHelper),
	Rust(RustHelper)
}

impl fmt::Display for Helper {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    	match *self {
    		Helper::LibsnarkGadget(ref h) => write!(f, "LibsnarkGadget::{}", h),
    		Helper::Rust(ref h) => write!(f, "Rust::{}", h)
    	}
    }
}

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub enum LibsnarkGadgetHelper {
	Sha256Compress,
}

impl fmt::Display for LibsnarkGadgetHelper {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    	match *self {
    		LibsnarkGadgetHelper::Sha256Compress => write!(f, "Sha256Compress"),
    	}
    }
}

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub enum RustHelper {
	Identity,
	ConditionEq,
}

impl fmt::Display for RustHelper {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    	match *self {
    		RustHelper::Identity => write!(f, "Identity"),
    		RustHelper::ConditionEq => write!(f, "ConditionEq"),
    	}
    }
}

pub trait Executable<T: Field>
	: Signed {
	fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, String>;
}

pub trait Signed {
	fn get_signature(&self) -> (usize, usize);
}

impl<T: Field> Executable<T> for LibsnarkGadgetHelper {
	fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, String> {
		match self {
			LibsnarkGadgetHelper::Sha256Compress => {
				#[cfg(feature = "nolibsnark")]
				{
					Err(format!("Libsnark is not available"))
				}

				#[cfg(not(feature = "nolibsnark"))]
				{
					let witness_result: Result<standard::Witness, serde_json::Error> = serde_json::from_str(&get_sha256_witness(inputs));

					if let Err(e) = witness_result {
						return Err(format!("{}", e));
					}

					Ok(witness_result.unwrap().variables.iter().map(|&i| T::from(i)).collect())
				}
			},
		}
	}
}

impl Signed for LibsnarkGadgetHelper {
	fn get_signature(&self) -> (usize, usize) {
		match self {
			LibsnarkGadgetHelper::Sha256Compress => (512, 25561),
		}
	}
}

impl<T: Field> Executable<T> for RustHelper {
	fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, String> {
		match self {
			RustHelper::Identity => Ok(inputs.clone()),
			RustHelper::ConditionEq => {
				match inputs[0].is_zero() {
					true => Ok(vec![T::zero(), T::one()]),
					false => Ok(vec![T::one(), T::one() / inputs[0].clone()])
				}
			},
		}
	}
}

impl Signed for RustHelper {
	fn get_signature(&self) -> (usize, usize) {
		match self {
			RustHelper::Identity => (1, 1),
			RustHelper::ConditionEq => (1, 2),
		}
	}
}

impl<T: Field> Executable<T> for Helper {
	fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, String> {
		let (expected_input_count, expected_output_count) = self.get_signature();
		assert!(inputs.len() == expected_input_count);

		let result = match self {
			Helper::LibsnarkGadget(helper) => helper.execute(inputs),
			Helper::Rust(helper) => helper.execute(inputs)
		};

		match result {
			Ok(ref r) if r.len() != expected_output_count => Err(format!("invalid witness size: is {} but should be {}", r.len(), expected_output_count).to_string()),
			r => r
		}
	}
}

impl Signed for Helper {
	fn get_signature(&self) -> (usize, usize) {
		match self {
			Helper::LibsnarkGadget(helper) => helper.get_signature(),
			Helper::Rust(helper) => helper.get_signature()
		}
	}
}

#[cfg(test)]
mod tests {
	use field::FieldPrime;
	use super::*;

	mod sha256libsnark {
		use super::*;

		#[test]
		fn execute() {
			let sha = LibsnarkGadgetHelper::Sha256Compress;
			// second vector here https://homes.esat.kuleuven.be/~nsmart/MPC/sha-256-test.txt
			let inputs = vec![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,1,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,1,1,0,0,0,0,0,0,1,1,1,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,1,0,1,0,0,0,0,0,1,0,1,1,0,0,0,0,1,1,0,0,0,0,0,0,1,1,0,1,0,0,0,0,1,1,1,0,0,0,0,0,1,1,1,1,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,1,0,0,1,0,0,0,0,1,0,0,1,1,0,0,0,1,0,1,0,0,0,0,0,1,0,1,0,1,0,0,0,1,0,1,1,0,0,0,0,1,0,1,1,1,0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,1,0,0,0,1,1,0,1,0,0,0,0,1,1,0,1,1,0,0,0,1,1,1,0,0,0,0,0,1,1,1,0,1,0,0,0,1,1,1,1,0,0,0,0,1,1,1,1,1,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,1,0,0,1,0,0,1,0,0,0,0,1,0,0,1,0,1,0,0,1,0,0,1,1,0,0,0,1,0,0,1,1,1,0,0,1,0,1,0,0,0,0,0,1,0,1,0,0,1,0,0,1,0,1,0,1,0,0,0,1,0,1,0,1,1,0,0,1,0,1,1,0,0,0,0,1,0,1,1,0,1,0,0,1,0,1,1,1,0,0,0,1,0,1,1,1,1,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,1,0,0,1,1,0,0,1,0,0,0,1,1,0,0,1,1,0,0,1,1,0,1,0,0,0,0,1,1,0,1,0,1,0,0,1,1,0,1,1,0,0,0,1,1,0,1,1,1,0,0,1,1,1,0,0,0,0,0,1,1,1,0,0,1,0,0,1,1,1,0,1,0,0,0,1,1,1,0,1,1,0,0,1,1,1,1,0,0,0,0,1,1,1,1,0,1,0,0,1,1,1,1,1,0,0,0,1,1,1,1,1,1];
			let r = sha.execute(&inputs.iter().map(|&i| FieldPrime::from(i)).collect()).unwrap();
			let r1 = &r[513..769]; // index of the result
			let res: Vec<FieldPrime> = vec![1,1,1,1,1,1,0,0,1,0,0,1,1,0,0,1,1,0,1,0,0,0,1,0,1,1,0,1,1,1,1,1,1,0,0,0,1,0,0,0,1,1,1,1,0,1,0,0,0,0,1,0,1,0,1,0,0,1,1,1,1,0,1,0,0,1,1,1,1,0,1,1,1,0,1,1,1,0,0,1,1,1,0,1,0,0,0,1,1,0,0,0,0,0,0,0,0,0,1,1,0,0,1,1,1,1,0,0,1,1,0,1,1,1,0,0,0,1,1,0,1,0,1,0,0,0,1,0,0,0,0,0,0,0,1,0,0,1,0,1,0,1,1,0,0,1,1,1,0,1,0,1,0,1,0,1,1,1,1,1,1,0,0,1,1,1,0,1,0,1,0,1,1,0,1,1,1,0,0,1,1,0,1,0,0,1,0,1,0,0,0,0,0,1,0,0,0,1,0,0,1,0,1,0,1,0,0,1,1,1,0,0,1,1,0,0,0,0,1,1,0,0,0,1,0,1,0,1,1,0,1,0,1,0,1,1,1,1,1,0,1,0,0,0,0,1,0,0,1,0,1,0,0,1,1,1].iter().map(|&i| FieldPrime::from(i)).collect();
			assert_eq!(r1, &res[..]);
		}
	}


	mod eq_condition {

		// Wanted: (Y = (X != 0) ? 1 : 0)
        // # Y = if X == 0 then 0 else 1 fi
        // # M = if X == 0 then 1 else 1/X fi

		use super::*;

		#[test]
		fn execute() {
			let cond_eq = RustHelper::ConditionEq;
			let inputs = vec![0];
			let r = cond_eq.execute(&inputs.iter().map(|&i| FieldPrime::from(i)).collect()).unwrap();
			let res: Vec<FieldPrime> = vec![0, 1].iter().map(|&i| FieldPrime::from(i)).collect();
			assert_eq!(r, &res[..]);
		}

		#[test]
		fn execute_non_eq() {
			let cond_eq = RustHelper::ConditionEq;
			let inputs = vec![1];
			let r = cond_eq.execute(&inputs.iter().map(|&i| FieldPrime::from(i)).collect()).unwrap();
			let res: Vec<FieldPrime> = vec![1, 1].iter().map(|&i| FieldPrime::from(i)).collect();
			assert_eq!(r, &res[..]);
		}
	}
}



