#[cfg(feature = "libsnark")]
mod libsnark_gadget;
mod rust;

#[cfg(feature = "libsnark")]
pub use self::libsnark_gadget::LibsnarkGadgetHelper;
pub use self::rust::RustHelper;
use std::fmt;
use field::{Field};
use flat_absy::FlatVariable;


#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub struct DirectiveStatement {
	pub inputs: Vec<FlatVariable>,
	pub outputs: Vec<FlatVariable>,
	pub helper: Helper
}

impl DirectiveStatement {
	pub fn new(outputs: Vec<FlatVariable>, helper: Helper, inputs: Vec<FlatVariable>) -> Self {
		let (in_len, out_len) = helper.get_signature();
		assert_eq!(in_len, inputs.len());
		assert_eq!(out_len, outputs.len());
		DirectiveStatement {
			helper,
			inputs,
			outputs,
		}
	}
}

impl fmt::Display for DirectiveStatement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    	write!(f, "# {} = {}({})",
    		self.outputs.iter().map(|o| o.to_string()).collect::<Vec<String>>().join(", "),
    		self.helper,
    		self.inputs.iter().map(|i| i.to_string()).collect::<Vec<String>>().join(", ")
    	)
    }
}

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub enum Helper {
	#[cfg(feature = "libsnark")]
	LibsnarkGadget(LibsnarkGadgetHelper),
	Rust(RustHelper)
}

impl fmt::Display for Helper {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    	match *self {
    		#[cfg(feature = "libsnark")]
    		Helper::LibsnarkGadget(ref h) => write!(f, "LibsnarkGadget::{}", h),
    		Helper::Rust(ref h) => write!(f, "Rust::{}", h)
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

impl<T: Field> Executable<T> for Helper {
	fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, String> {
		let (expected_input_count, expected_output_count) = self.get_signature();
		assert!(inputs.len() == expected_input_count);

		let result = match self {
			#[cfg(feature = "libsnark")]
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
			#[cfg(feature = "libsnark")]
			Helper::LibsnarkGadget(helper) => helper.get_signature(),
			Helper::Rust(helper) => helper.get_signature()
		}
	}
}

#[cfg(test)]
mod tests {
	use field::FieldPrime;
	use super::*;

	#[cfg(feature = "libsnark")]
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



