use libsnark::{get_sha256_witness, get_ethsha256_witness};
use serde_json;
use standard;
use std::fmt;
use field::{Field};
use helpers::{Signed, Executable};

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub enum LibsnarkGadgetHelper {
	Sha256Compress,
	Sha256Ethereum,
}

impl fmt::Display for LibsnarkGadgetHelper {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    	match *self {
    		LibsnarkGadgetHelper::Sha256Compress => write!(f, "Sha256Compress"),
			LibsnarkGadgetHelper::Sha256Ethereum => write!(f, "Sha256Etherem"),
    	}
    }
}

impl<T: Field> Executable<T> for LibsnarkGadgetHelper {
	fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, String> {
		match self {
			LibsnarkGadgetHelper::Sha256Compress => {
				let witness_result: Result<standard::Witness, serde_json::Error> = serde_json::from_str(&get_sha256_witness(inputs));

				if let Err(e) = witness_result {
					return Err(format!("{}", e));
				}

				Ok(witness_result.unwrap().variables.iter().map(|&i| T::from(i)).collect())
			},
			LibsnarkGadgetHelper::Sha256Ethereum => {
				let witness_result: Result<standard::Witness, serde_json::Error> = serde_json::from_str(&get_ethsha256_witness(inputs));

				if let Err(e) = witness_result {
					return Err(format!("{}", e));
				}

				Ok(witness_result.unwrap().variables.iter().map(|&i| T::from(i)).collect())
			},
		}
	}
}

impl Signed for LibsnarkGadgetHelper {
	fn get_signature(&self) -> (usize, usize) {
		match self {
			LibsnarkGadgetHelper::Sha256Compress => (512, 25561),
			LibsnarkGadgetHelper::Sha256Ethereum => (512, 50610),
		}
	}
}