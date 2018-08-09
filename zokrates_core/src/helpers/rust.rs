use std::fmt;
use helpers::{Signed, Executable};
use field::{Field};

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

impl Signed for RustHelper {
	fn get_signature(&self) -> (usize, usize) {
		match self {
			RustHelper::Identity => (1, 1),
			RustHelper::ConditionEq => (1, 2),
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