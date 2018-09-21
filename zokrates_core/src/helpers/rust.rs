use std::fmt;
use helpers::{Signed, Executable};
use field::{Field};

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub enum RustHelper {
	Identity,
	ConditionEq,
	Bits,
}

impl fmt::Display for RustHelper {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    	match *self {
    		RustHelper::Identity => write!(f, "Identity"),
    		RustHelper::ConditionEq => write!(f, "ConditionEq"),
    		RustHelper::Bits => write!(f, "Bits"),
    	}
    }
}

impl Signed for RustHelper {
	fn get_signature(&self) -> (usize, usize) {
		match self {
			RustHelper::Identity => (1, 1),
			RustHelper::ConditionEq => (1, 2),
			RustHelper::Bits => (1, 254),
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
			RustHelper::Bits => {
				let mut num = inputs[0].clone();
				let mut res = vec![];
                let bits = 254;
                for i in (0..bits).rev() {
                    if T::from(2).pow(i) <= num {
                        num = num - T::from(2).pow(i);
                        res.push(T::one());
                    } else {
                        res.push(T::zero());
                    }
                }
                assert_eq!(num, T::zero());
                Ok(res)
            }
		}
	}
}