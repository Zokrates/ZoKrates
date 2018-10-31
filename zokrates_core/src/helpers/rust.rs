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

#[cfg(test)]
mod tests {
	use field::FieldPrime;
	use super::*;

	#[test]
	fn bits_of_one() {
		let inputs = vec![FieldPrime::from(1)];
		let res = RustHelper::Bits.execute(&inputs).unwrap();
		assert_eq!(res[253], FieldPrime::from(1));
		for i in 0..252 {
			assert_eq!(res[i], FieldPrime::from(0));
		}
	}

	#[test]
	fn bits_of_42() {
		let inputs = vec![FieldPrime::from(42)];
		let res = RustHelper::Bits.execute(&inputs).unwrap();
		assert_eq!(res[253], FieldPrime::from(0));
		assert_eq!(res[252], FieldPrime::from(1));
		assert_eq!(res[251], FieldPrime::from(0));
		assert_eq!(res[250], FieldPrime::from(1));
		assert_eq!(res[249], FieldPrime::from(0));
		assert_eq!(res[248], FieldPrime::from(1));
		assert_eq!(res[247], FieldPrime::from(0));
	}
}