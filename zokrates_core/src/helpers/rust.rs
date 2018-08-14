use std::fmt;
use helpers::{Signed, Executable};
use field::{Field};

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub enum RustHelper {
	Identity,
	ConditionEq,
	FromBits,
	ToBits,
}

impl fmt::Display for RustHelper {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    	match *self {
    		RustHelper::Identity => write!(f, "Identity"),
    		RustHelper::ConditionEq => write!(f, "ConditionEq"),
    		RustHelper::FromBits => write!(f, "FromBits"),
    		RustHelper::ToBits => write!(f, "ToBits"),
    	}
    }
}

impl Signed for RustHelper {
	fn get_signature(&self) -> (usize, usize) {
		match self {
			RustHelper::Identity => (1, 1),
			RustHelper::ConditionEq => (1, 2),
			RustHelper::FromBits => (8, 1),
			RustHelper::ToBits => (1, 8),
		}
	}
}


impl<T: Field> Executable<T> for RustHelper {
	fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, String> {
		let res = match self {
			RustHelper::Identity => inputs.clone(),
			RustHelper::ConditionEq => {
				match inputs[0].is_zero() {
					true => vec![T::zero(), T::one()],
					false => vec![T::one(), T::one() / inputs[0].clone()]
				}
			},
			RustHelper::FromBits => {
				vec![
					inputs
						.iter()
						.rev()
						.enumerate()
						.map(|(i, bit)| T::from(2).pow(i) * bit)
						.fold(T::from(0), |acc, x| acc + x)
				]
			},
			RustHelper::ToBits => {
				let i = inputs[0].into_byte_vector()[0];
				vec![
					i & 0b1000_0000,
					i & 0b0100_0000,
					i & 0b0010_0000,
					i & 0b0001_0000,
					i & 0b0000_1000,
					i & 0b0000_0100,
					i & 0b0000_0010,
					i & 0b0000_0001,
				]
				.into_iter()
				.map(|i| if i == 0 {0} else {1})
				.map(|i| T::from(i as u32))
				.collect()
			}
		};
		Ok(res)
	}
}

#[cfg(test)]
mod test {
	use field::FieldPrime;
	use super::*;

	mod from_bits {
		use super::*;
		#[test]
		fn zero() {
			let h = RustHelper::FromBits;
			let res = h.execute(&vec![0, 0, 0, 0, 0, 0, 0, 0].into_iter().map(|i| FieldPrime::from(i)).collect()).unwrap();
			assert_eq!(res, vec![FieldPrime::from(0)]);
		}

		#[test]
		fn ones() {
			let h = RustHelper::FromBits;
			let res = h.execute(&vec![1, 1, 1, 1, 1, 1, 1, 1].into_iter().map(|i| FieldPrime::from(i)).collect()).unwrap();
			assert_eq!(res, vec![FieldPrime::from(255)]);
		}

		#[test]
		fn forty_two() {
			let h = RustHelper::FromBits;
			let res = h.execute(&vec![0, 0, 1, 0, 1, 0, 1, 0].into_iter().map(|i| FieldPrime::from(i)).collect()).unwrap();
			assert_eq!(res, vec![FieldPrime::from(42)]);
		}
	}

	mod to_bits {
		use super::*;
		#[test]
		fn zero() {
			let h = RustHelper::ToBits;
			let res = h.execute(&vec![FieldPrime::from(0)]).unwrap();
			assert_eq!(res, vec![0, 0, 0, 0, 0, 0, 0, 0].into_iter().map(|i| FieldPrime::from(i)).collect::<Vec<_>>());
		}

		#[test]
		fn ones() {
			let h = RustHelper::ToBits;
			let res = h.execute(&vec![FieldPrime::from(255)]).unwrap();
			assert_eq!(res, vec![1, 1, 1, 1, 1, 1, 1, 1].into_iter().map(|i| FieldPrime::from(i)).collect::<Vec<_>>());
		}

		#[test]
		fn forty_two() {
			let h = RustHelper::ToBits;
			let res = h.execute(&vec![FieldPrime::from(42)]).unwrap();
			assert_eq!(res, vec![0, 0, 1, 0, 1, 0, 1, 0].into_iter().map(|i| FieldPrime::from(i)).collect::<Vec<_>>());
		}

	}
}