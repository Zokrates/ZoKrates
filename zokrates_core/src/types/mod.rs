use field::Field;
use types::constraints::Constraints;
use std::fmt;

pub mod signature;
pub mod conversions;
mod constraints;

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Type {
	FieldElement,
	Boolean,
	Unsigned8
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    	write!(f, "{:?}", self)
    }
}

impl fmt::Debug for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    	match *self {
    		Type::FieldElement => write!(f, "field"),
    		Type::Boolean => write!(f, "bool"),
    		Type::Unsigned8 => write!(f, "uint8")
    	}
    }
}

impl Type {
	fn get_constraints<T: Field>(&self) -> Constraints<T> {
		match self {
			Type::FieldElement => Constraints::none(),
			Type::Boolean => Constraints::boolean(),
			Type::Unsigned8 => Constraints::unsigned(8),
		}
	}

	// the number of field elements the type maps to
	pub fn get_primitive_count(&self) -> usize {
		match self {
			Type::FieldElement => 1,
			Type::Boolean => 1,
			Type::Unsigned8 => 8,
		}
	}
}
