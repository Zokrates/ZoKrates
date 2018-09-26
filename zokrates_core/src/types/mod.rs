use field::Field;
use types::constraints::Constraints;
use std::fmt;
pub use types::signature::Signature;

mod signature;
pub mod conversions;
mod constraints;

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Type {
	FieldElement,
	Boolean
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    	match *self {
    		Type::FieldElement => write!(f, "field"),
    		Type::Boolean => write!(f, "bool"),
    	}
    }
}

impl fmt::Debug for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    	match *self {
    		Type::FieldElement => write!(f, "field"),
    		Type::Boolean => write!(f, "bool"),
    	}
    }
}

impl Type {
	fn get_constraints<T: Field>(&self) -> Constraints<T> {
		match self {
			Type::FieldElement => Constraints::none(),
			Type::Boolean => Constraints::boolean(),
		}
	}

	// the number of field elements the type maps to
	pub fn get_primitive_count(&self) -> usize {
		match self {
			Type::FieldElement => 1,
			Type::Boolean => 1
		}
	}

	fn to_slug(&self) -> &'static str {
		match *self {
			Type::FieldElement => "f",
			Type::Boolean => "b",
		}
	}
}
