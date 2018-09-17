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
	Boolean,
	Array(usize, Box<Type>),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    	match *self {
    		Type::FieldElement => write!(f, "field"),
    		Type::Boolean => write!(f, "bool"),
    		Type::Array(size, box t) => write!(f, "{}[{}]", t, size)
    	}
    }
}

impl fmt::Debug for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    	match *self {
    		Type::FieldElement => write!(f, "field"),
    		Type::Boolean => write!(f, "bool"),
    		Type::Array(size, box t) => write!(f, "{}[{}]", t, size),
    	}
    }
}

impl Type {
	fn get_constraints<T: Field>(&self) -> Constraints<T> {
		match self {
			Type::FieldElement => Constraints::none(),
			Type::Boolean => Constraints::boolean(),
			Type::Array(_, box t) => t.get_constraints(),
		}
	}

	// the number of field elements the type maps to
	pub fn get_primitive_count(&self) -> usize {
		match self {
			Type::FieldElement => 1,
			Type::Boolean => 1,
			Type::Array(size, box t) => size * t.get_primitive_count(),
		}
	}

	fn to_slug(&self) -> &'static str {
		match *self {
			Type::FieldElement => "f",
			Type::Boolean => "b",
			Type::Array(..) => "[]", // TODO differentiate types?
		}
	}
}

#[cfg(test)]
mod tests {
	use field::FieldPrime;
	use super::*;

	#[test]
	fn array() {
		let t = Type::Array(42, box Type::FieldElement);
		assert_eq!(t.get_primitive_count(), 1);
		assert_eq!(t.get_constraints::<FieldPrime>(), Constraints::none());
		assert_eq!(t.to_slug(), "[]");
	}

	#[test]
	fn array_of_arrays() {
		let t = Type::Array(42, box Type::Array(33, box Type::Boolean));
		assert_eq!(t.get_primitive_count(), 1);
		assert_eq!(t.get_constraints::<FieldPrime>(), Constraints::boolean());
		assert_eq!(t.to_slug(), "[]");
	}
}