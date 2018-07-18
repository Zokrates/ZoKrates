use field::Field;
use types::constraints::Constraints;
use std::string::String;
use std::fmt;

pub mod field_element;
pub mod signature;
mod constraints;

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Debug)]
pub enum Type {
	FieldElement
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    	match *self {
    		Type::FieldElement => write!(f, "field"),
    	}
    }
}

impl Type {
	fn get_constraints<T: Field>(&self) -> Constraints<T> {
		match self {
			Type::FieldElement => Constraints::none(),
		}
	}

	fn get_primitive_count(&self) -> usize {
		match self {
			Type::FieldElement => 1,
		}
	}
}

trait Typed<T: Field> {
	fn get_constraints(&self) -> Constraints<T>;
	fn get_type(&self) -> Type;
}
