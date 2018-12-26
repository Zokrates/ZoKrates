use std::fmt;
use types::constraints::Constraints;
pub use types::signature::Signature;
use zokrates_field::field::Field;

mod constraints;
pub mod conversions;
mod signature;

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Type {
    FieldElement,
    Boolean,
    FieldElementArray(usize),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Type::FieldElement => write!(f, "field"),
            Type::Boolean => write!(f, "bool"),
            Type::FieldElementArray(size) => write!(f, "{}[{}]", Type::FieldElement, size),
        }
    }
}

impl fmt::Debug for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Type::FieldElement => write!(f, "field"),
            Type::Boolean => write!(f, "bool"),
            Type::FieldElementArray(size) => write!(f, "{}[{}]", Type::FieldElement, size),
        }
    }
}

impl Type {
    fn get_constraints<T: Field>(&self) -> Constraints<T> {
        match self {
            Type::FieldElement => Constraints::none(),
            Type::Boolean => Constraints::boolean(),
            Type::FieldElementArray(_) => Type::FieldElement.get_constraints(),
        }
    }

    // the number of field elements the type maps to
    pub fn get_primitive_count(&self) -> usize {
        match self {
            Type::FieldElement => 1,
            Type::Boolean => 1,
            Type::FieldElementArray(size) => size * Type::FieldElement.get_primitive_count(),
        }
    }

    fn to_slug(&self) -> String {
        match *self {
            Type::FieldElement => String::from("f"),
            Type::Boolean => String::from("b"),
            Type::FieldElementArray(size) => format!("{}[{}]", Type::FieldElement.to_slug(), size), // TODO differentiate types?
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn array() {
        let t = Type::FieldElementArray(42);
        assert_eq!(t.get_primitive_count(), 42);
        assert_eq!(t.get_constraints::<FieldPrime>(), Constraints::none());
        assert_eq!(t.to_slug(), "f[42]");
    }

    // #[test]
    // fn array_of_arrays() {
    // 	let t = Type::FieldElementArray(42, box Type::FieldElementArray(33, box Type::Boolean));
    // 	assert_eq!(t.get_primitive_count(), 1);
    // 	assert_eq!(t.get_constraints::<FieldPrime>(), Constraints::boolean());
    // 	assert_eq!(t.to_slug(), "[]");
    // }
}
