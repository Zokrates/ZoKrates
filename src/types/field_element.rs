use field::Field;
use types::constraints::Constraints;
use types::{Type, Typed};

pub struct FieldElement<T: Field> {
	elements: [T; 1],
}

impl<T: Field> FieldElement<T> {
	fn unpack(&self) -> [T; 1] {
		self.elements.clone()
	}
}

impl<T: Field> Typed<T> for FieldElement<T> {
	fn get_constraints(&self) -> Constraints<T> {
		self.get_type().get_constraints()
	}

	fn get_type(&self) -> Type {
		Type::FieldElement
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use field::FieldPrime;

	#[test]
	fn forty_two() {
		let e = FieldElement {
			elements: [FieldPrime::from(42)]
		};
		assert_eq!(e.elements.len(), 1);
		assert_eq!(e.elements[0], FieldPrime::from(42));
		assert_eq!(e.get_constraints().constraints.len(), 0);
	}
}