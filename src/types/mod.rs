use field::Field;
use types::constraints::Constraints;
use std::string::String;

mod boolean;
pub mod field_element;
mod constraints;

pub enum Type {
	FieldElement,
	Boolean
}

impl Type {
	fn get_constraints<T: Field>(&self) -> Constraints<T> {
		match self {
			Type::FieldElement => Constraints::none(),
			Type::Boolean => Constraints::boolean(1)
		}
	}

	fn get_primitive_count(&self) -> usize {
		match self {
			FieldElement => 1,
			Boolean => 1
		}
	}
}

trait Typed<T: Field> {
	fn get_constraints(&self) -> Constraints<T>;
	fn get_type(&self) -> Type;
}

pub struct CheckedFunction<T: Field> {
	id: String,
	signature: Signature,
	input_wires: Vec<usize>,
	output_wires: Vec<usize>,
	assertions: Constraints<T>,
}

impl<T: Field> CheckedFunction<T> {
	fn to_r1cs(&self) -> Constraints<T> {
		let mut constraints = vec![];
		
		// input type checking
		// TODO

		// assertions
		constraints.extend(self.assertions.constraints.clone());

		// output type checking
		// TODO

		Constraints {
			constraints: constraints
		}
	}
}

pub struct Signature {
	inputs: Vec<Type>,
	outputs: Vec<Type>
}
