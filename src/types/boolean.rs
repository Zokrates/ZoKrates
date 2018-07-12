use field::Field;
use types::constraints::{Constraints, Constraint};
use types::{Type, Typed};
use types::{CheckedFunction, Signature};

#[derive(PartialEq, PartialOrd, Clone, Eq, Ord, Debug)]
pub struct Boolean<T: Field> {
	elements: [T; 1],
}

impl<T: Field> Boolean<T> {
	fn b_false() -> Boolean<T> {
		Boolean {
			elements: [T::zero()],
		}
	}

	fn b_true() -> Boolean<T> {
		Boolean {
			elements: [T::one()],
		}
	}
}

impl<T: Field> Typed<T> for Boolean<T> {
	fn get_constraints(&self) -> Constraints<T> {
		self.get_type().get_constraints()
	}

	fn get_type(&self) -> Type {
		Type::Boolean
	}
}

pub fn AND<T: Field>() -> CheckedFunction<T> {
	CheckedFunction {
		id: "AND".to_string(),
		signature: Signature {
			inputs: vec![Type::Boolean, Type::Boolean],
			outputs: vec![Type::Boolean]
		},
		input_wires: vec![0, 1],
		output_wires: vec![2],
		assertions: Constraints {
			constraints: vec![
				Constraint { 
					a: Box::new([T::one(), T::zero(), T::zero()]),
					b: Box::new([T::zero(), T::one(), T::zero()]),
					c: Box::new([T::zero(), T::zero(), T::one()])
				}
			]
		},
	}
}

pub fn XOR<T: Field>() -> CheckedFunction<T> {
	CheckedFunction {
		id: "AND".to_string(),
		signature: Signature {
			inputs: vec![Type::Boolean, Type::Boolean],
			outputs: vec![Type::Boolean]
		},
		input_wires: vec![0, 1],
		output_wires: vec![2],
		assertions: Constraints {
			constraints: vec![
				Constraint { 
					a: Box::new([T::from(2), T::zero(), T::zero()]),
					b: Box::new([T::zero(), T::one(), T::zero()]),
					c: Box::new([T::from(-1), T::from(-1), T::one()])
				}
			]
		},
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use field::FieldPrime;

	#[test]
	fn b_false() {
		let b: Boolean<FieldPrime> = Boolean::b_false();
		assert_eq!(b.elements.len(), 1);
		assert_eq!(b.elements[0], FieldPrime::from(0));
		assert_eq!(b.get_constraints().constraints.len(), 1);
		assert_eq!(b.get_constraints().constraints[0].a.len(), 1);
		assert_eq!(b.get_constraints().constraints[0].b.len(), 1);
		assert_eq!(b.get_constraints().constraints[0].c.len(), 1);
		assert_eq!(b.get_constraints().constraints[0].a[0], FieldPrime::from(1));
		assert_eq!(b.get_constraints().constraints[0].b[0], FieldPrime::from(1));
		assert_eq!(b.get_constraints().constraints[0].c[0], FieldPrime::from(1));
	}


	#[test]
	fn b_true() {
		let b: Boolean<FieldPrime> = Boolean::b_true();
		assert_eq!(b.elements.len(), 1);
		assert_eq!(b.elements[0], FieldPrime::from(1));
		assert_eq!(b.get_constraints().constraints.len(), 1);
		assert_eq!(b.get_constraints().constraints[0].a.len(), 1);
		assert_eq!(b.get_constraints().constraints[0].b.len(), 1);
		assert_eq!(b.get_constraints().constraints[0].c.len(), 1);
		assert_eq!(b.get_constraints().constraints[0].a[0], FieldPrime::from(1));
		assert_eq!(b.get_constraints().constraints[0].b[0], FieldPrime::from(1));
		assert_eq!(b.get_constraints().constraints[0].c[0], FieldPrime::from(1));
	}

	#[test]
	fn and() {
		let AND: CheckedFunction<FieldPrime> = AND();
		let cs = AND.to_r1cs();
		assert_eq!(cs.constraints.len(), 1);
		assert_eq!(cs.constraints[0].a.len(), 3);
	}

	#[test]
	fn xor() {
		let XOR: CheckedFunction<FieldPrime> = XOR();
		let cs = XOR.to_r1cs();
		assert_eq!(cs.constraints.len(), 1);
		assert_eq!(cs.constraints[0].a.len(), 3);
	}
}