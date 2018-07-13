use field::Field;

#[derive(PartialEq, PartialOrd, Clone, Eq, Ord, Debug)]
pub struct Constraints<T: Field> {
	pub constraints: Vec<Constraint<T>>
}

impl<T: Field> Constraints<T> {
	pub fn none() -> Constraints<T> {
		Constraints {
			constraints: vec![]
		}
	}
}

#[derive(PartialEq, PartialOrd, Clone, Eq, Ord, Debug)]
pub struct Constraint<T: Field> {
	pub a: Box<[T]>,
	pub b: Box<[T]>,
	pub c: Box<[T]>,
}
