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
	pub fn boolean() -> Constraints<T> {
		Constraints {
			constraints: vec![
				Constraint {
					a: box [T::from(1)],
					b: box [T::from(1)],
					c: box [T::from(1)],
				}
			]
		}
	}
	pub fn unsigned(size: usize) -> Constraints<T> {
		Constraints {
			constraints: (0..size).enumerate().map(|i|
				Constraint {
					a: (0..size).enumerate().map(|j| if j == i {1} else {0}).map(|r| T::from(r)).collect::<Vec<T>>().into_boxed_slice(),
					b: (0..size).enumerate().map(|j| if j == i {1} else {0}).map(|r| T::from(r)).collect::<Vec<T>>().into_boxed_slice(),
					c: (0..size).enumerate().map(|j| if j == i {1} else {0}).map(|r| T::from(r)).collect::<Vec<T>>().into_boxed_slice(),
				}
			).collect()
		}
	}
}

#[derive(PartialEq, PartialOrd, Clone, Eq, Ord, Debug)]
pub struct Constraint<T: Field> {
	pub a: Box<[T]>,
	pub b: Box<[T]>,
	pub c: Box<[T]>,
}
