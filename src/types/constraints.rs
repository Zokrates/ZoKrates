use field::Field;

#[derive(PartialEq, PartialOrd, Clone, Eq, Ord, Debug)]
pub struct Constraints<T: Field> {
	pub constraints: Vec<Constraint<T>>
}

impl<T: Field> Constraints<T> {
	pub fn boolean(size: usize) -> Constraints<T> {

		let constraints: Vec<Constraint<T>> = (0..size).map(|index| Constraint::boolean(size, index)).collect();

		Constraints {
			constraints: constraints
		}
	}

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

impl<T: Field> Constraint<T> {
    fn zero(size: usize) -> Constraint<T> {
        Constraint {
            a: vec![T::zero(); size].into_boxed_slice(),
            b: vec![T::zero(); size].into_boxed_slice(),
            c: vec![T::zero(); size].into_boxed_slice(),
        }
    }

    fn boolean(size: usize, index: usize) -> Constraint<T> {
    	assert!(index < size);

    	let mut a = vec![T::zero(); size];
       	a[index] = T::one();

       	let b = a.clone();
       	let c = a.clone();

        Constraint {
            a: a.into_boxed_slice(),
            b: b.into_boxed_slice(),
            c: c.into_boxed_slice(),
        }
    }
}