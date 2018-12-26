use zokrates_field::field::Field;

#[derive(PartialEq, PartialOrd, Clone, Eq, Ord, Debug)]
pub struct Constraints<T: Field> {
    pub constraints: Vec<Constraint<T>>,
}

impl<T: Field> Constraints<T> {
    pub fn none() -> Constraints<T> {
        Constraints {
            constraints: vec![],
        }
    }
    pub fn boolean() -> Constraints<T> {
        Constraints {
            constraints: vec![Constraint {
                a: box [T::from(1)],
                b: box [T::from(1)],
                c: box [T::from(1)],
            }],
        }
    }
}

#[derive(PartialEq, PartialOrd, Clone, Eq, Ord, Debug)]
pub struct Constraint<T: Field> {
    pub a: Box<[T]>,
    pub b: Box<[T]>,
    pub c: Box<[T]>,
}
