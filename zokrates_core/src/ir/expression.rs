use flat_absy::FlatVariable;
use num::Zero;
use std::collections::BTreeMap;
use std::fmt;
use std::ops::{Add, Sub};
use zokrates_field::field::Field;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct QuadComb<T: Field> {
    pub left: LinComb<T>,
    pub right: LinComb<T>,
}

impl<T: Field> QuadComb<T> {
    pub fn from_linear_combinations(left: LinComb<T>, right: LinComb<T>) -> Self {
        QuadComb { left, right }
    }
}

impl<T: Field> From<FlatVariable> for QuadComb<T> {
    fn from(v: FlatVariable) -> QuadComb<T> {
        LinComb::from(v).into()
    }
}

impl<T: Field> fmt::Display for QuadComb<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}) * ({})", self.left, self.right,)
    }
}

impl<T: Field> From<LinComb<T>> for QuadComb<T> {
    fn from(lc: LinComb<T>) -> QuadComb<T> {
        QuadComb::from_linear_combinations(LinComb::one(), lc)
    }
}

#[derive(PartialEq, PartialOrd, Clone, Eq, Ord, Hash, Debug, Serialize, Deserialize)]
pub struct LinComb<T: Field>(pub BTreeMap<FlatVariable, T>);

impl<T: Field> LinComb<T> {
    pub fn summand<U: Into<T>>(mult: U, var: FlatVariable) -> LinComb<T> {
        let mut res = BTreeMap::new();
        res.insert(var, mult.into());
        LinComb(res)
    }

    pub fn one() -> LinComb<T> {
        Self::summand(1, FlatVariable::one())
    }
}

impl<T: Field> fmt::Display for LinComb<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.is_zero() {
            true => write!(f, "0"),
            false => write!(
                f,
                "{}",
                self.0
                    .iter()
                    .map(|(k, v)| format!("{} * {}", v.to_compact_dec_string(), k))
                    .collect::<Vec<_>>()
                    .join(" + ")
            ),
        }
    }
}

impl<T: Field> From<FlatVariable> for LinComb<T> {
    fn from(v: FlatVariable) -> LinComb<T> {
        let mut r = BTreeMap::new();
        r.insert(v, T::one());
        LinComb(r)
    }
}

impl<T: Field> Add<LinComb<T>> for LinComb<T> {
    type Output = LinComb<T>;

    fn add(self, other: LinComb<T>) -> LinComb<T> {
        let mut res = self.0.clone();
        for (k, v) in other.0 {
            let new_val = v + res.get(&k).unwrap_or(&T::zero());
            if new_val == T::zero() {
                res.remove(&k)
            } else {
                res.insert(k, new_val)
            };
        }
        LinComb(res)
    }
}

impl<T: Field> Sub<LinComb<T>> for LinComb<T> {
    type Output = LinComb<T>;

    fn sub(self, other: LinComb<T>) -> LinComb<T> {
        let mut res = self.0.clone();
        for (k, v) in other.0 {
            let new_val = T::zero() - v + res.get(&k).unwrap_or(&T::zero());
            if new_val == T::zero() {
                res.remove(&k)
            } else {
                res.insert(k, new_val)
            };
        }
        LinComb(res)
    }
}

impl<T: Field> Zero for LinComb<T> {
    fn zero() -> LinComb<T> {
        LinComb(BTreeMap::new())
    }
    fn is_zero(&self) -> bool {
        self.0.len() == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    mod linear {

        use super::*;
        #[test]
        fn add_zero() {
            let a: LinComb<FieldPrime> = LinComb::zero();
            let b: LinComb<FieldPrime> = FlatVariable::new(42).into();
            let c = a + b.clone();
            assert_eq!(c, b);
        }
        #[test]
        fn add() {
            let a: LinComb<FieldPrime> = FlatVariable::new(42).into();
            let b: LinComb<FieldPrime> = FlatVariable::new(42).into();
            let c = a + b.clone();
            let mut expected_map = BTreeMap::new();
            expected_map.insert(FlatVariable::new(42), FieldPrime::from(2));
            assert_eq!(c, LinComb(expected_map));
        }
        #[test]
        fn sub() {
            let a: LinComb<FieldPrime> = FlatVariable::new(42).into();
            let b: LinComb<FieldPrime> = FlatVariable::new(42).into();
            let c = a - b.clone();
            assert_eq!(c, LinComb::zero());
        }

        #[test]
        fn display() {
            let a: LinComb<FieldPrime> =
                LinComb::from(FlatVariable::new(42)) + LinComb::summand(3, FlatVariable::new(21));
            assert_eq!(&a.to_string(), "3 * _21 + 1 * _42");
            let zero: LinComb<FieldPrime> = LinComb::zero();
            assert_eq!(&zero.to_string(), "0");
        }
    }

    mod quadratic {
        use super::*;
        #[test]
        fn from_linear() {
            let a: LinComb<FieldPrime> = LinComb::summand(3, FlatVariable::new(42))
                + LinComb::summand(4, FlatVariable::new(33));
            let expected = QuadComb {
                left: LinComb::one(),
                right: a.clone(),
            };
            assert_eq!(QuadComb::from(a), expected);
        }

        #[test]
        fn zero() {
            let a: LinComb<FieldPrime> = LinComb::zero();
            let expected: QuadComb<FieldPrime> = QuadComb {
                left: LinComb::one(),
                right: LinComb::zero(),
            };
            assert_eq!(QuadComb::from(a), expected);
        }

        #[test]
        fn display() {
            let a: QuadComb<FieldPrime> = QuadComb {
                left: LinComb::summand(3, FlatVariable::new(42))
                    + LinComb::summand(4, FlatVariable::new(33)),
                right: LinComb::summand(1, FlatVariable::new(21)),
            };
            assert_eq!(&a.to_string(), "(4 * _33 + 3 * _42) * (1 * _21)");
            let a: QuadComb<FieldPrime> = QuadComb {
                left: LinComb::zero(),
                right: LinComb::summand(1, FlatVariable::new(21)),
            };
            assert_eq!(&a.to_string(), "(0) * (1 * _21)");
        }
    }
}
