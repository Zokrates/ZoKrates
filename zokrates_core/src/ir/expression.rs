use flat_absy::FlatVariable;
use num::Zero;
use std::fmt;
use std::ops::{Add, Div, Mul, Sub};
use zokrates_field::field::Field;
use std::collections::btree_set::BTreeSet;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct QuadComb<T: Field> {
    pub left: LinComb<T>,
    pub right: LinComb<T>,
}

impl<T: Field> QuadComb<T> {
    pub fn from_linear_combinations(left: LinComb<T>, right: LinComb<T>) -> Self {
        QuadComb { left, right }
    }

    pub fn try_linear(&self) -> Option<LinComb<T>> {
        // identify (k * ~ONE) * (lincomb) and return (k * lincomb)

        match self.left.try_summand() {
            Some((variable, coefficient)) if *variable == FlatVariable::one() => {
                return Some(self.right.clone() * &coefficient);
            }
            _ => {}
        }
        match self.right.try_summand() {
            Some((variable, coefficient)) if *variable == FlatVariable::one() => {
                return Some(self.left.clone() * &coefficient);
            }
            _ => {}
        }
        None
    }
}

impl<T: Field> From<T> for LinComb<T> {
    fn from(x: T) -> LinComb<T> {
        LinComb::one() * &x
    }
}

impl<T: Field, U: Into<LinComb<T>>> From<U> for QuadComb<T> {
    fn from(x: U) -> QuadComb<T> {
        QuadComb::from_linear_combinations(LinComb::one(), x.into())
    }
}

impl<T: Field> fmt::Display for QuadComb<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}) * ({})", self.left, self.right,)
    }
}

#[derive(PartialEq, PartialOrd, Clone, Eq, Ord, Hash, Debug, Serialize, Deserialize)]
pub struct LinComb<T: Field>(pub Vec<(FlatVariable, T)>);

impl<T: Field> LinComb<T> {
    pub fn summand<U: Into<T>>(mult: U, var: FlatVariable) -> LinComb<T> {
        let res = vec![(var, mult.into())];

        LinComb(res)
    }

    pub fn one() -> LinComb<T> {
        Self::summand(1, FlatVariable::one())
    }

    pub fn try_summand(&self) -> Option<(&FlatVariable, &T)> {
        if self.0.len() == 1 {
            return self.0.first().map(|(id, k)| (id, k))
        }

        None
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
        let r = vec![(v, T::one())];
        LinComb(r)
    }
}

impl<T: Field> Add<LinComb<T>> for LinComb<T> {
    type Output = LinComb<T>;

    fn add(self, other: LinComb<T>) -> LinComb<T> {
        let mut res = self.0;
        let mut to_remove = BTreeSet::new();

        for (k, v) in other.0 {
            let var;
            {
                var = res
                    .iter()
                    .find(|(id, _)| *id == k)
                    .map(|(_, v)| v)
                    .cloned();
            }

            let new_val = v + var.unwrap_or(T::zero());
            if new_val != T::zero() {
                res.push((k, new_val));
            } else {
                to_remove.insert(k);
            }
        }

        res.retain(|(id, _)| !to_remove.contains(id));
        LinComb(res)
    }
}

impl<T: Field> Sub<LinComb<T>> for LinComb<T> {
    type Output = LinComb<T>;

    fn sub(self, other: LinComb<T>) -> LinComb<T> {
        let mut res = self.0;
        let mut to_remove = BTreeSet::new();

        for (k, v) in other.0 {
            let var;
            {
                var = res
                    .iter()
                    .find(|(id, _)| *id == k)
                    .map(|(_, v)| v)
                    .cloned();
            }

            let new_val = T::zero() - v + var.unwrap_or(T::zero());
            if new_val != T::zero() {
                res.push((k, new_val));
            } else {
                to_remove.insert(k);
            }
        }

        res.retain(|(id, _)| !to_remove.contains(id));
        LinComb(res)
    }
}

impl<T: Field> Mul<&T> for LinComb<T> {
    type Output = LinComb<T>;

    fn mul(self, scalar: &T) -> LinComb<T> {
        LinComb(
            self.0
                .into_iter()
                .map(|(var, coeff)| (var, coeff * scalar))
                .collect(),
        )
    }
}

impl<T: Field> Div<&T> for LinComb<T> {
    type Output = LinComb<T>;

    fn div(self, scalar: &T) -> LinComb<T> {
        self * &scalar.inverse_mul()
    }
}

impl<T: Field> Zero for LinComb<T> {
    fn zero() -> LinComb<T> {
        LinComb(Vec::new())
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

            let expected_vec = vec![
                (FlatVariable::new(42), FieldPrime::from(1)),
                (FlatVariable::new(42), FieldPrime::from(2)),

            ];
            assert_eq!(c, LinComb(expected_vec));
        }
        #[test]
        fn sub() {
            let a: LinComb<FieldPrime> = FlatVariable::new(42).into();
            let b: LinComb<FieldPrime> = FlatVariable::new(42).into();
            let c = a - b.clone();
            assert_eq!(LinComb::zero(), c);
        }

        #[test]
        fn display() {
            let a: LinComb<FieldPrime> =
                LinComb::from(FlatVariable::new(42)) + LinComb::summand(3, FlatVariable::new(21));
            assert_eq!(&a.to_string(), "1 * _42 + 3 * _21");
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
            assert_eq!(&a.to_string(), "(3 * _42 + 4 * _33) * (1 * _21)");
            let a: QuadComb<FieldPrime> = QuadComb {
                left: LinComb::zero(),
                right: LinComb::summand(1, FlatVariable::new(21)),
            };
            assert_eq!(&a.to_string(), "(0) * (1 * _21)");
        }
    }
}
