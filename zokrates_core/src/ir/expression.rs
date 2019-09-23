use crate::flat_absy::FlatVariable;
use num::Zero;
use std::collections::btree_map::{BTreeMap, Entry};
use std::fmt;
use std::ops::{Add, Div, Mul, Sub};
use zokrates_field::field::Field;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Hash, Eq)]
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
            Some((ref variable, ref coefficient)) if *variable == FlatVariable::one() => {
                return Some(self.right.clone() * &coefficient);
            }
            _ => {}
        }
        match self.right.try_summand() {
            Some((ref variable, ref coefficient)) if *variable == FlatVariable::one() => {
                return Some(self.left.clone() * &coefficient);
            }
            _ => {}
        }

        if self.left.is_zero() || self.right.is_zero() {
            return Some(LinComb::zero());
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

#[derive(Eq, PartialOrd, Clone, Ord, Hash, Debug, Serialize, Deserialize)]
pub struct LinComb<T: Field>(pub Vec<(FlatVariable, T)>);

impl<T: Field> PartialEq for LinComb<T> {
    fn eq(&self, other: &Self) -> bool {
        self.as_canonical() == other.as_canonical()
    }
}

#[derive(PartialEq, PartialOrd, Clone, Eq, Ord, Hash, Debug, Serialize, Deserialize)]
pub struct CanonicalLinComb<T: Field>(pub BTreeMap<FlatVariable, T>);

impl<T: Field> LinComb<T> {
    pub fn summand<U: Into<T>>(mult: U, var: FlatVariable) -> LinComb<T> {
        let res = vec![(var, mult.into())];

        LinComb(res)
    }

    pub fn one() -> LinComb<T> {
        Self::summand(1, FlatVariable::one())
    }

    pub fn try_summand(&self) -> Option<(FlatVariable, T)> {
        match self.0.len() {
            // if the lincomb is empty, it is not reduceable to a summand
            0 => None,
            _ => {
                // take the first variable in the lincomb
                let first = &self.0[0].0;

                self.0
                    .iter()
                    .map(|element| {
                        // all terms must contain the same variable
                        if element.0 == *first {
                            // if they do, return the coefficient
                            Ok(&element.1)
                        } else {
                            // otherwise, stop
                            Err(())
                        }
                    })
                    // collect to a Result to short circuit when we hit an error
                    .collect::<Result<_, _>>()
                    // we didn't hit an error, do final processing. It's fine to clone here.
                    .map(|v: Vec<_>| (first.clone(), v.iter().fold(T::zero(), |acc, e| acc + *e)))
                    .ok()
            }
        }
    }

    pub fn as_canonical(&self) -> CanonicalLinComb<T> {
        CanonicalLinComb(self.0.clone().into_iter().fold(
            BTreeMap::new(),
            |mut acc, (val, coeff)| {
                // if we're adding 0 times some variable, we can ignore this term
                if coeff != T::zero() {
                    match acc.entry(val) {
                        Entry::Occupied(o) => {
                            // if the new value is non zero, update, else remove the term entirely
                            if o.get().clone() + coeff.clone() != T::zero() {
                                *o.into_mut() = o.get().clone() + coeff;
                            } else {
                                o.remove();
                            }
                        }
                        Entry::Vacant(v) => {
                            // We checked earlier but let's make sure we're not creating zero-coeff terms
                            assert!(coeff != T::zero());
                            v.insert(coeff);
                        }
                    }
                }

                acc
            },
        ))
    }
}

impl<T: Field> fmt::Display for LinComb<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.is_zero() {
            true => write!(f, "0"),
            false => write!(
                f,
                "{}",
                self.as_canonical()
                    .0
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
        res.extend(other.0);
        LinComb(res)
    }
}

impl<T: Field> Sub<LinComb<T>> for LinComb<T> {
    type Output = LinComb<T>;

    fn sub(self, other: LinComb<T>) -> LinComb<T> {
        // Concatenate with second vector that have negative coeffs
        let mut res = self.0;
        res.extend(other.0.into_iter().map(|(var, val)| (var, T::zero() - val)));
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
                (FlatVariable::new(42), FieldPrime::from(1)),
            ];

            assert_eq!(c, LinComb(expected_vec));
        }
        #[test]
        fn sub() {
            let a: LinComb<FieldPrime> = FlatVariable::new(42).into();
            let b: LinComb<FieldPrime> = FlatVariable::new(42).into();
            let c = a - b.clone();

            let expected_vec = vec![
                (FlatVariable::new(42), FieldPrime::from(1)),
                (FlatVariable::new(42), FieldPrime::from(-1)),
            ];

            assert_eq!(c, LinComb(expected_vec));
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

    mod try {
        use super::*;

        #[test]
        fn try_summand() {
            let summand = LinComb(vec![
                (FlatVariable::new(42), FieldPrime::from(1)),
                (FlatVariable::new(42), FieldPrime::from(2)),
                (FlatVariable::new(42), FieldPrime::from(3)),
            ]);
            assert_eq!(
                summand.try_summand(),
                Some((FlatVariable::new(42), FieldPrime::from(6)))
            );

            let not_summand = LinComb(vec![
                (FlatVariable::new(41), FieldPrime::from(1)),
                (FlatVariable::new(42), FieldPrime::from(2)),
                (FlatVariable::new(42), FieldPrime::from(3)),
            ]);
            assert_eq!(not_summand.try_summand(), None);

            let empty: LinComb<FieldPrime> = LinComb(vec![]);
            assert_eq!(empty.try_summand(), None);
        }
    }
}
