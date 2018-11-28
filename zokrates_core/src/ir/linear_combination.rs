use field::Field;
use flat_absy::FlatVariable;
use num::Zero;
use std::collections::BTreeMap;
use std::fmt;
use std::ops::{Add, Sub};

#[derive(PartialEq, PartialOrd, Clone, Eq, Ord, Hash, Debug)]
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
        write!(
            f,
            "{}",
            self.0
                .iter()
                .map(|(k, v)| format!("{} * {}", v, k))
                .collect::<Vec<_>>()
                .join(" + ")
        )
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
    use field::FieldPrime;

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
        assert_eq!(c, b);
    }
    #[test]
    fn sub() {
        let a: LinComb<FieldPrime> = FlatVariable::new(42).into();
        let b: LinComb<FieldPrime> = FlatVariable::new(42).into();
        let c = a - b.clone();
        assert_eq!(c, LinComb::zero());
    }
}
