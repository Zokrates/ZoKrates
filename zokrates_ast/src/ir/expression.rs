use super::Witness;
use crate::common::{flat::Variable, Span, WithSpan};
use derivative::Derivative;
use serde::{Deserialize, Serialize};
use std::collections::btree_map::{BTreeMap, Entry};
use std::fmt;
use std::ops::{Add, Div, Mul, Sub};
use zokrates_field::Field;

#[derive(Derivative)]
#[derivative(PartialEq, Hash)]
#[derive(Debug, Clone, Serialize, Deserialize, Eq)]
pub struct QuadComb<T> {
    #[derivative(PartialEq = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub left: LinComb<T>,
    pub right: LinComb<T>,
}

impl<T> WithSpan for QuadComb<T> {
    fn span(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

impl<T: Field> QuadComb<T> {
    #[allow(clippy::result_large_err)]
    pub fn try_linear(self) -> Result<LinComb<T>, Self> {
        // identify `(k * ~ONE) * (lincomb)` and `(lincomb) * (k * ~ONE)` and return (k * lincomb)
        // if not, error out with the input

        if self.left.is_zero() || self.right.is_zero() {
            return Ok(LinComb::zero());
        }

        match self.left.try_constant() {
            Ok(coefficient) => Ok(self.right * &coefficient),
            Err(left) => match self.right.try_constant() {
                Ok(coefficient) => Ok(left * &coefficient),
                Err(right) => Err(QuadComb::new(left, right)),
            },
        }
    }
}

impl<T: Field> From<T> for LinComb<T> {
    fn from(x: T) -> LinComb<T> {
        LinComb::one() * &x
    }
}

impl<T: Field, U: Into<LinComb<T>>> From<U> for QuadComb<T> {
    fn from(x: U) -> QuadComb<T> {
        QuadComb::new(LinComb::one(), x.into())
    }
}

impl<T: Field> fmt::Display for QuadComb<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}) * ({})", self.left, self.right,)
    }
}

#[derive(Derivative)]
#[derivative(PartialEq, Hash)]
#[derive(Clone, Debug, Serialize, Deserialize, Eq)]
pub struct LinComb<T> {
    #[derivative(PartialEq = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub value: Vec<(Variable, T)>,
}

#[derive(Derivative)]
#[derivative(PartialEq, Hash)]
#[derive(Clone, Debug, Serialize, Deserialize, Eq)]
pub struct CanonicalLinComb<T> {
    #[derivative(PartialEq = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub value: BTreeMap<Variable, T>,
}

impl<T> WithSpan for CanonicalLinComb<T> {
    fn span(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

#[derive(Derivative)]
#[derivative(PartialEq, Hash)]
#[derive(Clone, Debug, Serialize, Deserialize, Eq)]
pub struct CanonicalQuadComb<T> {
    #[derivative(PartialEq = "ignore", Hash = "ignore")]
    span: Option<Span>,
    left: CanonicalLinComb<T>,
    right: CanonicalLinComb<T>,
}

impl<T> WithSpan for CanonicalQuadComb<T> {
    fn span(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

impl<T> CanonicalQuadComb<T> {
    pub fn new(left: CanonicalLinComb<T>, right: CanonicalLinComb<T>) -> Self {
        Self {
            span: None,
            left,
            right,
        }
    }
}

impl<T> QuadComb<T> {
    pub fn new(left: LinComb<T>, right: LinComb<T>) -> Self {
        Self {
            span: None,
            left,
            right,
        }
    }
}

impl<T> From<CanonicalQuadComb<T>> for QuadComb<T> {
    fn from(q: CanonicalQuadComb<T>) -> Self {
        QuadComb {
            span: q.span,
            left: q.left.into(),
            right: q.right.into(),
        }
    }
}

impl<T> From<CanonicalLinComb<T>> for LinComb<T> {
    fn from(l: CanonicalLinComb<T>) -> Self {
        LinComb {
            span: l.span,
            value: l.value.into_iter().collect(),
        }
    }
}

impl<T> CanonicalLinComb<T> {
    pub fn new(value: BTreeMap<Variable, T>) -> Self {
        Self { span: None, value }
    }
}

impl<T> LinComb<T> {
    pub fn new(value: Vec<(Variable, T)>) -> Self {
        Self { span: None, value }
    }

    pub fn summand<U: Into<T>>(mult: U, var: Variable) -> LinComb<T> {
        let res = vec![(var, mult.into())];

        LinComb::new(res)
    }

    pub fn zero() -> LinComb<T> {
        LinComb::new(Vec::new())
    }

    pub fn is_zero(&self) -> bool {
        self.value.is_empty()
    }
}

impl<T> WithSpan for LinComb<T> {
    fn span(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

impl<T: Field> LinComb<T> {
    pub fn try_constant(self) -> Result<T, Self> {
        match self.value.len() {
            // if the lincomb is empty, it is reduceable to 0
            0 => Ok(T::zero()),
            _ => {
                // take the first variable in the lincomb
                let first = &self.value[0].0;

                if first != &Variable::one() {
                    return Err(self);
                }

                // all terms must contain the same variable
                if self.value.iter().all(|element| element.0 == *first) {
                    Ok(self.value.into_iter().fold(T::zero(), |acc, e| acc + e.1))
                } else {
                    Err(self)
                }
            }
        }
    }

    pub fn is_assignee(&self, witness: &Witness<T>) -> bool {
        self.value.len() == 1
            && self.value.get(0).unwrap().1 == T::from(1)
            && !witness.0.contains_key(&self.value.get(0).unwrap().0)
    }

    pub fn try_summand(self) -> Result<(Variable, T), Self> {
        match self.value.len() {
            // if the lincomb is empty, it is not reduceable to a summand
            0 => Err(self),
            _ => {
                // take the first variable in the lincomb
                let first = &self.value[0].0;

                if self.value.iter().all(|element|
                        // all terms must contain the same variable
                        element.0 == *first)
                {
                    Ok((
                        *first,
                        self.value.into_iter().fold(T::zero(), |acc, e| acc + e.1),
                    ))
                } else {
                    Err(self)
                }
            }
        }
    }

    pub fn one() -> LinComb<T> {
        Self::summand(1, Variable::one())
    }
}

impl<T: Field> LinComb<T> {
    pub fn into_canonical(self) -> CanonicalLinComb<T> {
        let span = self.get_span();

        CanonicalLinComb::new(self.value.into_iter().fold(
            BTreeMap::<Variable, T>::new(),
            |mut acc, (val, coeff)| {
                // if we're adding 0 times some variable, we can ignore this term
                if coeff != T::zero() {
                    match acc.entry(val) {
                        Entry::Occupied(o) => {
                            // if the new value is non zero, update, else remove the term entirely
                            if *o.get() + coeff != T::zero() {
                                *o.into_mut() = *o.get() + coeff;
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
        .span(span)
    }

    pub fn reduce(self) -> Self {
        self.into_canonical().into()
    }
}

impl<T: Field> QuadComb<T> {
    pub fn into_canonical(self) -> CanonicalQuadComb<T> {
        CanonicalQuadComb::new(self.left.into_canonical(), self.right.into_canonical())
            .span(self.span)
    }

    pub fn reduce(self) -> Self {
        self.into_canonical().into()
    }
}

impl<T: Field> fmt::Display for LinComb<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.is_zero() {
            true => write!(f, "0"),
            false => write!(
                f,
                "{}",
                self.value
                    .iter()
                    .map(|(k, v)| format!("{} * {}", v.to_compact_dec_string(), k))
                    .collect::<Vec<_>>()
                    .join(" + ")
            ),
        }
    }
}

impl<T: Field> From<Variable> for LinComb<T> {
    fn from(v: Variable) -> LinComb<T> {
        let r = vec![(v, T::one())];
        LinComb::new(r)
    }
}

impl<T: Field> Add<LinComb<T>> for LinComb<T> {
    type Output = LinComb<T>;

    fn add(self, other: LinComb<T>) -> LinComb<T> {
        let mut res = self.value;
        res.extend(other.value);
        LinComb::new(res)
    }
}

impl<T: Field> Sub<LinComb<T>> for LinComb<T> {
    type Output = LinComb<T>;

    fn sub(self, other: LinComb<T>) -> LinComb<T> {
        // Concatenate with second vector that have negative coeffs
        let mut res = self.value;
        res.extend(
            other
                .value
                .into_iter()
                .map(|(var, val)| (var, T::zero() - val)),
        );
        LinComb::new(res)
    }
}

impl<T: Field> Mul<&T> for LinComb<T> {
    type Output = LinComb<T>;

    fn mul(self, scalar: &T) -> LinComb<T> {
        if scalar == &T::one() {
            return self;
        }

        LinComb::new(
            self.value
                .into_iter()
                .map(|(var, coeff)| (var, coeff * scalar))
                .collect(),
        )
    }
}

impl<T: Field> Div<&T> for LinComb<T> {
    type Output = LinComb<T>;
    // Clippy warns about multiplication in a method named div. It's okay, here, since we multiply with the inverse.
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, scalar: &T) -> LinComb<T> {
        self * &scalar.inverse_mul().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::Bn128Field;

    mod linear {

        use super::*;
        #[test]
        fn add_zero() {
            let a: LinComb<Bn128Field> = LinComb::zero();
            let b: LinComb<Bn128Field> = Variable::new(42).into();
            let c = a + b.clone();
            assert_eq!(c, b);
        }
        #[test]
        fn add() {
            let a: LinComb<Bn128Field> = Variable::new(42).into();
            let b: LinComb<Bn128Field> = Variable::new(42).into();
            let c = a + b;

            let expected_vec = vec![
                (Variable::new(42), Bn128Field::from(1)),
                (Variable::new(42), Bn128Field::from(1)),
            ];

            assert_eq!(c, LinComb::new(expected_vec));
        }
        #[test]
        fn sub() {
            let a: LinComb<Bn128Field> = Variable::new(42).into();
            let b: LinComb<Bn128Field> = Variable::new(42).into();
            let c = a - b;

            let expected_vec = vec![
                (Variable::new(42), Bn128Field::from(1)),
                (Variable::new(42), Bn128Field::from(-1)),
            ];

            assert_eq!(c, LinComb::new(expected_vec));
        }

        #[test]
        fn display() {
            let a: LinComb<Bn128Field> =
                LinComb::from(Variable::new(42)) + LinComb::summand(3, Variable::new(21));
            assert_eq!(&a.to_string(), "1 * _42 + 3 * _21");
            let zero: LinComb<Bn128Field> = LinComb::zero();
            assert_eq!(&zero.to_string(), "0");
        }
    }

    mod quadratic {
        use super::*;
        #[test]
        fn from_linear() {
            let a: LinComb<Bn128Field> =
                LinComb::summand(3, Variable::new(42)) + LinComb::summand(4, Variable::new(33));
            let expected = QuadComb::new(LinComb::one(), a.clone());
            assert_eq!(QuadComb::from(a), expected);
        }

        #[test]
        fn zero() {
            let a: LinComb<Bn128Field> = LinComb::zero();
            let expected: QuadComb<Bn128Field> = QuadComb::new(LinComb::one(), LinComb::zero());
            assert_eq!(QuadComb::from(a), expected);
        }

        #[test]
        fn display() {
            let a: QuadComb<Bn128Field> = QuadComb::new(
                LinComb::summand(3, Variable::new(42)) + LinComb::summand(4, Variable::new(33)),
                LinComb::summand(1, Variable::new(21)),
            );
            assert_eq!(&a.to_string(), "(3 * _42 + 4 * _33) * (1 * _21)");
            let a: QuadComb<Bn128Field> =
                QuadComb::new(LinComb::zero(), LinComb::summand(1, Variable::new(21)));
            assert_eq!(&a.to_string(), "(0) * (1 * _21)");
        }
    }

    mod try_summand {
        use super::*;

        #[test]
        fn try_summand() {
            let summand = LinComb::new(vec![
                (Variable::new(42), Bn128Field::from(1)),
                (Variable::new(42), Bn128Field::from(2)),
                (Variable::new(42), Bn128Field::from(3)),
            ]);
            assert_eq!(
                summand.try_summand(),
                Ok((Variable::new(42), Bn128Field::from(6)))
            );

            let not_summand = LinComb::new(vec![
                (Variable::new(41), Bn128Field::from(1)),
                (Variable::new(42), Bn128Field::from(2)),
                (Variable::new(42), Bn128Field::from(3)),
            ]);
            assert!(not_summand.try_summand().is_err());

            let empty: LinComb<Bn128Field> = LinComb::new(vec![]);
            assert!(empty.try_summand().is_err());
        }
    }
}
