use crate::zir::{FieldElementExpression, Identifier};
use zokrates_field::Field;

pub type LinearTerm<'ast, T> = (T, Identifier<'ast>);
pub type QuadraticTerm<'ast, T> = (T, Identifier<'ast>, Identifier<'ast>);

#[derive(Clone, PartialEq, Hash, Eq, Debug, Default)]
pub struct LinQuadComb<'ast, T> {
    // the constant terms
    pub constant: T,
    // the linear terms
    pub linear: Vec<LinearTerm<'ast, T>>,
    // the quadratic terms
    pub quadratic: Vec<QuadraticTerm<'ast, T>>,
}

impl<'ast, T: Field> std::ops::Add for LinQuadComb<'ast, T> {
    type Output = Self;

    fn add(self, mut other: Self) -> Self::Output {
        Self {
            constant: self.constant + other.constant,
            linear: {
                let mut l = self.linear;
                l.append(&mut other.linear);
                l
            },
            quadratic: {
                let mut q = self.quadratic;
                q.append(&mut other.quadratic);
                q
            },
        }
    }
}

impl<'ast, T: Field> std::ops::Sub for LinQuadComb<'ast, T> {
    type Output = Self;

    fn sub(self, mut other: Self) -> Self::Output {
        Self {
            constant: self.constant - other.constant,
            linear: {
                let mut l = self.linear;
                other.linear.iter_mut().for_each(|(c, _)| {
                    *c = T::zero() - *c;
                });
                l.append(&mut other.linear);
                l
            },
            quadratic: {
                let mut q = self.quadratic;
                other.quadratic.iter_mut().for_each(|(c, _, _)| {
                    *c = T::zero() - *c;
                });
                q.append(&mut other.quadratic);
                q
            },
        }
    }
}

impl<'ast, T: Field> LinQuadComb<'ast, T> {
    fn try_mul(self, rhs: Self) -> Result<Self, ()> {
        // fail if the result has degree higher than 2
        if !(self.quadratic.is_empty() || rhs.quadratic.is_empty()) {
            return Err(());
        }

        Ok(Self {
            constant: self.constant * rhs.constant,
            linear: {
                // lin0 * const1 + lin1 * const0
                self.linear
                    .clone()
                    .into_iter()
                    .map(|(c, i)| (c * rhs.constant, i))
                    .chain(
                        rhs.linear
                            .clone()
                            .into_iter()
                            .map(|(c, i)| (c * self.constant, i)),
                    )
                    .collect()
            },
            quadratic: {
                // quad0 * const1 + quad1 * const0 + lin0 * lin1
                self.quadratic
                    .into_iter()
                    .map(|(c, i0, i1)| (c * rhs.constant, i0, i1))
                    .chain(
                        rhs.quadratic
                            .into_iter()
                            .map(|(c, i0, i1)| (c * self.constant, i0, i1)),
                    )
                    .chain(self.linear.iter().flat_map(|(cl, l)| {
                        rhs.linear
                            .iter()
                            .map(|(cr, r)| (*cl * *cr, l.clone(), r.clone()))
                    }))
                    .collect()
            },
        })
    }
}

impl<'ast, T: Field> TryFrom<FieldElementExpression<'ast, T>> for LinQuadComb<'ast, T> {
    type Error = ();

    fn try_from(e: FieldElementExpression<'ast, T>) -> Result<Self, Self::Error> {
        match e {
            FieldElementExpression::Value(v) => Ok(Self {
                constant: v.value,
                ..Self::default()
            }),
            FieldElementExpression::Identifier(id) => Ok(Self {
                linear: vec![(T::one(), id.id)],
                ..Self::default()
            }),
            FieldElementExpression::Add(e) => {
                Ok(Self::try_from(*e.left)? + Self::try_from(*e.right)?)
            }
            FieldElementExpression::Sub(e) => {
                Ok(Self::try_from(*e.left)? - Self::try_from(*e.right)?)
            }
            FieldElementExpression::Mult(e) => {
                let left = Self::try_from(*e.left)?;
                let right = Self::try_from(*e.right)?;

                left.try_mul(right)
            }
            _ => Err(()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::zir::{Expr, Id};
    use std::ops::*;
    use zokrates_field::Bn128Field;

    #[test]
    fn add() {
        // (2 + 2*a)
        let a = LinQuadComb::try_from(FieldElementExpression::add(
            FieldElementExpression::value(Bn128Field::from(2)),
            FieldElementExpression::mul(
                FieldElementExpression::value(Bn128Field::from(2)),
                FieldElementExpression::identifier("a".into()),
            ),
        ))
        .unwrap();

        // (2 + 2*a*b)
        let b = LinQuadComb::try_from(FieldElementExpression::add(
            FieldElementExpression::value(Bn128Field::from(2)),
            FieldElementExpression::mul(
                FieldElementExpression::mul(
                    FieldElementExpression::value(Bn128Field::from(2)),
                    FieldElementExpression::identifier("a".into()),
                ),
                FieldElementExpression::identifier("b".into()),
            ),
        ))
        .unwrap();

        // (2 + 2*a) + (2 + 2*a*b) => 4 + 2*a + 2*a*b
        let c = a + b;

        assert_eq!(c.constant, Bn128Field::from(4));
        assert_eq!(
            c.linear,
            vec![
                (Bn128Field::from(2), "a".into()),
                (Bn128Field::from(0), "a".into()),
                (Bn128Field::from(0), "b".into())
            ]
        );
        assert_eq!(
            c.quadratic,
            vec![(Bn128Field::from(2), "a".into(), "b".into())]
        );
    }

    #[test]
    fn sub() {
        // (2 + 2*a)
        let a = LinQuadComb::try_from(FieldElementExpression::add(
            FieldElementExpression::value(Bn128Field::from(2)),
            FieldElementExpression::mul(
                FieldElementExpression::value(Bn128Field::from(2)),
                FieldElementExpression::identifier("a".into()),
            ),
        ))
        .unwrap();

        // (2 + 2*a*b)
        let b = LinQuadComb::try_from(FieldElementExpression::add(
            FieldElementExpression::value(Bn128Field::from(2)),
            FieldElementExpression::mul(
                FieldElementExpression::mul(
                    FieldElementExpression::value(Bn128Field::from(2)),
                    FieldElementExpression::identifier("a".into()),
                ),
                FieldElementExpression::identifier("b".into()),
            ),
        ))
        .unwrap();

        // (2 + 2*a) - (2 + 2*a*b) => 0 + 2*a + (-2)*a*b
        let c = a - b;

        assert_eq!(c.constant, Bn128Field::from(0));
        assert_eq!(
            c.linear,
            vec![
                (Bn128Field::from(2), "a".into()),
                (Bn128Field::from(0), "a".into()),
                (Bn128Field::from(0), "b".into())
            ]
        );
        assert_eq!(
            c.quadratic,
            vec![(Bn128Field::from(-2), "a".into(), "b".into())]
        );
    }

    #[test]
    fn mul() {
        // (2 + 2*a)
        let a = LinQuadComb::try_from(FieldElementExpression::add(
            FieldElementExpression::value(Bn128Field::from(2)),
            FieldElementExpression::mul(
                FieldElementExpression::value(Bn128Field::from(2)),
                FieldElementExpression::identifier("a".into()),
            ),
        ))
        .unwrap();

        // (2 + 2*b)
        let b = LinQuadComb::try_from(FieldElementExpression::add(
            FieldElementExpression::value(Bn128Field::from(2)),
            FieldElementExpression::mul(
                FieldElementExpression::value(Bn128Field::from(2)),
                FieldElementExpression::identifier("b".into()),
            ),
        ))
        .unwrap();

        // (2 + 2*a) * (2 + 2*b) => 4 + 4*b + 4*a + 4*a*b
        let c = a.try_mul(b).unwrap();

        assert_eq!(c.constant, Bn128Field::from(4));
        assert_eq!(
            c.linear,
            vec![
                (Bn128Field::from(4), "a".into()),
                (Bn128Field::from(4), "b".into()),
            ]
        );
        assert_eq!(
            c.quadratic,
            vec![(Bn128Field::from(4), "a".into(), "b".into())]
        );
    }

    #[test]
    fn mul_degree_error() {
        // 2*a*b
        let a = LinQuadComb::try_from(FieldElementExpression::add(
            FieldElementExpression::value(Bn128Field::from(2)),
            FieldElementExpression::mul(
                FieldElementExpression::identifier("a".into()),
                FieldElementExpression::identifier("b".into()),
            ),
        ))
        .unwrap();

        // 2*a*b
        let b = a.clone();

        // (2*a*b) * (2*a*b) would result in a higher degree than expected
        let c = a.try_mul(b);
        assert!(c.is_err());
    }
}
