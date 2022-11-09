use crate::zir::{FieldElementExpression, Identifier};
use zokrates_field::Field;

#[derive(Clone, PartialEq, Hash, Eq, Debug, Default)]
pub struct LinQuadComb<'ast, T> {
    // the constant terms
    pub constant: T,
    // the linear terms
    pub linear: Vec<(T, Identifier<'ast>)>,
    // the quadratic terms
    pub quadratic: Vec<(T, Identifier<'ast>, Identifier<'ast>)>,
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
                    *c = T::zero() - &*c;
                });
                l.append(&mut other.linear);
                l
            },
            quadratic: {
                let mut q = self.quadratic;
                other.quadratic.iter_mut().for_each(|(c, _, _)| {
                    *c = T::zero() - &*c;
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
            constant: self.constant.clone() * rhs.constant.clone(),
            linear: {
                // lin0 * const1 + lin1 * const0
                self.linear
                    .clone()
                    .into_iter()
                    .map(|(c, i)| (c * rhs.constant.clone(), i))
                    .chain(
                        rhs.linear
                            .clone()
                            .into_iter()
                            .map(|(c, i)| (c * self.constant.clone(), i)),
                    )
                    .collect()
            },
            quadratic: {
                // quad0 * const1 + quad1 * const0 + lin0 * lin1
                self.quadratic
                    .into_iter()
                    .map(|(c, i0, i1)| (c * rhs.constant.clone(), i0, i1))
                    .chain(
                        rhs.quadratic
                            .into_iter()
                            .map(|(c, i0, i1)| (c * self.constant.clone(), i0, i1)),
                    )
                    .chain(self.linear.iter().flat_map(|(cl, l)| {
                        rhs.linear
                            .iter()
                            .map(|(cr, r)| (cl.clone() * cr.clone(), l.clone(), r.clone()))
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
            FieldElementExpression::Number(v) => Ok(Self {
                constant: v,
                ..Self::default()
            }),
            FieldElementExpression::Identifier(id) => Ok(Self {
                linear: vec![(T::one(), id)],
                ..Self::default()
            }),
            FieldElementExpression::Add(box left, box right) => {
                Ok(Self::try_from(left)? + Self::try_from(right)?)
            }
            FieldElementExpression::Sub(box left, box right) => {
                Ok(Self::try_from(left)? - Self::try_from(right)?)
            }
            FieldElementExpression::Mult(box left, box right) => {
                let left = Self::try_from(left)?;
                let right = Self::try_from(right)?;

                left.try_mul(right)
            }
            _ => Err(()),
        }
    }
}
