use std::fmt;
use zokrates_ast::zir::lqc::LinQuadComb;
use zokrates_ast::zir::result_folder::{fold_field_expression, ResultFolder};
use zokrates_ast::zir::{FieldElementExpression, Id, Identifier, ZirAssemblyStatement, ZirProgram};
use zokrates_field::Field;

#[derive(Debug)]
pub struct Error(String);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub struct AssemblyTransformer;

impl AssemblyTransformer {
    pub fn transform<T: Field>(p: ZirProgram<T>) -> Result<ZirProgram<T>, Error> {
        let mut f = AssemblyTransformer;
        f.fold_program(p)
    }
}

impl<'ast, T: Field> ResultFolder<'ast, T> for AssemblyTransformer {
    type Error = Error;

    fn fold_assembly_statement(
        &mut self,
        s: ZirAssemblyStatement<'ast, T>,
    ) -> Result<ZirAssemblyStatement<'ast, T>, Self::Error> {
        match s {
            ZirAssemblyStatement::Assignment(_, _) => Ok(s),
            ZirAssemblyStatement::Constraint(lhs, rhs) => {
                let lhs = self.fold_field_expression(lhs)?;
                let rhs = self.fold_field_expression(rhs)?;

                let (is_quadratic, lhs, rhs) = match (lhs, rhs) {
                    (FieldElementExpression::Mult(x, y), other)
                    | (other, FieldElementExpression::Mult(x, y))
                        if other.is_linear() =>
                    {
                        (
                            x.is_linear() && y.is_linear(),
                            other,
                            FieldElementExpression::Mult(x, y),
                        )
                    }
                    (lhs, rhs) => (false, lhs, rhs),
                };

                match is_quadratic {
                    true => Ok(ZirAssemblyStatement::Constraint(lhs, rhs)),
                    false => {
                        let sub = FieldElementExpression::Sub(box lhs.clone(), box rhs.clone());
                        let mut lqc = LinQuadComb::try_from(sub.clone()).map_err(|_| {
                            Error("Non-quadratic constraints are not allowed".to_string())
                        })?;

                        let linear = lqc
                            .linear
                            .into_iter()
                            .filter_map(|(c, i)| match c {
                                c if c == T::from(0) => None,
                                c if c == T::from(1) => Some(FieldElementExpression::identifier(i)),
                                _ => Some(FieldElementExpression::Mult(
                                    box FieldElementExpression::Number(c),
                                    box FieldElementExpression::identifier(i),
                                )),
                            })
                            .reduce(|p, n| FieldElementExpression::Add(box p, box n))
                            .unwrap_or_else(|| FieldElementExpression::Number(T::from(0)));

                        let lhs = match lqc.constant {
                            c if c == T::from(0) => linear,
                            c => FieldElementExpression::Add(
                                box FieldElementExpression::Number(c),
                                box linear,
                            ),
                        };

                        let rhs: FieldElementExpression<'ast, T> = if lqc.quadratic.len() > 1 {
                            let is_common_factor = |id: &Identifier<'ast>,
                                                    q: &Vec<(
                                T,
                                Identifier<'ast>,
                                Identifier<'ast>,
                            )>| {
                                q.iter().all(|(_, i0, i1)| i0.eq(id) || i1.eq(id))
                            };

                            let common_factor: Option<Identifier<'ast>> =
                                lqc.quadratic.iter().find_map(|(_, i0, i1)| {
                                    if is_common_factor(i0, &lqc.quadratic) {
                                        Some(i0.clone())
                                    } else if is_common_factor(i1, &lqc.quadratic) {
                                        Some(i1.clone())
                                    } else {
                                        None
                                    }
                                });

                            match common_factor {
                                Some(id) => Ok(FieldElementExpression::Mult(
                                    box lqc
                                        .quadratic
                                        .into_iter()
                                        .filter_map(|(c, i0, i1)| {
                                            let c = T::zero() - c;
                                            let id = if id.eq(&i0) { i1 } else { i0 };
                                            match c {
                                                c if c == T::from(0) => None,
                                                c if c == T::from(1) => {
                                                    Some(FieldElementExpression::identifier(id))
                                                }
                                                _ => Some(FieldElementExpression::Mult(
                                                    box FieldElementExpression::Number(c),
                                                    box FieldElementExpression::identifier(id),
                                                )),
                                            }
                                        })
                                        .reduce(|p, n| FieldElementExpression::Add(box p, box n))
                                        .unwrap_or_else(|| {
                                            FieldElementExpression::Number(T::from(0))
                                        }),
                                    box FieldElementExpression::identifier(id),
                                )),
                                _ => Err(Error(
                                    "Non-quadratic constraints are not allowed".to_string(),
                                )),
                            }?
                        } else {
                            lqc.quadratic
                                .pop()
                                .map(|(c, i0, i1)| {
                                    FieldElementExpression::Mult(
                                        box FieldElementExpression::Mult(
                                            box FieldElementExpression::Number(T::zero() - c),
                                            box FieldElementExpression::identifier(i0),
                                        ),
                                        box FieldElementExpression::identifier(i1),
                                    )
                                })
                                .unwrap_or_else(|| FieldElementExpression::Number(T::from(0)))
                        };

                        Ok(ZirAssemblyStatement::Constraint(lhs, rhs))
                    }
                }
            }
        }
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> Result<FieldElementExpression<'ast, T>, Self::Error> {
        match e {
            FieldElementExpression::And(_, _)
            | FieldElementExpression::Or(_, _)
            | FieldElementExpression::Xor(_, _)
            | FieldElementExpression::LeftShift(_, _)
            | FieldElementExpression::RightShift(_, _) => Err(Error(
                format!("Found bitwise operation in expression `{}` of type `field` (only allowed in assembly assignment statement)", e)
            )),
            e => fold_field_expression(self, e),
        }
    }
}
