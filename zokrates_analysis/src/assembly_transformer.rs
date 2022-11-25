// A static analyser pass to transform user-defined constraints to the form `lin_comb === quad_comb`
// This pass can fail if a non-quadratic constraint is found which cannot be transformed to the expected form

use crate::ZirPropagator;
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
        AssemblyTransformer.fold_program(p)
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
                        let sub = FieldElementExpression::Sub(box lhs, box rhs);
                        let mut lqc = LinQuadComb::try_from(sub.clone()).map_err(|_| {
                            Error("Non-quadratic constraints are not allowed".to_string())
                        })?;

                        let linear = lqc
                            .linear
                            .into_iter()
                            .map(|(c, i)| {
                                FieldElementExpression::Mult(
                                    box FieldElementExpression::Number(c),
                                    box FieldElementExpression::identifier(i),
                                )
                            })
                            .fold(FieldElementExpression::Number(T::from(0)), |acc, e| {
                                FieldElementExpression::Add(box acc, box e)
                            });

                        let lhs = FieldElementExpression::Add(
                            box FieldElementExpression::Number(lqc.constant),
                            box linear,
                        );

                        let rhs: FieldElementExpression<'ast, T> = if lqc.quadratic.len() > 1 {
                            let common_factors = lqc.quadratic.iter().fold(
                                None,
                                |acc: Option<Vec<Identifier>>, (_, a, b)| {
                                    Some(
                                        acc.map(|factors| {
                                            factors
                                                .into_iter()
                                                .filter(|f| f == a || f == b)
                                                .collect()
                                        })
                                        .unwrap_or_else(|| vec![a.clone(), b.clone()]),
                                    )
                                },
                            );

                            match common_factors {
                                Some(factors) => Ok(FieldElementExpression::Mult(
                                    box lqc
                                        .quadratic
                                        .into_iter()
                                        .map(|(c, i0, i1)| {
                                            let c = T::zero() - c;
                                            let i0 = match factors.contains(&i0) {
                                                true => FieldElementExpression::Number(T::from(1)),
                                                false => FieldElementExpression::identifier(i0),
                                            };
                                            let i1 = match factors.contains(&i1) {
                                                true => FieldElementExpression::Number(T::from(1)),
                                                false => FieldElementExpression::identifier(i1),
                                            };
                                            FieldElementExpression::Mult(
                                                box FieldElementExpression::Number(c),
                                                box FieldElementExpression::Mult(box i0, box i1),
                                            )
                                        })
                                        .fold(
                                            FieldElementExpression::Number(T::from(0)),
                                            |acc, e| FieldElementExpression::Add(box acc, box e),
                                        ),
                                    box factors.into_iter().fold(
                                        FieldElementExpression::Number(T::from(1)),
                                        |acc, id| {
                                            FieldElementExpression::Mult(
                                                box acc,
                                                box FieldElementExpression::identifier(id),
                                            )
                                        },
                                    ),
                                )),
                                None => Err(Error(
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

                        let mut propagator = ZirPropagator::default();
                        let lhs = propagator
                            .fold_field_expression(lhs)
                            .map_err(|e| Error(e.to_string()))?;

                        let rhs = propagator
                            .fold_field_expression(rhs)
                            .map_err(|e| Error(e.to_string()))?;

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
