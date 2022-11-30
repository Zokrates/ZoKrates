// A static analyser pass to transform user-defined constraints to the form `lin_comb === quad_comb`
// This pass can fail if a non-quadratic constraint is found which cannot be transformed to the expected form

use crate::ZirPropagator;
use std::fmt;
use zokrates_ast::zir::lqc::LinQuadComb;
use zokrates_ast::zir::result_folder::ResultFolder;
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
            ZirAssemblyStatement::Constraint(lhs, rhs, metadata) => {
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
                    true => Ok(ZirAssemblyStatement::Constraint(lhs, rhs, metadata)),
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
                            let common_factor = lqc
                                .quadratic
                                .iter()
                                .scan(None, |state: &mut Option<Vec<&Identifier>>, (_, a, b)| {
                                    // short circuit if we do not have any common factors anymore
                                    if *state == Some(vec![]) {
                                        None
                                    } else {
                                        match state {
                                            // only keep factors found in this term
                                            Some(factors) => {
                                                factors.retain(|&x| x == a || x == b);
                                            }
                                            // initialisation step, start with the two factors in the first term
                                            None => {
                                                *state = Some(vec![a, b]);
                                            }
                                        };
                                        state.clone()
                                    }
                                })
                                .last()
                                .and_then(|mut v| v.pop().cloned());

                            match common_factor {
                                Some(factor) => Ok(FieldElementExpression::Mult(
                                    box lqc
                                        .quadratic
                                        .into_iter()
                                        .map(|(c, i0, i1)| {
                                            let c = T::zero() - c;
                                            let e = match (i0, i1) {
                                                (i0, i1) if factor.eq(&i0) => {
                                                    FieldElementExpression::identifier(i1)
                                                }
                                                (i0, i1) if factor.eq(&i1) => {
                                                    FieldElementExpression::identifier(i0)
                                                }
                                                _ => unreachable!(),
                                            };
                                            FieldElementExpression::Mult(
                                                box FieldElementExpression::Number(c),
                                                box e,
                                            )
                                        })
                                        .fold(
                                            FieldElementExpression::Number(T::from(0)),
                                            |acc, e| FieldElementExpression::Add(box acc, box e),
                                        ),
                                    box FieldElementExpression::identifier(factor),
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

                        Ok(ZirAssemblyStatement::Constraint(lhs, rhs, metadata))
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_ast::common::SourceMetadata;
    use zokrates_field::Bn128Field;

    #[test]
    fn quadratic() {
        // x === a * b;
        let lhs = FieldElementExpression::<Bn128Field>::identifier("x".into());
        let rhs = FieldElementExpression::Mult(
            box FieldElementExpression::identifier("a".into()),
            box FieldElementExpression::identifier("b".into()),
        );

        let expected = ZirAssemblyStatement::Constraint(
            FieldElementExpression::identifier("x".into()),
            FieldElementExpression::Mult(
                box FieldElementExpression::identifier("a".into()),
                box FieldElementExpression::identifier("b".into()),
            ),
            SourceMetadata::default(),
        );
        let result = AssemblyTransformer
            .fold_assembly_statement(ZirAssemblyStatement::Constraint(
                lhs,
                rhs,
                SourceMetadata::default(),
            ))
            .unwrap();

        assert_eq!(result, expected);
    }

    #[test]
    fn non_quadratic() {
        // x === ((a * b) * c);
        let lhs = FieldElementExpression::<Bn128Field>::identifier("x".into());
        let rhs = FieldElementExpression::Mult(
            box FieldElementExpression::Mult(
                box FieldElementExpression::identifier("a".into()),
                box FieldElementExpression::identifier("b".into()),
            ),
            box FieldElementExpression::identifier("c".into()),
        );

        let result = AssemblyTransformer.fold_assembly_statement(ZirAssemblyStatement::Constraint(
            lhs,
            rhs,
            SourceMetadata::default(),
        ));

        assert!(result.is_err());
    }

    #[test]
    fn transform() {
        // x === 1 - a * b; --> (-1) + x === (((-1) * a) * b);
        let lhs = FieldElementExpression::identifier("x".into());
        let rhs = FieldElementExpression::Sub(
            box FieldElementExpression::Number(Bn128Field::from(1)),
            box FieldElementExpression::Mult(
                box FieldElementExpression::identifier("a".into()),
                box FieldElementExpression::identifier("b".into()),
            ),
        );

        let expected = ZirAssemblyStatement::Constraint(
            FieldElementExpression::Add(
                box FieldElementExpression::Number(Bn128Field::from(-1)),
                box FieldElementExpression::identifier("x".into()),
            ),
            FieldElementExpression::Mult(
                box FieldElementExpression::Mult(
                    box FieldElementExpression::Number(Bn128Field::from(-1)),
                    box FieldElementExpression::identifier("a".into()),
                ),
                box FieldElementExpression::identifier("b".into()),
            ),
            SourceMetadata::default(),
        );

        let result = AssemblyTransformer
            .fold_assembly_statement(ZirAssemblyStatement::Constraint(
                lhs,
                rhs,
                SourceMetadata::default(),
            ))
            .unwrap();

        assert_eq!(result, expected);
    }

    #[test]
    fn factorize() {
        // x === (a * b) + (b * c);  -->  x === ((a + c) * b);
        let lhs = FieldElementExpression::<Bn128Field>::identifier("x".into());
        let rhs = FieldElementExpression::Add(
            box FieldElementExpression::Mult(
                box FieldElementExpression::identifier("a".into()),
                box FieldElementExpression::identifier("b".into()),
            ),
            box FieldElementExpression::Mult(
                box FieldElementExpression::identifier("b".into()),
                box FieldElementExpression::identifier("c".into()),
            ),
        );

        let expected = ZirAssemblyStatement::Constraint(
            FieldElementExpression::identifier("x".into()),
            FieldElementExpression::Mult(
                box FieldElementExpression::Add(
                    box FieldElementExpression::identifier("a".into()),
                    box FieldElementExpression::identifier("c".into()),
                ),
                box FieldElementExpression::identifier("b".into()),
            ),
            SourceMetadata::default(),
        );
        let result = AssemblyTransformer
            .fold_assembly_statement(ZirAssemblyStatement::Constraint(
                lhs,
                rhs,
                SourceMetadata::default(),
            ))
            .unwrap();

        assert_eq!(result, expected);
    }

    #[test]
    fn transform_complex() {
        // mid = b*c;
        // x === a+b+c - 2*a*b - 2*a*c - 2*mid + 4*a*mid; // x === a ^ b ^ c
        // -->
        // ((((x + ((-1)*a)) + ((-1)*b)) + ((-1)*c)) + (2*mid)) === (((((-2)*b) + ((-2)*c)) + (4*mid)) * a);
        let lhs = FieldElementExpression::<Bn128Field>::identifier("x".into());
        let rhs = FieldElementExpression::Add(
            box FieldElementExpression::Sub(
                box FieldElementExpression::Sub(
                    box FieldElementExpression::Sub(
                        box FieldElementExpression::Add(
                            box FieldElementExpression::Add(
                                box FieldElementExpression::identifier("a".into()),
                                box FieldElementExpression::identifier("b".into()),
                            ),
                            box FieldElementExpression::identifier("c".into()),
                        ),
                        box FieldElementExpression::Mult(
                            box FieldElementExpression::Mult(
                                box FieldElementExpression::Number(Bn128Field::from(2)),
                                box FieldElementExpression::identifier("a".into()),
                            ),
                            box FieldElementExpression::identifier("b".into()),
                        ),
                    ),
                    box FieldElementExpression::Mult(
                        box FieldElementExpression::Mult(
                            box FieldElementExpression::Number(Bn128Field::from(2)),
                            box FieldElementExpression::identifier("a".into()),
                        ),
                        box FieldElementExpression::identifier("c".into()),
                    ),
                ),
                box FieldElementExpression::Mult(
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                    box FieldElementExpression::identifier("mid".into()),
                ),
            ),
            box FieldElementExpression::Mult(
                box FieldElementExpression::Mult(
                    box FieldElementExpression::Number(Bn128Field::from(4)),
                    box FieldElementExpression::identifier("a".into()),
                ),
                box FieldElementExpression::identifier("mid".into()),
            ),
        );

        let lhs_expected = FieldElementExpression::Add(
            box FieldElementExpression::Add(
                box FieldElementExpression::Add(
                    box FieldElementExpression::Add(
                        box FieldElementExpression::identifier("x".into()),
                        box FieldElementExpression::Mult(
                            box FieldElementExpression::Number(Bn128Field::from(-1)),
                            box FieldElementExpression::identifier("a".into()),
                        ),
                    ),
                    box FieldElementExpression::Mult(
                        box FieldElementExpression::Number(Bn128Field::from(-1)),
                        box FieldElementExpression::identifier("b".into()),
                    ),
                ),
                box FieldElementExpression::Mult(
                    box FieldElementExpression::Number(Bn128Field::from(-1)),
                    box FieldElementExpression::identifier("c".into()),
                ),
            ),
            box FieldElementExpression::Mult(
                box FieldElementExpression::Number(Bn128Field::from(2)),
                box FieldElementExpression::identifier("mid".into()),
            ),
        );

        let rhs_expected = FieldElementExpression::Mult(
            box FieldElementExpression::Add(
                box FieldElementExpression::Add(
                    box FieldElementExpression::Mult(
                        box FieldElementExpression::Number(Bn128Field::from(-2)),
                        box FieldElementExpression::identifier("b".into()),
                    ),
                    box FieldElementExpression::Mult(
                        box FieldElementExpression::Number(Bn128Field::from(-2)),
                        box FieldElementExpression::identifier("c".into()),
                    ),
                ),
                box FieldElementExpression::Mult(
                    box FieldElementExpression::Number(Bn128Field::from(4)),
                    box FieldElementExpression::identifier("mid".into()),
                ),
            ),
            box FieldElementExpression::identifier("a".into()),
        );

        let expected =
            ZirAssemblyStatement::Constraint(lhs_expected, rhs_expected, SourceMetadata::default());
        let result = AssemblyTransformer
            .fold_assembly_statement(ZirAssemblyStatement::Constraint(
                lhs,
                rhs,
                SourceMetadata::default(),
            ))
            .unwrap();

        assert_eq!(result, expected);
    }
}
