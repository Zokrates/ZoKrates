// A static analyser pass to transform user-defined constraints to the form `lin_comb === quad_comb`
// This pass can fail if a non-quadratic constraint is found which cannot be transformed to the expected form

use crate::ZirPropagator;
use std::fmt;
use std::ops::*;
use zokrates_ast::zir::lqc::LinQuadComb;
use zokrates_ast::zir::result_folder::ResultFolder;
use zokrates_ast::zir::AssemblyConstraint;
use zokrates_ast::zir::{
    Expr, FieldElementExpression, Id, Identifier, ZirAssemblyStatement, ZirProgram,
};
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

    fn fold_assembly_constraint(
        &mut self,
        s: AssemblyConstraint<'ast, T>,
    ) -> Result<Vec<ZirAssemblyStatement<'ast, T>>, Self::Error> {
        let lhs = self.fold_field_expression(s.left)?;
        let rhs = self.fold_field_expression(s.right)?;

        let (is_quadratic, lhs, rhs) = match (lhs, rhs) {
            (
                lhs @ FieldElementExpression::Identifier(..),
                rhs @ FieldElementExpression::Identifier(..),
            ) => (true, lhs, rhs),
            (FieldElementExpression::Mult(e), other) | (other, FieldElementExpression::Mult(e))
                if other.is_linear() =>
            {
                (
                    e.left.is_linear() && e.right.is_linear(),
                    other,
                    FieldElementExpression::Mult(e),
                )
            }
            (lhs, rhs) => (false, lhs, rhs),
        };

        match is_quadratic {
            true => Ok(vec![ZirAssemblyStatement::constraint(lhs, rhs, s.metadata)]),
            false => {
                let sub = FieldElementExpression::sub(lhs, rhs);
                let mut lqc = LinQuadComb::try_from(sub.clone())
                    .map_err(|_| Error("Non-quadratic constraints are not allowed".to_string()))?;

                let linear = lqc
                    .linear
                    .into_iter()
                    .map(|(c, i)| {
                        FieldElementExpression::mul(
                            FieldElementExpression::value(c),
                            FieldElementExpression::identifier(i),
                        )
                    })
                    .fold(FieldElementExpression::value(T::from(0)), |acc, e| {
                        FieldElementExpression::add(acc, e)
                    });

                let lhs = FieldElementExpression::add(
                    FieldElementExpression::value(lqc.constant),
                    linear,
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
                        Some(factor) => Ok(FieldElementExpression::mul(
                            lqc.quadratic
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
                                    FieldElementExpression::mul(FieldElementExpression::value(c), e)
                                })
                                .fold(
                                    FieldElementExpression::value(T::from(0)),
                                    FieldElementExpression::add,
                                ),
                            FieldElementExpression::identifier(factor),
                        )),
                        None => Err(Error(
                            "Non-quadratic constraints are not allowed".to_string(),
                        )),
                    }?
                } else {
                    lqc.quadratic
                        .pop()
                        .map(|(c, i0, i1)| {
                            FieldElementExpression::mul(
                                FieldElementExpression::mul(
                                    FieldElementExpression::value(T::zero() - c),
                                    FieldElementExpression::identifier(i0),
                                ),
                                FieldElementExpression::identifier(i1),
                            )
                        })
                        .unwrap_or_else(|| FieldElementExpression::value(T::from(0)))
                };

                let mut propagator = ZirPropagator::default();
                let lhs = propagator
                    .fold_field_expression(lhs)
                    .map_err(|e| Error(e.to_string()))?;

                let rhs = propagator
                    .fold_field_expression(rhs)
                    .map_err(|e| Error(e.to_string()))?;

                Ok(vec![ZirAssemblyStatement::constraint(lhs, rhs, s.metadata)])
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
        let rhs = FieldElementExpression::mul(
            FieldElementExpression::identifier("a".into()),
            FieldElementExpression::identifier("b".into()),
        );

        let expected = vec![ZirAssemblyStatement::constraint(
            FieldElementExpression::identifier("x".into()),
            FieldElementExpression::mul(
                FieldElementExpression::identifier("a".into()),
                FieldElementExpression::identifier("b".into()),
            ),
            SourceMetadata::default(),
        )];
        let result = AssemblyTransformer
            .fold_assembly_statement(ZirAssemblyStatement::constraint(
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
        let rhs = FieldElementExpression::mul(
            FieldElementExpression::mul(
                FieldElementExpression::identifier("a".into()),
                FieldElementExpression::identifier("b".into()),
            ),
            FieldElementExpression::identifier("c".into()),
        );

        let result = AssemblyTransformer.fold_assembly_statement(ZirAssemblyStatement::constraint(
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
        let rhs = FieldElementExpression::sub(
            FieldElementExpression::value(Bn128Field::from(1)),
            FieldElementExpression::mul(
                FieldElementExpression::identifier("a".into()),
                FieldElementExpression::identifier("b".into()),
            ),
        );

        let expected = vec![ZirAssemblyStatement::constraint(
            FieldElementExpression::add(
                FieldElementExpression::value(Bn128Field::from(-1)),
                FieldElementExpression::identifier("x".into()),
            ),
            FieldElementExpression::mul(
                FieldElementExpression::mul(
                    FieldElementExpression::value(Bn128Field::from(-1)),
                    FieldElementExpression::identifier("a".into()),
                ),
                FieldElementExpression::identifier("b".into()),
            ),
            SourceMetadata::default(),
        )];

        let result = AssemblyTransformer
            .fold_assembly_statement(ZirAssemblyStatement::constraint(
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
        let rhs = FieldElementExpression::add(
            FieldElementExpression::mul(
                FieldElementExpression::identifier("a".into()),
                FieldElementExpression::identifier("b".into()),
            ),
            FieldElementExpression::mul(
                FieldElementExpression::identifier("b".into()),
                FieldElementExpression::identifier("c".into()),
            ),
        );

        let expected = vec![ZirAssemblyStatement::constraint(
            FieldElementExpression::identifier("x".into()),
            FieldElementExpression::mul(
                FieldElementExpression::add(
                    FieldElementExpression::identifier("a".into()),
                    FieldElementExpression::identifier("c".into()),
                ),
                FieldElementExpression::identifier("b".into()),
            ),
            SourceMetadata::default(),
        )];
        let result = AssemblyTransformer
            .fold_assembly_statement(ZirAssemblyStatement::constraint(
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
        let rhs = FieldElementExpression::add(
            FieldElementExpression::sub(
                FieldElementExpression::sub(
                    FieldElementExpression::sub(
                        FieldElementExpression::add(
                            FieldElementExpression::add(
                                FieldElementExpression::identifier("a".into()),
                                FieldElementExpression::identifier("b".into()),
                            ),
                            FieldElementExpression::identifier("c".into()),
                        ),
                        FieldElementExpression::mul(
                            FieldElementExpression::mul(
                                FieldElementExpression::value(Bn128Field::from(2)),
                                FieldElementExpression::identifier("a".into()),
                            ),
                            FieldElementExpression::identifier("b".into()),
                        ),
                    ),
                    FieldElementExpression::mul(
                        FieldElementExpression::mul(
                            FieldElementExpression::value(Bn128Field::from(2)),
                            FieldElementExpression::identifier("a".into()),
                        ),
                        FieldElementExpression::identifier("c".into()),
                    ),
                ),
                FieldElementExpression::mul(
                    FieldElementExpression::value(Bn128Field::from(2)),
                    FieldElementExpression::identifier("mid".into()),
                ),
            ),
            FieldElementExpression::mul(
                FieldElementExpression::mul(
                    FieldElementExpression::value(Bn128Field::from(4)),
                    FieldElementExpression::identifier("a".into()),
                ),
                FieldElementExpression::identifier("mid".into()),
            ),
        );

        let lhs_expected = FieldElementExpression::add(
            FieldElementExpression::add(
                FieldElementExpression::add(
                    FieldElementExpression::add(
                        FieldElementExpression::identifier("x".into()),
                        FieldElementExpression::mul(
                            FieldElementExpression::value(Bn128Field::from(-1)),
                            FieldElementExpression::identifier("a".into()),
                        ),
                    ),
                    FieldElementExpression::mul(
                        FieldElementExpression::value(Bn128Field::from(-1)),
                        FieldElementExpression::identifier("b".into()),
                    ),
                ),
                FieldElementExpression::mul(
                    FieldElementExpression::value(Bn128Field::from(-1)),
                    FieldElementExpression::identifier("c".into()),
                ),
            ),
            FieldElementExpression::mul(
                FieldElementExpression::value(Bn128Field::from(2)),
                FieldElementExpression::identifier("mid".into()),
            ),
        );

        let rhs_expected = FieldElementExpression::mul(
            FieldElementExpression::add(
                FieldElementExpression::add(
                    FieldElementExpression::mul(
                        FieldElementExpression::value(Bn128Field::from(-2)),
                        FieldElementExpression::identifier("b".into()),
                    ),
                    FieldElementExpression::mul(
                        FieldElementExpression::value(Bn128Field::from(-2)),
                        FieldElementExpression::identifier("c".into()),
                    ),
                ),
                FieldElementExpression::mul(
                    FieldElementExpression::value(Bn128Field::from(4)),
                    FieldElementExpression::identifier("mid".into()),
                ),
            ),
            FieldElementExpression::identifier("a".into()),
        );

        let expected = vec![ZirAssemblyStatement::constraint(
            lhs_expected,
            rhs_expected,
            SourceMetadata::default(),
        )];
        let result = AssemblyTransformer
            .fold_assembly_statement(ZirAssemblyStatement::constraint(
                lhs,
                rhs,
                SourceMetadata::default(),
            ))
            .unwrap();

        assert_eq!(result, expected);
    }
}
