use std::fmt;
use zokrates_ast::zir::lqc::LinQuadComb;
use zokrates_ast::zir::result_folder::{fold_field_expression, ResultFolder};
use zokrates_ast::zir::{FieldElementExpression, ZirAssemblyStatement, ZirProgram};
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
                let sub = FieldElementExpression::Sub(box lhs, box rhs);

                // let sub = match (lhs, rhs) {
                //     (FieldElementExpression::Number(n), e)
                //     | (e, FieldElementExpression::Number(n)) => {
                //         FieldElementExpression::Sub(box FieldElementExpression::Number(n), box e)
                //     }
                //     (lhs, rhs) => FieldElementExpression::Sub(box lhs, box rhs),
                // };

                let mut lqc = LinQuadComb::try_from(sub.clone()).map_err(|_| {
                    Error("Found forbidden operation in user-defined constraint".to_string())
                })?;

                println!("{:#?}", lqc);

                if lqc.quadratic.len() > 1 {
                    return Err(Error(
                        "Non-quadratic constraints are not allowed".to_string(),
                    ));
                }

                let linear = lqc
                    .linear
                    .into_iter()
                    .filter_map(|(c, i)| match c {
                        c if c == T::from(0) => None,
                        c if c == T::from(1) => Some(FieldElementExpression::Identifier(i)),
                        _ => Some(FieldElementExpression::Mult(
                            box FieldElementExpression::Number(c),
                            box FieldElementExpression::Identifier(i),
                        )),
                    })
                    .reduce(|p, n| FieldElementExpression::Add(box p, box n))
                    .unwrap();

                let lhs = match lqc.constant {
                    c if c == T::from(0) => linear,
                    c => FieldElementExpression::Add(
                        box FieldElementExpression::Number(c),
                        box linear,
                    ),
                };

                let rhs: FieldElementExpression<'ast, T> = lqc
                    .quadratic
                    .pop()
                    .map(|(c, i0, i1)| {
                        FieldElementExpression::Mult(
                            box FieldElementExpression::Mult(
                                box FieldElementExpression::Number(T::zero() - c),
                                box FieldElementExpression::Identifier(i0),
                            ),
                            box FieldElementExpression::Identifier(i1),
                        )
                    })
                    .unwrap_or_else(|| FieldElementExpression::Number(T::from(0)));

                println!("{} == {}", lhs, rhs);

                Ok(ZirAssemblyStatement::Constraint(lhs, rhs))
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
