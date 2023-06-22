use std::fmt;
use zokrates_ast::typed::{result_folder::*, AssemblyAssignment, UExpression};
use zokrates_ast::typed::{
    FieldElementExpression, TypedAssemblyStatement, TypedProgram, UBitwidth, UExpressionInner,
};
use zokrates_field::Field;

#[derive(Debug, PartialEq, Eq)]
pub struct Error(String);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub struct ExpressionValidator;

impl ExpressionValidator {
    pub fn validate<T: Field>(p: TypedProgram<T>) -> Result<TypedProgram<T>, Error> {
        ExpressionValidator.fold_program(p)
    }
}

impl<'ast, T: Field> ResultFolder<'ast, T> for ExpressionValidator {
    type Error = Error;

    // we allow more dynamic expressions in witness generation
    fn fold_assembly_assignment(
        &mut self,
        s: AssemblyAssignment<'ast, T>,
    ) -> Result<Vec<TypedAssemblyStatement<'ast, T>>, Self::Error> {
        Ok(vec![TypedAssemblyStatement::Assignment(s)])
    }

    fn fold_field_expression_cases(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> Result<FieldElementExpression<'ast, T>, Self::Error> {
        match e {
            // these should have been propagated away
            FieldElementExpression::And(_)
            | FieldElementExpression::Or(_)
            | FieldElementExpression::Xor(_)
            | FieldElementExpression::LeftShift(_)
            | FieldElementExpression::RightShift(_) => Err(Error(format!(
                "Found non-constant bitwise operation in field element expression `{}`",
                e
            ))),
            FieldElementExpression::Pow(e) => {
                let base = self.fold_field_expression(*e.left)?;
                let exp = self.fold_uint_expression(*e.right)?;

                match exp.as_inner() {
                    UExpressionInner::Value(_) => Ok(FieldElementExpression::pow(base, exp)),
                    exp => Err(Error(format!(
                        "Found non-constant exponent in power expression `{}**{}`",
                        base,
                        exp.clone().annotate(UBitwidth::B32)
                    ))),
                }
            }
            e => fold_field_expression_cases(self, e),
        }
    }

    fn fold_uint_expression_cases(
        &mut self,
        bitwidth: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> Result<UExpressionInner<'ast, T>, Error> {
        match e {
            UExpressionInner::LeftShift(e) => {
                let expr = self.fold_uint_expression(*e.left)?;
                let by = self.fold_uint_expression(*e.right)?;

                match by.as_inner() {
                    UExpressionInner::Value(_) => {
                        Ok(UExpression::left_shift(expr, by).into_inner())
                    }
                    _ => Err(Error(format!(
                        "Cannot shift by a variable value, found `{}`",
                        UExpression::left_shift(expr, by)
                    ))),
                }
            }
            UExpressionInner::RightShift(e) => {
                let expr = self.fold_uint_expression(*e.left)?;
                let by = self.fold_uint_expression(*e.right)?;

                match by.as_inner() {
                    UExpressionInner::Value(_) => {
                        Ok(UExpression::right_shift(expr, by).into_inner())
                    }
                    _ => Err(Error(format!(
                        "Cannot shift by a variable value, found `{}`",
                        UExpression::right_shift(expr, by)
                    ))),
                }
            }
            e => fold_uint_expression_cases(self, bitwidth, e),
        }
    }
}
