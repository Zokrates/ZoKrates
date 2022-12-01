use std::fmt;
use zokrates_ast::typed::result_folder::{
    fold_assembly_statement, fold_field_expression, fold_uint_expression_inner, ResultFolder,
};
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

    fn fold_assembly_statement(
        &mut self,
        s: TypedAssemblyStatement<'ast, T>,
    ) -> Result<TypedAssemblyStatement<'ast, T>, Self::Error> {
        match s {
            // we allow more dynamic expressions in witness generation
            TypedAssemblyStatement::Assignment(_, _) => Ok(s),
            s => fold_assembly_statement(self, s),
        }
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> Result<FieldElementExpression<'ast, T>, Self::Error> {
        match e {
            // these should have been propagated away
            FieldElementExpression::And(_, _)
            | FieldElementExpression::Or(_, _)
            | FieldElementExpression::Xor(_, _)
            | FieldElementExpression::LeftShift(_, _)
            | FieldElementExpression::RightShift(_, _) => Err(Error(format!(
                "Found non-constant bitwise operation in field element expression `{}`",
                e
            ))),
            FieldElementExpression::Pow(box e, box exp) => {
                let e = self.fold_field_expression(e)?;
                let exp = self.fold_uint_expression(exp)?;

                match exp.as_inner() {
                    UExpressionInner::Value(_) => Ok(FieldElementExpression::Pow(box e, box exp)),
                    exp => Err(Error(format!(
                        "Found non-constant exponent in power expression `{}**{}`",
                        e,
                        exp.clone().annotate(UBitwidth::B32)
                    ))),
                }
            }
            e => fold_field_expression(self, e),
        }
    }

    fn fold_uint_expression_inner(
        &mut self,
        bitwidth: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> Result<UExpressionInner<'ast, T>, Error> {
        match e {
            UExpressionInner::LeftShift(box e, box by) => {
                let e = self.fold_uint_expression(e)?;
                let by = self.fold_uint_expression(by)?;

                match by.as_inner() {
                    UExpressionInner::Value(_) => Ok(UExpressionInner::LeftShift(box e, box by)),
                    by => Err(Error(format!(
                        "Cannot shift by a variable value, found `{} << {}`",
                        e,
                        by.clone().annotate(UBitwidth::B32)
                    ))),
                }
            }
            UExpressionInner::RightShift(box e, box by) => {
                let e = self.fold_uint_expression(e)?;
                let by = self.fold_uint_expression(by)?;

                match by.as_inner() {
                    UExpressionInner::Value(_) => Ok(UExpressionInner::RightShift(box e, box by)),
                    by => Err(Error(format!(
                        "Cannot shift by a variable value, found `{} >> {}`",
                        e,
                        by.clone().annotate(UBitwidth::B32)
                    ))),
                }
            }
            e => fold_uint_expression_inner(self, bitwidth, e),
        }
    }
}
