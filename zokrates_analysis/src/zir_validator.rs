use std::fmt;
use zokrates_ast::zir::result_folder::{
    fold_assembly_statement, fold_field_expression, ResultFolder,
};
use zokrates_ast::zir::{FieldElementExpression, ZirAssemblyStatement, ZirProgram};
use zokrates_field::Field;

#[derive(Debug)]
pub struct Error(String);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub struct ZirValidator;

impl ZirValidator {
    pub fn validate<T: Field>(p: ZirProgram<T>) -> Result<ZirProgram<T>, Error> {
        let mut checker = ZirValidator;
        checker.fold_program(p)
    }
}

impl<'ast, T: Field> ResultFolder<'ast, T> for ZirValidator {
    type Error = Error;

    fn fold_assembly_statement(
        &mut self,
        s: ZirAssemblyStatement<'ast, T>,
    ) -> Result<ZirAssemblyStatement<'ast, T>, Self::Error> {
        match s {
            ZirAssemblyStatement::Assignment(_, _) => Ok(s),
            s => fold_assembly_statement(self, s),
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
