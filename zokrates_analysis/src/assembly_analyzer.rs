use std::fmt;
use zokrates_ast::typed::result_folder::{
    fold_assembly_statement, fold_field_expression, ResultFolder,
};
use zokrates_ast::typed::{FieldElementExpression, TypedAssemblyStatement, TypedProgram};
use zokrates_field::Field;

#[derive(Debug)]
pub struct Error(String);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub struct AssemblyAnalyzer;

impl AssemblyAnalyzer {
    pub fn analyze<T: Field>(p: TypedProgram<T>) -> Result<TypedProgram<T>, Error> {
        let mut checker = AssemblyAnalyzer;
        checker.fold_program(p)
    }
}

impl<'ast, T: Field> ResultFolder<'ast, T> for AssemblyAnalyzer {
    type Error = Error;

    fn fold_assembly_statement(
        &mut self,
        s: TypedAssemblyStatement<'ast, T>,
    ) -> Result<TypedAssemblyStatement<'ast, T>, Self::Error> {
        match s {
            TypedAssemblyStatement::Assignment(_, _) => Ok(s),
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
                "Bitwise operations on field elements are allowed only in witness assignment statement"
                    .to_string(),
            )),
            e => fold_field_expression(self, e),
        }
    }
}
