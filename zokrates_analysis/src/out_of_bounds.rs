use std::fmt;
use zokrates_ast::typed::{
    result_folder::*, Expr, SelectExpression, SelectOrExpression, Type, TypedAssignee,
    TypedProgram, UExpressionInner,
};
use zokrates_field::Field;

#[derive(Default)]
pub struct OutOfBoundsChecker;

#[derive(Debug)]
pub struct Error(String);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl OutOfBoundsChecker {
    pub fn check<T: Field>(p: TypedProgram<T>) -> Result<TypedProgram<T>, Error> {
        Self::default().fold_program(p)
    }
}

impl<'ast, T: Field> ResultFolder<'ast, T> for OutOfBoundsChecker {
    type Error = Error;

    fn fold_select_expression<E: Expr<'ast, T>>(
        &mut self,
        _: &E::Ty,
        s: SelectExpression<'ast, T, E>,
    ) -> Result<SelectOrExpression<'ast, T, E>, Self::Error> {
        match (s.index.as_inner(), s.array.size().as_inner()) {
            (UExpressionInner::Value(index), UExpressionInner::Value(size)) if index >= size => {
                Err(Error(format!(
                    "Out of bounds access `{}` because `{}` has size {}",
                    s, s.array, size
                )))
            }
            _ => Ok(SelectOrExpression::Select(s)),
        }
    }

    fn fold_assignee(
        &mut self,
        a: TypedAssignee<'ast, T>,
    ) -> Result<TypedAssignee<'ast, T>, Error> {
        match a {
            TypedAssignee::Select(box array, box index) => {
                use zokrates_ast::typed::Typed;

                let array = self.fold_assignee(array)?;

                let size = match array.get_type() {
                    Type::Array(array_ty) => match array_ty.size.as_inner() {
                        UExpressionInner::Value(size) => *size,
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                };

                match index.as_inner() {
                    UExpressionInner::Value(i) if i >= &size => Err(Error(format!(
                        "Out of bounds write to `{}` because `{}` has size {}",
                        TypedAssignee::Select(box array.clone(), box index),
                        array,
                        size
                    ))),
                    _ => Ok(TypedAssignee::Select(
                        box self.fold_assignee(array)?,
                        box self.fold_uint_expression(index)?,
                    )),
                }
            }
            a => fold_assignee(self, a),
        }
    }
}
