use zokrates_ast::typed::{folder::*, LogStatement, TypedProgram, TypedStatement};
use zokrates_field::Field;

#[derive(Default)]
pub struct LogIgnorer;

impl LogIgnorer {
    pub fn ignore<T: Field>(p: TypedProgram<T>) -> TypedProgram<T> {
        Self::default().fold_program(p)
    }
}

impl<'ast, T: Field> Folder<'ast, T> for LogIgnorer {
    fn fold_log_statement(&mut self, _: LogStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        vec![]
    }
}
