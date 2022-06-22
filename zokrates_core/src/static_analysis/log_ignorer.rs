use crate::typed_absy::{folder::*, TypedProgram, TypedStatement};
use zokrates_field::Field;

#[derive(Default)]
pub struct LogIgnorer;

impl LogIgnorer {
    pub fn ignore<'ast, T: Field>(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        Self::default().fold_program(p)
    }
}

impl<'ast, T: Field> Folder<'ast, T> for LogIgnorer {
    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        match s {
            TypedStatement::Log(..) => vec![],
            s => fold_statement(self, s),
        }
    }
}
