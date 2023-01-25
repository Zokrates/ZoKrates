use super::folder::Folder;
use super::{ProgIterator, Statement};
use zokrates_field::Field;

#[derive(Default)]
pub struct Cleaner;

impl<'ast, T: Field, I: IntoIterator<Item = Statement<'ast, T>>> ProgIterator<'ast, T, I> {
    pub fn clean(self) -> ProgIterator<'ast, T, impl IntoIterator<Item = Statement<'ast, T>>> {
        ProgIterator {
            arguments: self.arguments,
            return_count: self.return_count,
            statements: self
                .statements
                .into_iter()
                .flat_map(|s| Cleaner::default().fold_statement(s)),
            solvers: self.solvers,
        }
    }
}

impl<'ast, T: Field> Folder<'ast, T> for Cleaner {
    fn fold_statement(&mut self, s: Statement<'ast, T>) -> Vec<Statement<'ast, T>> {
        match s {
            Statement::Block(statements) => statements
                .into_iter()
                .flat_map(|s| self.fold_statement(s))
                .collect(),
            s => vec![s],
        }
    }
}
