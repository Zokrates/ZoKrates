use crate::common::WithSpan;

use super::folder::Folder;
use super::{ProgIterator, Statement};
use zokrates_field::Field;

#[derive(Default)]
pub struct Cleaner;

impl<'ast, T: Field, I: IntoIterator<Item = Statement<'ast, T>>> ProgIterator<'ast, T, I> {
    pub fn clean(self) -> ProgIterator<'ast, T, impl IntoIterator<Item = Statement<'ast, T>>> {
        ProgIterator {
            module_map: self.module_map,
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
        if s.get_span().is_none() {
            eprintln!("Internal compiler warning: found a statement without source information. Please open an issue https://github.com/Zokrates/ZoKrates/issues/new?template=bug_report.md");
        }

        match s {
            Statement::Block(s) => s
                .inner
                .into_iter()
                .flat_map(|s| self.fold_statement(s))
                .collect(),
            s => vec![s],
        }
    }
}
