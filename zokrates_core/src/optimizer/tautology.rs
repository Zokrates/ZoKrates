//! Module containing the `TautologyOptimizer` to remove code of the form
// ```
// a * 1 == a
// ```
//
// This makes the assumption that ~one has value 1, as should be guaranteed by the verifier

use zokrates_ast::ir::folder::fold_statement;
use zokrates_ast::ir::folder::Folder;
use zokrates_ast::ir::*;
use zokrates_field::Field;

#[derive(Default)]
pub struct TautologyOptimizer;

impl<T: Field> Folder<T> for TautologyOptimizer {
    fn fold_statement(&mut self, s: Statement<T>) -> Vec<Statement<T>> {
        match s {
            Statement::Constraint(quad, lin, message) => match quad.try_linear() {
                Ok(l) => {
                    if l == lin {
                        vec![]
                    } else {
                        vec![Statement::Constraint(l.into(), lin, message)]
                    }
                }
                Err(quad) => vec![Statement::Constraint(quad, lin, message)],
            },
            _ => fold_statement(self, s),
        }
    }
}

#[cfg(test)]
mod tests {}
