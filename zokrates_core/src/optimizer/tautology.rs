//! Module containing the `TautologyOptimizer` to remove code of the form
// ```
// a * 1 == a
// ```
//
// This makes the assumption that ~one has value 1, as should be guaranteed by the verifier

use zokrates_ast::ir::folder::Folder;
use zokrates_ast::ir::*;
use zokrates_field::Field;

#[derive(Default)]
pub struct TautologyOptimizer;

impl<'ast, T: Field> Folder<'ast, T> for TautologyOptimizer {
    fn fold_constraint_statement(&mut self, s: ConstraintStatement<T>) -> Vec<Statement<'ast, T>> {
        match s.quad.try_linear() {
            Ok(l) => {
                if l == s.lin {
                    vec![]
                } else {
                    vec![Statement::constraint(l, s.lin, s.error)]
                }
            }
            Err(quad) => vec![Statement::constraint(quad, s.lin, s.error)],
        }
    }
}

#[cfg(test)]
mod tests {}
