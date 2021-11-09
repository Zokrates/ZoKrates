//! Module containing the `TautologyOptimizer` to remove code of the form
// ```
// a * 1 == a
// ```
//
// This makes the assumption that ~one has value 1, as should be guaranteed by the verifier

use crate::ir::folder::fold_statement;
use crate::ir::folder::Folder;
use crate::ir::*;
use zokrates_field::Field;

#[derive(Default)]
pub struct TautologyOptimizer;

impl<T: Field> Folder<T> for TautologyOptimizer {
    fn fold_statement(&mut self, s: Statement<T>) -> Result<MemoryStatements<T>, ()> {
        Ok(match s {
            Statement::Constraint(quad, lin, message) => match quad.try_linear() {
                Ok(l) => {
                    if l == lin {
                        MemoryStatements(vec![])
                    } else {
                        MemoryStatements(vec![Statement::Constraint(l.into(), lin, message)])
                    }
                }
                Err(quad) => MemoryStatements(vec![Statement::Constraint(quad, lin, message)]),
            },
            _ => fold_statement(self, s),
        })
    }
}

#[cfg(test)]
mod tests {}
