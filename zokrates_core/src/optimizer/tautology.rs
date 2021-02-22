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

pub struct TautologyOptimizer {}

impl TautologyOptimizer {
    fn new() -> TautologyOptimizer {
        TautologyOptimizer {}
    }

    pub fn optimize<T: Field>(p: Prog<T>) -> Prog<T> {
        TautologyOptimizer::new().fold_module(p)
    }
}

impl<T: Field> Folder<T> for TautologyOptimizer {
    fn fold_statement(&mut self, s: Statement<T>) -> Vec<Statement<T>> {
        match s {
            Statement::Constraint(quad, lin) => match quad.try_linear() {
                Ok(l) => {
                    if l == lin {
                        vec![]
                    } else {
                        vec![Statement::Constraint(l.into(), lin)]
                    }
                }
                Err(quad) => vec![Statement::Constraint(quad, lin)],
            },
            _ => fold_statement(self, s),
        }
    }
}

#[cfg(test)]
mod tests {}
