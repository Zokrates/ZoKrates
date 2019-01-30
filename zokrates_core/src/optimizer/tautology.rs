//! Module containing the `TautologyOptimizer` to remove code of the form
// ```
// a * 1 == a
// ```

use ir::folder::fold_statement;
use ir::folder::Folder;
use ir::*;
use zokrates_field::field::Field;

pub struct TautologyOptimizer {}

impl TautologyOptimizer {
    fn new() -> TautologyOptimizer {
        TautologyOptimizer {}
    }

    pub fn optimize<T: Field>(p: Prog<T>) -> Prog<T> {
        TautologyOptimizer::new().fold_program(p)
    }
}

impl<T: Field> Folder<T> for TautologyOptimizer {
    fn fold_statement(&mut self, s: Statement<T>) -> Vec<Statement<T>> {
        match s {
            Statement::Constraint(quad, lin) => {
                match quad.try_linear() {
                    Some(l) => {
                        if l == lin {
                            return vec![];
                        }
                    }
                    None => {}
                }
                vec![Statement::Constraint(quad, lin)]
            }
            _ => fold_statement(self, s),
        }
    }
}

#[cfg(test)]
mod tests {}
