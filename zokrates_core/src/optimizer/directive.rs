//! Module containing the `RedefinitionOptimizer` to remove code of the form
// ```
// b := Directive(a)
// c := Directive(a)
// ```
// and replace by
// ```
// b := Directive(a)
// c := b
// ```

use crate::flat_absy::flat_variable::FlatVariable;
use crate::ir::folder::*;
use crate::ir::*;
use crate::optimizer::canonicalizer::Canonicalizer;
use crate::solvers::Solver;
use std::collections::hash_map::{Entry, HashMap};
use zokrates_field::Field;

#[derive(Debug, Default)]
pub struct DirectiveOptimizer<T> {
    calls: HashMap<(Solver, Vec<QuadComb<T>>), Vec<FlatVariable>>,
    /// Map of renamings for reassigned variables while processing the program.
    substitution: HashMap<FlatVariable, FlatVariable>,
}

impl<T: Field> Folder<T> for DirectiveOptimizer<T> {
    fn fold_module(&mut self, p: Prog<T>) -> Prog<T> {
        // in order to correctly identify duplicates, we need to first canonicalize the statements

        let mut canonicalizer = Canonicalizer;

        let p = Prog {
            statements: p
                .statements
                .into_iter()
                .flat_map(|s| canonicalizer.fold_statement(s))
                .collect(),
            ..p
        };

        fold_module(self, p)
    }

    fn fold_variable(&mut self, v: FlatVariable) -> FlatVariable {
        *self.substitution.get(&v).unwrap_or(&v)
    }

    fn fold_statement(&mut self, s: Statement<T>) -> Vec<Statement<T>> {
        match s {
            Statement::Directive(d) => {
                let d = self.fold_directive(d);

                match self.calls.entry((d.solver.clone(), d.inputs.clone())) {
                    Entry::Vacant(e) => {
                        e.insert(d.outputs.clone());
                        vec![Statement::Directive(d)]
                    }
                    Entry::Occupied(e) => {
                        self.substitution
                            .extend(d.outputs.into_iter().zip(e.get().iter().cloned()));
                        vec![]
                    }
                }
            }
            s => fold_statement(self, s),
        }
    }
}

#[cfg(test)]
mod tests {}
