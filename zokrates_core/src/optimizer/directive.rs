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

use std::collections::hash_map::{Entry, HashMap};
use zokrates_ast::ir::folder::*;
use zokrates_ast::ir::*;
use zokrates_field::Field;

#[derive(Debug, Default)]
pub struct DirectiveOptimizer<T> {
    calls: HashMap<(Solver, Vec<QuadComb<T>>), Vec<Variable>>,
    /// Map of renamings for reassigned variables while processing the program.
    substitution: HashMap<Variable, Variable>,
}

impl<T: Field> Folder<T> for DirectiveOptimizer<T> {
    fn fold_variable(&mut self, v: Variable) -> Variable {
        *self.substitution.get(&v).unwrap_or(&v)
    }

    fn fold_directive_statement(&mut self, d: DirectiveStatement<T>) -> Vec<Statement<T>> {
        let d = DirectiveStatement {
            inputs: d
                .inputs
                .into_iter()
                .map(|e| self.fold_quadratic_combination(e))
                .collect(),
            outputs: d
                .outputs
                .into_iter()
                .map(|o| self.fold_variable(o))
                .collect(),
            ..d
        };

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
}

// #[cfg(test)]
// mod tests {}
