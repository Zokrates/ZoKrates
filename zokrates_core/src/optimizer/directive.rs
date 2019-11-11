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

use helpers::Helper;
use crate::flat_absy::flat_variable::FlatVariable;
use crate::ir::folder::*;
use crate::ir::LinComb;
use crate::ir::*;
use num::Zero;
use std::collections::hash_map::{HashMap, Entry};
use zokrates_field::field::Field;

#[derive(Debug)]
pub struct DirectiveOptimizer<T: Field> {
    calls: HashMap<(Helper, Vec<LinComb<T>>), Vec<FlatVariable>>,
    /// Map of renamings for reassigned variables while processing the program.
    substitution: HashMap<FlatVariable, FlatVariable>,
}

impl<T: Field> DirectiveOptimizer<T> {
    fn new() -> DirectiveOptimizer<T> {
        DirectiveOptimizer {
            calls: HashMap::new(),
            substitution: HashMap::new(),
        }
    }

    pub fn optimize(p: Prog<T>) -> Prog<T> {
        DirectiveOptimizer::new().fold_module(p)
    }
}

impl<T: Field> Folder<T> for DirectiveOptimizer<T> {
    fn fold_statement(&mut self, s: Statement<T>) -> Vec<Statement<T>> {
        println!("{:?}", s);
        match s {
            Statement::Directive(d) => {
                let d = self.fold_directive(d);

                match self.calls.entry((d.helper.clone(), d.inputs.clone())) {
                    Entry::Vacant(e) => {
                        e.insert(d.outputs.clone());
                        vec![Statement::Directive(d)]
                    },
                    Entry::Occupied(e) => {
                        self.substitution.extend(d.outputs.into_iter().zip(e.get().into_iter().cloned()));
                        vec![]
                    }
                }            
            },
            s => fold_statement(self, s)
        }
    }

    fn fold_variable(&mut self, v: FlatVariable) -> FlatVariable {
        *self.substitution.get(&v).unwrap_or(&v)
    }
}

#[cfg(test)]
mod tests {

}
