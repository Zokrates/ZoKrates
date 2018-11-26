//! Module containing the `DeadCodeOptimizer` to remove code that will never be executed

use field::Field;
use flat_absy::{FlatProg, Folder};

pub struct DeadCodeOptimizer {}

impl DeadCodeOptimizer {
    fn new() -> DeadCodeOptimizer {
        DeadCodeOptimizer {}
    }

    pub fn optimize<T: Field>(p: FlatProg<T>) -> FlatProg<T> {
        DeadCodeOptimizer::new().fold_program(p)
    }
}

impl<T: Field> Folder<T> for DeadCodeOptimizer {
    fn fold_program(&mut self, prog: FlatProg<T>) -> FlatProg<T> {
        FlatProg {
            functions: prog
                .functions
                .into_iter()
                .filter_map(|func| {
                    if func.id == "main" {
                        return Some(self.fold_function(func));
                    }
                    return None;
                })
                .collect(),
        }
    }
}
