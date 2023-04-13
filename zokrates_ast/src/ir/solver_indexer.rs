use crate::common::RefCall;
use crate::ir::folder::Folder;
use crate::ir::Solver;
use crate::zir::ZirFunction;
use std::collections::hash_map::DefaultHasher;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use zokrates_field::Field;

use super::DirectiveStatement;
use super::Statement;

type Hash = u64;

fn hash<T: Field>(f: &ZirFunction<T>) -> Hash {
    use std::hash::Hash;
    use std::hash::Hasher;
    let mut hasher = DefaultHasher::new();
    f.hash(&mut hasher);
    hasher.finish()
}

#[derive(Debug, Default)]
pub struct SolverIndexer<'ast, T> {
    pub solvers: Vec<Solver<'ast, T>>,
    pub index_map: HashMap<Hash, usize>,
}

impl<'ast, T: Field> Folder<'ast, T> for SolverIndexer<'ast, T> {
    fn fold_directive_statement(
        &mut self,
        d: DirectiveStatement<'ast, T>,
    ) -> Vec<Statement<'ast, T>> {
        let res = match d.solver {
            Solver::Zir(f) => {
                let argument_count = f.arguments.len();
                let h = hash(&f);
                let index = match self.index_map.entry(h) {
                    Entry::Occupied(v) => *v.get(),
                    Entry::Vacant(entry) => {
                        let index = self.solvers.len();
                        entry.insert(index);
                        self.solvers.push(Solver::Zir(f));
                        index
                    }
                };
                DirectiveStatement::new(
                    d.outputs,
                    Solver::Ref(RefCall {
                        index,
                        argument_count,
                    }),
                    d.inputs,
                )
            }
            _ => d,
        };
        vec![Statement::Directive(res)]
    }
}
