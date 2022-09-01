use std::collections::HashSet;
use zokrates_ast::zir::{folder::*, Identifier, ZirFunction, ZirProgram, ZirStatement};
use zokrates_field::Field;

#[derive(Default)]
pub struct DeadCodeEliminator<'ast> {
    used: HashSet<Identifier<'ast>>,
}

impl<'ast> DeadCodeEliminator<'ast> {
    pub fn eliminate<T: Field>(p: ZirProgram<'ast, T>) -> ZirProgram<'ast, T> {
        Self::default().fold_program(p)
    }
}

impl<'ast, T: Field> Folder<'ast, T> for DeadCodeEliminator<'ast> {
    fn fold_function(&mut self, f: ZirFunction<'ast, T>) -> ZirFunction<'ast, T> {
        // iterate on the statements starting from the end, as we want to see usage before definition
        let mut statements: Vec<_> = f
            .statements
            .into_iter()
            .rev()
            .flat_map(|s| self.fold_statement(s))
            .collect();
        statements.reverse();
        ZirFunction { statements, ..f }
    }

    fn fold_statement(&mut self, s: ZirStatement<'ast, T>) -> Vec<ZirStatement<'ast, T>> {
        match s {
            ZirStatement::Definition(v, e) => {
                // if the lhs is used later in the program
                if self.used.remove(&v.id) {
                    // include this statement
                    fold_statement(self, ZirStatement::Definition(v, e))
                } else {
                    // otherwise remove it
                    vec![]
                }
            }
            ZirStatement::IfElse(condition, consequence, alternative) => {
                let condition = self.fold_boolean_expression(condition);

                let mut consequence: Vec<_> = consequence
                    .into_iter()
                    .rev()
                    .flat_map(|e| self.fold_statement(e))
                    .collect();
                consequence.reverse();

                let mut alternative: Vec<_> = alternative
                    .into_iter()
                    .rev()
                    .flat_map(|e| self.fold_statement(e))
                    .collect();
                alternative.reverse();

                vec![ZirStatement::IfElse(condition, consequence, alternative)]
            }
            s => fold_statement(self, s),
        }
    }

    fn fold_name(&mut self, n: Identifier<'ast>) -> Identifier<'ast> {
        self.used.insert(n.clone());
        n
    }
}
