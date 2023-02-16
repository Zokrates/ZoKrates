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

    fn fold_if_else_statement(
        &mut self,
        s: zokrates_ast::zir::IfElseStatement<'ast, T>,
    ) -> Vec<ZirStatement<'ast, T>> {
        let condition = self.fold_boolean_expression(s.condition);

        let mut consequence: Vec<_> = s
            .consequence
            .into_iter()
            .rev()
            .flat_map(|e| self.fold_statement(e))
            .collect();
        consequence.reverse();

        let mut alternative: Vec<_> = s
            .alternative
            .into_iter()
            .rev()
            .flat_map(|e| self.fold_statement(e))
            .collect();
        alternative.reverse();

        vec![ZirStatement::if_else(condition, consequence, alternative)]
    }

    fn fold_multiple_definition_statement(
        &mut self,
        s: zokrates_ast::zir::MultipleDefinitionStatement<'ast, T>,
    ) -> Vec<ZirStatement<'ast, T>> {
        // if the lhs is used later in the program
        if s.assignees.iter().any(|a| self.used.remove(&a.id)) {
            // include this statement
            fold_multiple_definition_statement(self, s)
        } else {
            // otherwise remove it
            vec![]
        }
    }

    fn fold_definition_statement(
        &mut self,
        s: zokrates_ast::zir::DefinitionStatement<'ast, T>,
    ) -> Vec<ZirStatement<'ast, T>> {
        // if the lhs is used later in the program
        if self.used.remove(&s.assignee.id) {
            // include this statement
            fold_definition_statement(self, s)
        } else {
            // otherwise remove it
            vec![]
        }
    }

    fn fold_name(&mut self, n: Identifier<'ast>) -> Identifier<'ast> {
        self.used.insert(n.clone());
        n
    }
}
