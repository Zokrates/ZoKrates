use std::collections::HashSet;
use zokrates_ast::typed::{
    folder::*, BlockExpression, Identifier, TypedAssignee, TypedFunction, TypedProgram,
    TypedStatement,
};
use zokrates_field::Field;

#[derive(Default)]
pub struct DeadCodeEliminator<'ast> {
    used: HashSet<Identifier<'ast>>,
    in_block: usize,
}

impl<'ast> DeadCodeEliminator<'ast> {
    pub fn eliminate<T: Field>(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        Self::default().fold_program(p)
    }
}

impl<'ast, T: Field> Folder<'ast, T> for DeadCodeEliminator<'ast> {
    fn fold_function(&mut self, f: TypedFunction<'ast, T>) -> TypedFunction<'ast, T> {
        // iterate on the statements starting from the end, as we want to see usage before definition
        let mut statements: Vec<_> = f
            .statements
            .into_iter()
            .rev()
            .flat_map(|s| self.fold_statement(s))
            .collect();
        statements.reverse();
        TypedFunction { statements, ..f }
    }

    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        match s {
            TypedStatement::Definition(a, e) => match a {
                TypedAssignee::Identifier(ref id) => {
                    // if the lhs is used later in the program and we're in a block
                    if self.used.remove(&id.id) {
                        // include this statement
                        fold_statement(self, TypedStatement::Definition(a, e))
                    } else {
                        // otherwise remove it
                        vec![]
                    }
                }
                _ => fold_statement(self, TypedStatement::Definition(a, e)),
            },
            TypedStatement::For(..) => {
                unreachable!("for loops should be removed before dead code elimination is run")
            }
            s => fold_statement(self, s),
        }
    }

    fn fold_block_expression<E: Fold<'ast, T>>(
        &mut self,
        block: BlockExpression<'ast, T, E>,
    ) -> BlockExpression<'ast, T, E> {
        self.in_block += 1;

        let value = box block.value.fold(self);
        let mut statements: Vec<_> = block
            .statements
            .into_iter()
            .rev()
            .flat_map(|s| self.fold_statement(s))
            .collect();
        statements.reverse();

        let block = BlockExpression { value, statements };
        self.in_block -= 1;
        block
    }

    fn fold_name(&mut self, n: Identifier<'ast>) -> Identifier<'ast> {
        self.used.insert(n.clone());
        n
    }
}
