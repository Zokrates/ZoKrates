use crate::typed_absy::{
    folder::*, BlockExpression, BooleanExpression, Conditional, ConditionalExpression,
    ConditionalOrExpression, CoreIdentifier, Expr, Identifier, TypedProgram, TypedStatement,
    Variable,
};
use zokrates_field::Field;

#[derive(Default)]
pub struct ConditionRedefiner<'ast, T> {
    index: usize,
    buffer: Vec<TypedStatement<'ast, T>>,
}

impl<'ast, T: Field> ConditionRedefiner<'ast, T> {
    pub fn redefine(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        Self::default().fold_program(p)
    }
}

impl<'ast, T: Field> Folder<'ast, T> for ConditionRedefiner<'ast, T> {
    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        assert!(self.buffer.is_empty());
        let s = fold_statement(self, s);
        let buffer = std::mem::take(&mut self.buffer);
        buffer.into_iter().chain(s).collect()
    }

    fn fold_block_expression<E: Fold<'ast, T>>(
        &mut self,
        b: BlockExpression<'ast, T, E>,
    ) -> BlockExpression<'ast, T, E> {
        // start with a fresh state, but keep the global counter
        let mut redefiner = ConditionRedefiner {
            index: self.index,
            buffer: vec![],
        };

        let b = fold_block_expression(&mut redefiner, b);

        // we add the buffer statements *after* the block statements because they refer to the return value,
        // the buffered statements for the block statements are already included in the result
        let b = BlockExpression {
            statements: b
                .statements
                .into_iter()
                .chain(std::mem::take(&mut redefiner.buffer))
                .collect(),
            ..b
        };

        // continue from the latest index
        self.index = redefiner.index;

        b
    }

    fn fold_conditional_expression<E: Expr<'ast, T> + Conditional<'ast, T> + Fold<'ast, T>>(
        &mut self,
        _: &E::Ty,
        e: ConditionalExpression<'ast, T, E>,
    ) -> ConditionalOrExpression<'ast, T, E> {
        let condition = self.fold_boolean_expression(*e.condition);
        let condition = match condition {
            condition @ BooleanExpression::Value(_)
            | condition @ BooleanExpression::Identifier(_) => condition,
            condition => {
                let condition_id = Identifier::from(CoreIdentifier::Condition(self.index));
                self.buffer.push(TypedStatement::Definition(
                    Variable::boolean(condition_id.clone()).into(),
                    condition.into(),
                ));
                self.index += 1;
                BooleanExpression::Identifier(condition_id)
            }
        };

        let consequence = e.consequence.fold(self);
        let alternative = e.alternative.fold(self);

        ConditionalOrExpression::Conditional(ConditionalExpression::new(
            condition,
            consequence,
            alternative,
            e.kind,
        ))
    }
}
