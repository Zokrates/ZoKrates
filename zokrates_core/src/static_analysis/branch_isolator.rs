// Isolate branches means making sure that any branch is enclosed in a block.
// This is important, because we want any statement resulting from inlining any branch to be isolated from the coller, so that its panics can be conditional to the branch being logically run

// `if c then a else b fi` becomes `if c then { a } else { b } fi`, and down the line any statements resulting from trating `a` and `b` can be safely kept inside the respective blocks.

use crate::typed_absy::folder::*;
use crate::typed_absy::*;
use zokrates_field::Field;

pub struct Isolator;

impl Isolator {
    pub fn isolate<T: Field>(p: TypedProgram<T>) -> TypedProgram<T> {
        let mut isolator = Isolator;
        isolator.fold_program(p)
    }
}

impl<'ast, T: Field> Folder<'ast, T> for Isolator {
    fn fold_conditional_expression<
        E: Expr<'ast, T> + Block<'ast, T> + Fold<'ast, T> + Conditional<'ast, T>,
    >(
        &mut self,
        _: &E::Ty,
        e: ConditionalExpression<'ast, T, E>,
    ) -> ConditionalOrExpression<'ast, T, E> {
        ConditionalOrExpression::Conditional(ConditionalExpression::new(
            self.fold_boolean_expression(*e.condition),
            E::block(vec![], e.consequence.fold(self)),
            E::block(vec![], e.alternative.fold(self)),
            e.kind,
        ))
    }

    fn fold_block_expression<E: Expr<'ast, T> + Fold<'ast, T>>(
        &mut self,
        _: &E::Ty,
        block: BlockExpression<'ast, T, E>,
    ) -> BlockOrExpression<'ast, T, E> {
        assert!(block.statements.is_empty());

        let expression = block.value.fold(self);

        BlockOrExpression::Expression(expression.into_inner())
    }
}
