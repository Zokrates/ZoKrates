// Isolate branches means making sure that any branch is enclosed in a block.
// This is important, because we want any statement resulting from inlining any branch to be isolated from the coller, so that its panics can be conditional to the branch being logically run

// `if c then a else b fi` becomes `if c then { a } else { b } fi`, and down the line any statements resulting from trating `a` and `b` can be safely kept inside the respective blocks.

use zokrates_ast::common::{Fold, WithSpan};
use zokrates_ast::typed::folder::*;
use zokrates_ast::typed::*;
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
        E: Expr<'ast, T> + Block<'ast, T> + Fold<Self> + Conditional<'ast, T>,
    >(
        &mut self,
        _: &E::Ty,
        e: ConditionalExpression<'ast, T, E>,
    ) -> ConditionalOrExpression<'ast, T, E> {
        let span = e.get_span();

        let consequence_span = e.consequence.get_span();
        let alternative_span = e.alternative.get_span();

        ConditionalOrExpression::Conditional(
            ConditionalExpression::new(
                self.fold_boolean_expression(*e.condition),
                E::block(vec![], e.consequence.fold(self)).span(consequence_span),
                E::block(vec![], e.alternative.fold(self)).span(alternative_span),
                e.kind,
            )
            .span(span),
        )
    }
}
