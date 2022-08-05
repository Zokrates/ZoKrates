use zokrates_ast::typed::{
    folder::*, BooleanExpression, EqExpression, FieldElementExpression, RuntimeError, TypedProgram,
    TypedStatement, UBitwidth, UExpressionInner,
};
use zokrates_field::Field;

// a static analyser pass to extract the failure modes into separate assert statements, so that a statement can panic iff it's an assertion

#[derive(Default)]
pub struct PanicExtractor<'ast, T> {
    panic_buffer: Vec<(BooleanExpression<'ast, T>, RuntimeError)>,
}

impl<'ast, T: Field> PanicExtractor<'ast, T> {
    pub fn extract(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        Self::default().fold_program(p)
    }
}

impl<'ast, T: Field> Folder<'ast, T> for PanicExtractor<'ast, T> {
    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        let s = fold_statement(self, s);
        self.panic_buffer
            .drain(..)
            .map(|(b, e)| TypedStatement::Assertion(b, e))
            .chain(s)
            .collect()
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        match e {
            FieldElementExpression::Div(box n, box d) => {
                let n = self.fold_field_expression(n);
                let d = self.fold_field_expression(d);
                self.panic_buffer.push((
                    BooleanExpression::Not(box BooleanExpression::FieldEq(EqExpression::new(
                        d.clone(),
                        T::zero().into(),
                    ))),
                    RuntimeError::DivisionByZero,
                ));
                FieldElementExpression::Div(box n, box d)
            }
            e => fold_field_expression(self, e),
        }
    }

    fn fold_uint_expression_inner(
        &mut self,
        b: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> UExpressionInner<'ast, T> {
        match e {
            UExpressionInner::Div(box n, box d) => {
                let n = self.fold_uint_expression(n);
                let d = self.fold_uint_expression(d);
                self.panic_buffer.push((
                    BooleanExpression::Not(box BooleanExpression::UintEq(EqExpression::new(
                        d.clone(),
                        UExpressionInner::Value(0).annotate(b),
                    ))),
                    RuntimeError::DivisionByZero,
                ));
                UExpressionInner::Div(box n, box d)
            }
            e => fold_uint_expression_inner(self, b, e),
        }
    }
}
