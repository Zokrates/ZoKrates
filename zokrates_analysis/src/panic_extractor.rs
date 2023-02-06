use zokrates_ast::zir::{
    folder::*, BooleanExpression, Conditional, ConditionalExpression, ConditionalOrExpression,
    FieldElementExpression, RuntimeError, UBitwidth, UExpressionInner, ZirProgram, ZirStatement,
};
use zokrates_field::Field;

// a static analyser pass to extract the failure modes into separate assert statements, so that a statement can panic iff it's an assertion

#[derive(Default)]
pub struct PanicExtractor<'ast, T> {
    panic_buffer: Vec<ZirStatement<'ast, T>>,
}

impl<'ast, T: Field> PanicExtractor<'ast, T> {
    pub fn extract(p: ZirProgram<'ast, T>) -> ZirProgram<'ast, T> {
        Self::default().fold_program(p)
    }
}

impl<'ast, T: Field> Folder<'ast, T> for PanicExtractor<'ast, T> {
    fn fold_statement(&mut self, s: ZirStatement<'ast, T>) -> Vec<ZirStatement<'ast, T>> {
        match s {
            ZirStatement::IfElse(condition, consequence, alternative) => {
                let condition = self.fold_boolean_expression(condition);
                let mut consequence_extractor = Self::default();
                let consequence = consequence
                    .into_iter()
                    .flat_map(|s| consequence_extractor.fold_statement(s))
                    .collect();
                assert!(consequence_extractor.panic_buffer.is_empty());
                let mut alternative_extractor = Self::default();
                let alternative = alternative
                    .into_iter()
                    .flat_map(|s| alternative_extractor.fold_statement(s))
                    .collect();
                assert!(alternative_extractor.panic_buffer.is_empty());

                self.panic_buffer
                    .drain(..)
                    .chain(std::iter::once(ZirStatement::IfElse(
                        condition,
                        consequence,
                        alternative,
                    )))
                    .collect()
            }
            s => {
                let s = fold_statement(self, s);
                self.panic_buffer.drain(..).chain(s).collect()
            }
        }
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        match e {
            FieldElementExpression::Div(box n, box d) => {
                let n = self.fold_field_expression(n);
                let d = self.fold_field_expression(d);
                self.panic_buffer.push(ZirStatement::Assertion(
                    BooleanExpression::Not(box BooleanExpression::FieldEq(
                        box d.clone(),
                        box FieldElementExpression::Number(T::zero()),
                    )),
                    RuntimeError::DivisionByZero,
                ));
                FieldElementExpression::Div(box n, box d)
            }
            e => fold_field_expression(self, e),
        }
    }

    fn fold_conditional_expression<
        E: zokrates_ast::zir::Expr<'ast, T> + Fold<'ast, T> + Conditional<'ast, T>,
    >(
        &mut self,
        _: &E::Ty,
        e: ConditionalExpression<'ast, T, E>,
    ) -> ConditionalOrExpression<'ast, T, E> {
        let condition = self.fold_boolean_expression(*e.condition);
        let mut consequence_extractor = Self::default();
        let consequence = e.consequence.fold(&mut consequence_extractor);
        let mut alternative_extractor = Self::default();
        let alternative = e.alternative.fold(&mut alternative_extractor);

        let consequence_panics: Vec<_> = consequence_extractor.panic_buffer.drain(..).collect();
        let alternative_panics: Vec<_> = alternative_extractor.panic_buffer.drain(..).collect();

        if !(consequence_panics.is_empty() && alternative_panics.is_empty()) {
            self.panic_buffer.push(ZirStatement::IfElse(
                condition.clone(),
                consequence_panics,
                alternative_panics,
            ));
        }

        ConditionalOrExpression::Conditional(ConditionalExpression::new(
            condition,
            consequence,
            alternative,
        ))
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
                self.panic_buffer.push(ZirStatement::Assertion(
                    BooleanExpression::Not(box BooleanExpression::UintEq(
                        box d.clone(),
                        box UExpressionInner::Value(0).annotate(b),
                    )),
                    RuntimeError::DivisionByZero,
                ));
                UExpressionInner::Div(box n, box d)
            }
            e => fold_uint_expression_inner(self, b, e),
        }
    }

    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> BooleanExpression<'ast, T> {
        match e {
            // constant range checks are complete, so no panic needs to be extracted
            e @ BooleanExpression::FieldLt(box FieldElementExpression::Number(_), _)
            | e @ BooleanExpression::FieldLt(_, box FieldElementExpression::Number(_)) => {
                fold_boolean_expression(self, e)
            }
            BooleanExpression::FieldLt(box left, box right) => {
                let left = self.fold_field_expression(left);
                let right = self.fold_field_expression(right);

                let bit_width = T::get_required_bits();

                let safe_width = bit_width - 2; // dynamic comparison is not complete, it only applies to field elements whose difference is strictly smaller than 2**(bitwidth - 2)

                let offset = FieldElementExpression::Number(T::from(2).pow(safe_width));
                let max = FieldElementExpression::Number(T::from(2).pow(safe_width + 1));

                // `|left - right|` must be of bitwidth at most `safe_bitwidth`
                // this means we need to guarantee the following: `-2**(safe_width) < left - right < 2**(safe_width)`
                // adding an offset of `2**(safe_width)` we turn this into:
                // require `0 < 2**(safe_width) + left - right < 2**(safe_width + 1)`

                // we split this check in two:
                // `2**(safe_width) + left - right < 2**(safe_width + 1)`
                self.panic_buffer.push(ZirStatement::Assertion(
                    BooleanExpression::FieldLt(
                        box FieldElementExpression::Add(
                            box offset.clone(),
                            box FieldElementExpression::Sub(box left.clone(), box right.clone()),
                        ),
                        box max,
                    ),
                    RuntimeError::IncompleteDynamicRange,
                ));

                // and
                // `2**(safe_width) + left - right != 0`
                self.panic_buffer.push(ZirStatement::Assertion(
                    BooleanExpression::Not(box BooleanExpression::FieldEq(
                        box FieldElementExpression::Sub(box right.clone(), box left.clone()),
                        box offset,
                    )),
                    RuntimeError::IncompleteDynamicRange,
                ));

                // NOTE:
                // instead of splitting the check in two, we could have used a single `Lt` here, by simply subtracting 1 from all sides:
                // `let x = 2**(safe_width) + left - right`
                // `0 <= x - 1 < 2**(safe_width + 1) - 1` which is a single constant `Lt`
                // however, the *result* of `left < right` requires knowing the bits of `x`
                // if we use `x - 1` here, we end up having to calculate the bits of both `x` and `x - 1`, which is expensive
                // by splitting, we can reuse the bits of `x` needed for this completeness check when computing the result

                BooleanExpression::FieldLt(box left, box right)
            }
            e => fold_boolean_expression(self, e),
        }
    }
}
