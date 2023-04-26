use zokrates_ast::{
    common::{Fold, WithSpan},
    typed::{
        folder::*, BlockExpression, BooleanExpression, Conditional, ConditionalExpression,
        ConditionalOrExpression, CoreIdentifier, Expr, Id, Identifier, Type, TypedExpression,
        TypedProgram, TypedStatement, Variable,
    },
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
    fn fold_statement_cases(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        assert!(self.buffer.is_empty());
        let s = fold_statement_cases(self, s);
        let buffer = std::mem::take(&mut self.buffer);
        buffer.into_iter().chain(s).collect()
    }

    fn fold_block_expression<E: Fold<Self>>(
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

    fn fold_conditional_expression<E: Expr<'ast, T> + Conditional<'ast, T> + Fold<Self>>(
        &mut self,
        _: &E::Ty,
        e: ConditionalExpression<'ast, T, E>,
    ) -> ConditionalOrExpression<'ast, T, E> {
        let condition = self.fold_boolean_expression(*e.condition);
        let condition_span = condition.get_span();
        let condition = match condition {
            condition @ BooleanExpression::Value(_)
            | condition @ BooleanExpression::Identifier(_) => condition,
            condition => {
                let condition_id = Identifier::from(CoreIdentifier::Condition(self.index));
                self.buffer.push(
                    TypedStatement::definition(
                        Variable::new(condition_id.clone(), Type::Boolean)
                            .span(condition_span)
                            .into(),
                        TypedExpression::from(condition).span(condition_span),
                    )
                    .span(condition_span),
                );
                self.index += 1;
                BooleanExpression::identifier(condition_id).span(condition_span)
            }
        }
        .span(condition_span);

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

#[cfg(test)]
mod tests {
    use super::*;
    use std::ops::*;
    use zokrates_ast::typed::{
        Block, BooleanExpression, Conditional, ConditionalKind, FieldElementExpression, Type,
    };
    use zokrates_field::Bn128Field;

    #[test]
    fn no_redefine_if_constant() {
        // field foo = if true { 1 } else { 2 };
        // should be left unchanged

        let s = TypedStatement::definition(
            Variable::field_element("foo").into(),
            FieldElementExpression::conditional(
                BooleanExpression::value(true),
                FieldElementExpression::value(Bn128Field::from(1)),
                FieldElementExpression::value(Bn128Field::from(2)),
                ConditionalKind::IfElse,
            )
            .into(),
        );

        let mut r = ConditionRedefiner::default();

        assert_eq!(r.fold_statement(s.clone()), vec![s]);
    }

    #[test]
    fn no_redefine_if_identifier() {
        // field foo = if c { 1 } else { 2 };
        // should be left unchanged

        let s = TypedStatement::definition(
            Variable::field_element("foo").into(),
            FieldElementExpression::conditional(
                BooleanExpression::identifier("c".into()),
                FieldElementExpression::value(Bn128Field::from(1)),
                FieldElementExpression::value(Bn128Field::from(2)),
                ConditionalKind::IfElse,
            )
            .into(),
        );

        let mut r = ConditionRedefiner::default();

        assert_eq!(r.fold_statement(s.clone()), vec![s]);
    }

    #[test]
    fn redefine_if_expression() {
        // field foo = if c && d { 1 } else { 2 };
        // should become
        // bool #CONDITION_0 = c && d;
        // field foo = if #CONDITION_0 { 1 } else { 2 };

        let condition = BooleanExpression::bitand(
            BooleanExpression::identifier("c".into()),
            BooleanExpression::identifier("d".into()),
        );

        let s = TypedStatement::definition(
            Variable::field_element("foo").into(),
            FieldElementExpression::conditional(
                condition.clone(),
                FieldElementExpression::value(Bn128Field::from(1)),
                FieldElementExpression::value(Bn128Field::from(2)),
                ConditionalKind::IfElse,
            )
            .into(),
        );

        let mut r = ConditionRedefiner::default();

        let expected = vec![
            // define condition
            TypedStatement::definition(
                Variable::new(CoreIdentifier::Condition(0), Type::Boolean).into(),
                condition.into(),
            ),
            // rewrite statement
            TypedStatement::definition(
                Variable::field_element("foo").into(),
                FieldElementExpression::conditional(
                    BooleanExpression::identifier(CoreIdentifier::Condition(0).into()),
                    FieldElementExpression::value(Bn128Field::from(1)),
                    FieldElementExpression::value(Bn128Field::from(2)),
                    ConditionalKind::IfElse,
                )
                .into(),
            ),
        ];

        assert_eq!(r.fold_statement(s), expected);
    }

    #[test]
    fn redefine_rec() {
        // field foo = if c && d {
        //     if e && f { 1 } else { 2 }
        // } else {
        //     3
        // };
        //
        //
        // should become
        //
        // bool #CONDITION_0 = c && d;
        // bool #CONDITION_1 = e && f;
        // field foo = if #CONDITION_0 {
        //     if #CONDITION_1 { 1 } else { 2 }
        // } else {
        //     3
        // };

        let condition_0 = BooleanExpression::bitand(
            BooleanExpression::identifier("c".into()),
            BooleanExpression::identifier("d".into()),
        );

        let condition_1 = BooleanExpression::bitand(
            BooleanExpression::identifier("e".into()),
            BooleanExpression::identifier("f".into()),
        );

        let s = TypedStatement::definition(
            Variable::field_element("foo").into(),
            FieldElementExpression::conditional(
                condition_0.clone(),
                FieldElementExpression::conditional(
                    condition_1.clone(),
                    FieldElementExpression::value(Bn128Field::from(1)),
                    FieldElementExpression::value(Bn128Field::from(2)),
                    ConditionalKind::IfElse,
                ),
                FieldElementExpression::value(Bn128Field::from(3)),
                ConditionalKind::IfElse,
            )
            .into(),
        );

        let mut r = ConditionRedefiner::default();

        let expected = vec![
            // define conditions
            TypedStatement::definition(
                Variable::new(CoreIdentifier::Condition(0), Type::Boolean).into(),
                condition_0.into(),
            ),
            TypedStatement::definition(
                Variable::new(CoreIdentifier::Condition(1), Type::Boolean).into(),
                condition_1.into(),
            ),
            // rewrite statement
            TypedStatement::definition(
                Variable::field_element("foo").into(),
                FieldElementExpression::conditional(
                    BooleanExpression::identifier(CoreIdentifier::Condition(0).into()),
                    FieldElementExpression::conditional(
                        BooleanExpression::identifier(CoreIdentifier::Condition(1).into()),
                        FieldElementExpression::value(Bn128Field::from(1)),
                        FieldElementExpression::value(Bn128Field::from(2)),
                        ConditionalKind::IfElse,
                    ),
                    FieldElementExpression::value(Bn128Field::from(3)),
                    ConditionalKind::IfElse,
                )
                .into(),
            ),
        ];

        assert_eq!(r.fold_statement(s), expected);
    }

    #[test]
    fn redefine_block() {
        // field foo = if c && d {
        //     field a = 1;
        //     if e && f { 2 } else { 3 }
        // } else {
        //     field b = 2;
        //     if e && f { 2 } else { 3 }
        // };
        //
        // should become
        //
        // bool #CONDITION_0 = c && d;
        // field foo = if #CONDITION_0 ? {
        //     field a = 1;
        //     bool #CONDITION_1 = e && f;
        //     if #CONDITION_1 { 2 } : { 3 }
        // } else {
        //     field b = 2;
        //     bool #CONDITION_2 = e && f;
        //     if #CONDITION_2 { 2 } : { 3 }
        // };

        let condition_0 = BooleanExpression::bitand(
            BooleanExpression::identifier("c".into()),
            BooleanExpression::identifier("d".into()),
        );

        let condition_1 = BooleanExpression::bitand(
            BooleanExpression::identifier("e".into()),
            BooleanExpression::identifier("f".into()),
        );

        let condition_2 = BooleanExpression::bitand(
            BooleanExpression::identifier("e".into()),
            BooleanExpression::identifier("f".into()),
        );

        let condition_id_0 = BooleanExpression::identifier(CoreIdentifier::Condition(0).into());
        let condition_id_1 = BooleanExpression::identifier(CoreIdentifier::Condition(1).into());
        let condition_id_2 = BooleanExpression::identifier(CoreIdentifier::Condition(2).into());

        let s = TypedStatement::definition(
            Variable::field_element("foo").into(),
            FieldElementExpression::conditional(
                condition_0.clone(),
                FieldElementExpression::block(
                    vec![TypedStatement::definition(
                        Variable::field_element("a").into(),
                        FieldElementExpression::value(Bn128Field::from(1)).into(),
                    )],
                    FieldElementExpression::conditional(
                        condition_1.clone(),
                        FieldElementExpression::value(Bn128Field::from(2)),
                        FieldElementExpression::value(Bn128Field::from(3)),
                        ConditionalKind::IfElse,
                    ),
                ),
                FieldElementExpression::block(
                    vec![TypedStatement::definition(
                        Variable::field_element("b").into(),
                        FieldElementExpression::value(Bn128Field::from(2)).into(),
                    )],
                    FieldElementExpression::conditional(
                        condition_2.clone(),
                        FieldElementExpression::value(Bn128Field::from(2)),
                        FieldElementExpression::value(Bn128Field::from(3)),
                        ConditionalKind::IfElse,
                    ),
                ),
                ConditionalKind::IfElse,
            )
            .into(),
        );

        let mut r = ConditionRedefiner::default();

        let expected = vec![
            // define conditions
            TypedStatement::definition(
                Variable::new(CoreIdentifier::Condition(0), Type::Boolean).into(),
                condition_0.into(),
            ),
            // rewrite statement
            TypedStatement::definition(
                Variable::field_element("foo").into(),
                FieldElementExpression::conditional(
                    condition_id_0.clone(),
                    FieldElementExpression::block(
                        vec![
                            TypedStatement::definition(
                                Variable::field_element("a").into(),
                                FieldElementExpression::value(Bn128Field::from(1)).into(),
                            ),
                            TypedStatement::definition(
                                Variable::new(CoreIdentifier::Condition(1), Type::Boolean).into(),
                                condition_1.into(),
                            ),
                        ],
                        FieldElementExpression::conditional(
                            condition_id_1,
                            FieldElementExpression::value(Bn128Field::from(2)),
                            FieldElementExpression::value(Bn128Field::from(3)),
                            ConditionalKind::IfElse,
                        ),
                    ),
                    FieldElementExpression::block(
                        vec![
                            TypedStatement::definition(
                                Variable::field_element("b").into(),
                                FieldElementExpression::value(Bn128Field::from(2)).into(),
                            ),
                            TypedStatement::definition(
                                Variable::new(CoreIdentifier::Condition(2), Type::Boolean).into(),
                                condition_2.into(),
                            ),
                        ],
                        FieldElementExpression::conditional(
                            condition_id_2,
                            FieldElementExpression::value(Bn128Field::from(2)),
                            FieldElementExpression::value(Bn128Field::from(3)),
                            ConditionalKind::IfElse,
                        ),
                    ),
                    ConditionalKind::IfElse,
                )
                .into(),
            ),
        ];

        assert_eq!(r.fold_statement(s), expected);
    }
}
