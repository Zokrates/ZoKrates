use zokrates_ast::typed::{
    folder::*, BlockExpression, BooleanExpression, Conditional, ConditionalExpression,
    ConditionalOrExpression, CoreIdentifier, Expr, Identifier, Type, TypedExpression, TypedProgram,
    TypedStatement, Variable,
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
                self.buffer.push(TypedStatement::definition(
                    Variable::immutable(condition_id.clone(), Type::Boolean).into(),
                    TypedExpression::from(condition),
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

#[cfg(test)]
mod tests {
    use super::*;
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
                BooleanExpression::Value(true),
                FieldElementExpression::Number(Bn128Field::from(1)),
                FieldElementExpression::Number(Bn128Field::from(2)),
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
                BooleanExpression::Identifier("c".into()),
                FieldElementExpression::Number(Bn128Field::from(1)),
                FieldElementExpression::Number(Bn128Field::from(2)),
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

        let condition = BooleanExpression::And(
            box BooleanExpression::Identifier("c".into()),
            box BooleanExpression::Identifier("d".into()),
        );

        let s = TypedStatement::definition(
            Variable::field_element("foo").into(),
            FieldElementExpression::conditional(
                condition.clone(),
                FieldElementExpression::Number(Bn128Field::from(1)),
                FieldElementExpression::Number(Bn128Field::from(2)),
                ConditionalKind::IfElse,
            )
            .into(),
        );

        let mut r = ConditionRedefiner::default();

        let expected = vec![
            // define condition
            TypedStatement::definition(
                Variable::immutable(CoreIdentifier::Condition(0), Type::Boolean).into(),
                condition.into(),
            ),
            // rewrite statement
            TypedStatement::definition(
                Variable::field_element("foo").into(),
                FieldElementExpression::conditional(
                    BooleanExpression::Identifier(CoreIdentifier::Condition(0).into()),
                    FieldElementExpression::Number(Bn128Field::from(1)),
                    FieldElementExpression::Number(Bn128Field::from(2)),
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

        let condition_0 = BooleanExpression::And(
            box BooleanExpression::Identifier("c".into()),
            box BooleanExpression::Identifier("d".into()),
        );

        let condition_1 = BooleanExpression::And(
            box BooleanExpression::Identifier("e".into()),
            box BooleanExpression::Identifier("f".into()),
        );

        let s = TypedStatement::definition(
            Variable::field_element("foo").into(),
            FieldElementExpression::conditional(
                condition_0.clone(),
                FieldElementExpression::conditional(
                    condition_1.clone(),
                    FieldElementExpression::Number(Bn128Field::from(1)),
                    FieldElementExpression::Number(Bn128Field::from(2)),
                    ConditionalKind::IfElse,
                ),
                FieldElementExpression::Number(Bn128Field::from(3)),
                ConditionalKind::IfElse,
            )
            .into(),
        );

        let mut r = ConditionRedefiner::default();

        let expected = vec![
            // define conditions
            TypedStatement::definition(
                Variable::immutable(CoreIdentifier::Condition(0), Type::Boolean).into(),
                condition_0.into(),
            ),
            TypedStatement::definition(
                Variable::immutable(CoreIdentifier::Condition(1), Type::Boolean).into(),
                condition_1.into(),
            ),
            // rewrite statement
            TypedStatement::definition(
                Variable::field_element("foo").into(),
                FieldElementExpression::conditional(
                    BooleanExpression::Identifier(CoreIdentifier::Condition(0).into()),
                    FieldElementExpression::conditional(
                        BooleanExpression::Identifier(CoreIdentifier::Condition(1).into()),
                        FieldElementExpression::Number(Bn128Field::from(1)),
                        FieldElementExpression::Number(Bn128Field::from(2)),
                        ConditionalKind::IfElse,
                    ),
                    FieldElementExpression::Number(Bn128Field::from(3)),
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

        let condition_0 = BooleanExpression::And(
            box BooleanExpression::Identifier("c".into()),
            box BooleanExpression::Identifier("d".into()),
        );

        let condition_1 = BooleanExpression::And(
            box BooleanExpression::Identifier("e".into()),
            box BooleanExpression::Identifier("f".into()),
        );

        let condition_2 = BooleanExpression::And(
            box BooleanExpression::Identifier("e".into()),
            box BooleanExpression::Identifier("f".into()),
        );

        let condition_id_0 = BooleanExpression::Identifier(CoreIdentifier::Condition(0).into());
        let condition_id_1 = BooleanExpression::Identifier(CoreIdentifier::Condition(1).into());
        let condition_id_2 = BooleanExpression::Identifier(CoreIdentifier::Condition(2).into());

        let s = TypedStatement::definition(
            Variable::field_element("foo").into(),
            FieldElementExpression::conditional(
                condition_0.clone(),
                FieldElementExpression::block(
                    vec![TypedStatement::definition(
                        Variable::field_element("a").into(),
                        FieldElementExpression::Number(Bn128Field::from(1)).into(),
                    )],
                    FieldElementExpression::conditional(
                        condition_1.clone(),
                        FieldElementExpression::Number(Bn128Field::from(2)),
                        FieldElementExpression::Number(Bn128Field::from(3)),
                        ConditionalKind::IfElse,
                    ),
                ),
                FieldElementExpression::block(
                    vec![TypedStatement::definition(
                        Variable::field_element("b").into(),
                        FieldElementExpression::Number(Bn128Field::from(2)).into(),
                    )],
                    FieldElementExpression::conditional(
                        condition_2.clone(),
                        FieldElementExpression::Number(Bn128Field::from(2)),
                        FieldElementExpression::Number(Bn128Field::from(3)),
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
                Variable::immutable(CoreIdentifier::Condition(0), Type::Boolean).into(),
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
                                FieldElementExpression::Number(Bn128Field::from(1)).into(),
                            ),
                            TypedStatement::definition(
                                Variable::immutable(CoreIdentifier::Condition(1), Type::Boolean)
                                    .into(),
                                condition_1.into(),
                            ),
                        ],
                        FieldElementExpression::conditional(
                            condition_id_1,
                            FieldElementExpression::Number(Bn128Field::from(2)),
                            FieldElementExpression::Number(Bn128Field::from(3)),
                            ConditionalKind::IfElse,
                        ),
                    ),
                    FieldElementExpression::block(
                        vec![
                            TypedStatement::definition(
                                Variable::field_element("b").into(),
                                FieldElementExpression::Number(Bn128Field::from(2)).into(),
                            ),
                            TypedStatement::definition(
                                Variable::immutable(CoreIdentifier::Condition(2), Type::Boolean)
                                    .into(),
                                condition_2.into(),
                            ),
                        ],
                        FieldElementExpression::conditional(
                            condition_id_2,
                            FieldElementExpression::Number(Bn128Field::from(2)),
                            FieldElementExpression::Number(Bn128Field::from(3)),
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
