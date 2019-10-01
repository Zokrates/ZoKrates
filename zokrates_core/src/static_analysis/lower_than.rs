//! Module containing constant propagation for the typed AST
//!
//! @file propagation.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use crate::typed_absy::folder::*;
use crate::typed_absy::*;
use std::collections::HashMap;
use std::convert::TryFrom;
use types::{FunctionKey, Signature, Type};
use zokrates_field::field::Field;

pub struct LowerThan<'ast, T: Field> {
    statements: Vec<TypedStatement<'ast, T>>,
    counter: usize,
}

impl<'ast, T: Field> LowerThan<'ast, T> {
    fn new() -> Self {
        LowerThan {
            statements: vec![],
            counter: 0,
        }
    }

    pub fn reduce(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        LowerThan::new().fold_program(p)
    }
}

impl<'ast, T: Field> Folder<'ast, T> for LowerThan<'ast, T> {
    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> BooleanExpression<'ast, T> {
        match e {
            // swap
            BooleanExpression::Gt(box left, box right) => {
                self.fold_boolean_expression(BooleanExpression::Lt(box right, box left))
            }
            BooleanExpression::Ge(box left, box right) => {
                self.fold_boolean_expression(BooleanExpression::Le(box right, box left))
            }
            // reduce ´<=´ to ´< || ==´
            BooleanExpression::Le(box left, box right) => {
                self.fold_boolean_expression(BooleanExpression::Or(
                    box BooleanExpression::Lt(box left.clone(), box right.clone()),
                    box BooleanExpression::Eq(box left, box right),
                ))
            }
            BooleanExpression::Lt(box left, box right) => {
                let left_bits = Identifier::internal("left_bits", self.counter);
                let right_bits = Identifier::internal("right_bits", self.counter);
                let diff_bits = Identifier::internal("diff_bits", self.counter);

                self.statements.extend(vec![
                    TypedStatement::MultipleDefinition(
                        vec![Variable::array(
                            left_bits.clone(),
                            Type::Boolean,
                            T::get_required_bits(),
                        )],
                        TypedExpressionList::FunctionCall(
                            FunctionKey::with_id("_UNPACK").signature(
                                Signature::new()
                                    .inputs(vec![Type::FieldElement])
                                    .outputs(vec![Type::array(
                                        Type::Boolean,
                                        T::get_required_bits(),
                                    )]),
                            ),
                            vec![left.clone().into()],
                            vec![Type::array(Type::Boolean, T::get_required_bits())],
                        ),
                    ),
                    TypedStatement::Condition(
                        BooleanExpression::Select(
                            box ArrayExpressionInner::Identifier(left_bits.clone())
                                .annotate(Type::Boolean, T::get_required_bits()),
                            box FieldElementExpression::Number(T::from(0)),
                        )
                        .into(),
                        BooleanExpression::Value(false).into(),
                    ),
                    TypedStatement::Condition(
                        BooleanExpression::Select(
                            box ArrayExpressionInner::Identifier(left_bits.clone())
                                .annotate(Type::Boolean, T::get_required_bits()),
                            box FieldElementExpression::Number(T::from(1)),
                        )
                        .into(),
                        BooleanExpression::Value(false).into(),
                    ),
                    TypedStatement::MultipleDefinition(
                        vec![Variable::array(
                            right_bits.clone(),
                            Type::Boolean,
                            T::get_required_bits(),
                        )],
                        TypedExpressionList::FunctionCall(
                            FunctionKey::with_id("_UNPACK").signature(
                                Signature::new()
                                    .inputs(vec![Type::FieldElement])
                                    .outputs(vec![Type::array(
                                        Type::Boolean,
                                        T::get_required_bits(),
                                    )]),
                            ),
                            vec![right.clone().into()],
                            vec![Type::array(Type::Boolean, T::get_required_bits())],
                        ),
                    ),
                    TypedStatement::Condition(
                        BooleanExpression::Select(
                            box ArrayExpressionInner::Identifier(right_bits.clone())
                                .annotate(Type::Boolean, T::get_required_bits()),
                            box FieldElementExpression::Number(T::from(0)),
                        )
                        .into(),
                        BooleanExpression::Value(false).into(),
                    ),
                    TypedStatement::Condition(
                        BooleanExpression::Select(
                            box ArrayExpressionInner::Identifier(right_bits.clone())
                                .annotate(Type::Boolean, T::get_required_bits()),
                            box FieldElementExpression::Number(T::from(1)),
                        )
                        .into(),
                        BooleanExpression::Value(false).into(),
                    ),
                    TypedStatement::MultipleDefinition(
                        vec![Variable::array(
                            diff_bits.clone(),
                            Type::Boolean,
                            T::get_required_bits(),
                        )],
                        TypedExpressionList::FunctionCall(
                            FunctionKey::with_id("_UNPACK").signature(
                                Signature::new()
                                    .inputs(vec![Type::FieldElement])
                                    .outputs(vec![Type::array(
                                        Type::Boolean,
                                        T::get_required_bits(),
                                    )]),
                            ),
                            vec![FieldElementExpression::Sub(
                                box FieldElementExpression::Mult(
                                    box left,
                                    box FieldElementExpression::Number(T::from(2)),
                                ),
                                box FieldElementExpression::Mult(
                                    box right,
                                    box FieldElementExpression::Number(T::from(2)),
                                ),
                            )
                            .into()],
                            vec![Type::array(Type::Boolean, T::get_required_bits())],
                        ),
                    ),
                ]);

                self.counter += 1;

                BooleanExpression::Select(
                    box ArrayExpressionInner::Identifier(diff_bits)
                        .annotate(Type::Boolean, T::get_required_bits()),
                    box FieldElementExpression::Number(T::from(T::get_required_bits() - 1)),
                )
            }
            e => fold_boolean_expression(self, e),
        }
    }

    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        let s = fold_statement(self, s);
        self.statements.drain(..).chain(s.into_iter()).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;
}
