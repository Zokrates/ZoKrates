//! Module containing lower equal comparison of field elements
//!
//! @file lower_than.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @author Stefan Deml <stefandeml@gmail.com>
//! @date 2019



use crate::typed_absy::folder::*;
use crate::typed_absy::*;
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

    // compute 2a - 2b
    fn compute_2diff(
        &mut self,
        left: FieldElementExpression<'ast, T>,
        right: FieldElementExpression<'ast, T>,
    ) -> ArrayExpression<'ast, T> {
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
                            .outputs(vec![Type::array(Type::Boolean, T::get_required_bits())]),
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
                            .outputs(vec![Type::array(Type::Boolean, T::get_required_bits())]),
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
                            .outputs(vec![Type::array(Type::Boolean, T::get_required_bits())]),
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
        ArrayExpressionInner::Identifier(diff_bits.clone())
            .annotate(Type::Boolean, T::get_required_bits())
    }

    // strict check for a <= b
    // where b is a constant known at compile time
    fn strict_le_check(&mut self, b: &[bool], a: ArrayExpression<'ast, T>) {
        let len = b.len();
        assert_eq!(a.get_type(), Type::array(Type::Boolean, len));

        let mut is_not_smaller_run = vec![];
        let mut size_unknown = vec![];
        for _i in 0..len {
            is_not_smaller_run.push(Identifier::internal("isNotSmallerRun", self.counter));
            size_unknown.push(Identifier::internal("sizeUnknown", self.counter));
            self.counter += 1;
        }

        // as long as size_unknown is true we don't
        // know if a is smaller
        // hence we init with true
        self.statements.push(TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::boolean(size_unknown[0].clone())),
            TypedExpression::Boolean(BooleanExpression::Value(true)),
        ));

        for (i, b) in b.iter().enumerate() {
            if *b {
                self.statements.push(TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::boolean(is_not_smaller_run[i].clone())),
                    BooleanExpression::Select(
                        box a.clone(),
                        box FieldElementExpression::Number(T::from(i)),
                    )
                    .into(),
                ));

                // don't need to update size_unknown in the last round
                if i < len - 1 {
                    self.statements.push(TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::boolean(size_unknown[i + 1].clone())),
                        BooleanExpression::And(
                            box BooleanExpression::Identifier(
                                Variable::boolean(size_unknown[i].clone()).id,
                            ),
                            box BooleanExpression::Identifier(
                                Variable::boolean(is_not_smaller_run[i].clone()).id,
                            ),
                        )
                        .into(),
                    ));
                }
            } else {
                // don't need to update size_unknown in the last round
                if i < len - 1 {
                    self.statements.push(
                        // sizeUnknown is not changing in this case
                        // We sill have to assign the old value to the variable of the current run
                        // This trivial definition will later be removed by the optimiser
                        TypedStatement::Definition(
                            TypedAssignee::Identifier(Variable::boolean(
                                size_unknown[i + 1].clone(),
                            )),
                            BooleanExpression::Identifier(
                                Variable::boolean(size_unknown[i].clone()).id,
                            )
                            .into(),
                        ),
                    );
                }
                self.statements.push(TypedStatement::Condition(
                    TypedExpression::Boolean(BooleanExpression::Value(true)),
                    BooleanExpression::Or(
                        box BooleanExpression::Not(box BooleanExpression::Identifier(
                            Variable::boolean(size_unknown[i].clone()).id,
                        )),
                        box BooleanExpression::Not(box BooleanExpression::Select(
                            box a.clone(),
                            box FieldElementExpression::Number(T::from(i)),
                        )),
                    )
                    .into(),
                ));
            }
        }
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
                let diff_bits = self.compute_2diff(left, right);

                self.statements.push(TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::array("a".into(), Type::Boolean, 4)),
                    ArrayExpressionInner::Value(vec![
                        BooleanExpression::Value(true).into(),
                        BooleanExpression::Value(true).into(),
                        BooleanExpression::Value(false).into(),
                        BooleanExpression::Value(true).into(),
                    ])
                    .annotate(Type::Boolean, 4)
                    .into(),
                ));

                // get max value of the field as big-endian bit vector
                let field_bits_be = T::max_value_bit_vector_be();
                // drop the two most significant bits
                let field_bits_be = &field_bits_be[2..];
                self.strict_le_check(field_bits_be, diff_bits.clone());

                self.counter += 1;

                BooleanExpression::Select(
                    box diff_bits,
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

    // define boolean array:
    // self.statements.push(TypedStatement::Definition(
    //                 TypedAssignee::Identifier(Variable::array("a".into(), Type::Boolean, 4)),
    //                 ArrayExpressionInner::Value(vec![
    //                     BooleanExpression::Value(true).into(),
    //                     BooleanExpression::Value(true).into(),
    //                     BooleanExpression::Value(false).into(),
    //                     BooleanExpression::Value(true).into(),
    //                 ])
    //                 .annotate(Type::Boolean, 4)
    //                 .into(),
    //             ));

    // then different cases
    //    self.strict_le_check(
    //         vec![true, true, true, false],
    //         Variable::array("a".into(), Type::Boolean, 4).id.clone(),
    //     );
}
