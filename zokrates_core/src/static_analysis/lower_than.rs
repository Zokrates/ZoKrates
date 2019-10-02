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


impl<'ast, T: Field> LowerThan<'ast, T> {

// strict check for a <= b
// where b is a constant known at compile time
    fn strict_le_check(b: Vec<bool>, a: Identifier<'ast>) -> Vec<TypedStatement<'ast, T>> {
    // check that b is a bool array
    // check that len a  == len b
    let len = b.len();

    let mut statements = vec![];

    // as long as this value is true we don't
    // know if the value is smaller
    // hence we init with true 
    statements.push(TypedStatement::Definition(
        TypedAssignee::Identifier(Variable::boolean("sizeUnknown0".into())),
        TypedExpression::Boolean(BooleanExpression::Value(true)),
    ));

    for (i, b) in b.iter().enumerate() {
        if *b {
            statements.extend(vec![
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::boolean(
                        format!("isNotSmallerRun{}", i).as_str().into(),
                    )),
                    BooleanExpression::Select(
                        box ArrayExpressionInner::Identifier(a)
                            .annotate(Type::Boolean, len),
                        box FieldElementExpression::Number(T::from(i)),
                    )
                    .into(),
                ),
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::boolean(
                        format!("sizeUnknown{}", i + 1).as_str().into(),
                    )),
                    BooleanExpression::And(
                        box BooleanExpression::Identifier(
                            Variable::boolean(format!("sizeUnknown{}", i).as_str().into()).id,
                        ),
                        box BooleanExpression::Identifier(
                            Variable::boolean(
                        format!("isNotSmallerRun{}", i).as_str().into()
                            ).id
                        )
                    )
                    .into(),
                ),
            ]);
        } else {
            statements.extend(vec![
                // if sizeUnknown == true => a must be false
                // if sizeUnknown == false => a can be true or false
                // => 1 constraint each
                //  true == (!sizeUnknown || !a[3])
                TypedStatement::Condition(
                    TypedExpression::Boolean(BooleanExpression::Value(true)),
                    BooleanExpression::Or(
                        box BooleanExpression::Not(box BooleanExpression::Identifier(
                            Variable::boolean(format!("sizeUnknown{}", i).as_str().into()).id,
                        )),
                        box BooleanExpression::Not(box BooleanExpression::Select(
                            box ArrayExpressionInner::Identifier(a)
                                .annotate(Type::Boolean, len),
                            box FieldElementExpression::Number(T::from(i)),
                        )),
                    )
                    .into(),
                ),
            ])
        }
    }
    statements
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
                    ), //TODOs:
                       // * not using internal identifiers atm
                       //  assume a = 1 1 0 1
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::array("a".into(), Type::Boolean, 4)),
                        ArrayExpressionInner::Value(vec![
                            BooleanExpression::Value(true).into(),
                            BooleanExpression::Value(true).into(),
                            BooleanExpression::Value(false).into(),
                            BooleanExpression::Value(true).into(),
                        ])
                        .annotate(Type::Boolean, 4)
                        .into(),
                    ),
                    // TypedStatement::Definition(
                    //     TypedAssignee::Identifier(Variable::field_element(
                    //         "isNotSmallerRun0".into(),
                    //     )),
                    //     BooleanExpression::Select(
                    //         box ArrayExpressionInner::Identifier("a".into())
                    //             .annotate(Type::Boolean, 4),
                    //         box FieldElementExpression::Number(T::from(0)),
                    //     )
                    //     .into(),
                    // ),
                    // TypedStatement::Definition(
                    //     TypedAssignee::Identifier(Variable::boolean("sizeUnknown1".into())),
                    //     BooleanExpression::And(
                    //         box BooleanExpression::Identifier(
                    //             Variable::boolean("sizeUnknown".into()).id,
                    //         ),
                    //         box BooleanExpression::Eq(
                    //             // there should be a way to get around this equality constraint
                    //             box FieldElementExpression::Identifier(
                    //                 Variable::field_element("isNotSmallerRun0".into()).id,
                    //             ),
                    //             box FieldElementExpression::Number(T::from(1).into()),
                    //         ),
                    //     )
                    //     .into(),
                    // ),
                    // // b[3] = 0
                    // // if sizeUnknown == true => a must be false
                    // // if sizeUnknown == false => a can be true or false
                    // // => 1 constraint each
                    // //  true == (!sizeUnknown || !a[3])
                    // TypedStatement::Condition(
                    //     TypedExpression::Boolean(BooleanExpression::Value(true)),
                    //     BooleanExpression::Or(
                    //         box BooleanExpression::Not(box BooleanExpression::Identifier(
                    //             Variable::boolean("sizeUnknown1".into()).id,
                    //         )),
                    //         box BooleanExpression::Not(box BooleanExpression::Select(
                    //             box ArrayExpressionInner::Identifier("a".into())
                    //                 .annotate(Type::Boolean, 4),
                    //             box FieldElementExpression::Number(T::from(3)),
                    //         )),
                    //     )
                    //     .into(),
                    // ),
                    // add new statements above here!
                ]);

                // self.statements.extend(strict_le_check(
                //     vec![true, true, true, true],
                //     // pass a identifier here
                //     &Variable::array("a".into(), Type::Boolean, 4).id
                // ).into_iter());

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
