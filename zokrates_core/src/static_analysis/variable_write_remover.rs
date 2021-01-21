//! Module containing SSA reduction, including for-loop unrolling
//!
//! @file unroll.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use crate::typed_absy::folder::*;
use crate::typed_absy::types::{MemberId, Type};
use crate::typed_absy::*;
use std::collections::HashSet;
use zokrates_field::Field;

pub struct VariableWriteRemover;

impl<'ast> VariableWriteRemover {
    fn new() -> Self {
        VariableWriteRemover
    }

    pub fn apply<T: Field>(p: TypedProgram<T>) -> TypedProgram<T> {
        let mut remover = VariableWriteRemover::new();
        remover.fold_program(p)
    }

    fn choose_many<T: Field>(
        base: TypedExpression<'ast, T>,
        indices: Vec<Access<'ast, T>>,
        new_expression: TypedExpression<'ast, T>,
        statements: &mut HashSet<TypedStatement<'ast, T>>,
    ) -> TypedExpression<'ast, T> {
        let mut indices = indices;

        match indices.len() {
            0 => new_expression,
            _ => match base {
                TypedExpression::Array(base) => {
                    let inner_ty = base.inner_type();
                    let size = base.size();

                    let size = match size.as_inner() {
                        UExpressionInner::Value(v) => *v as u32,
                        _ => unreachable!(),
                    };

                    let head = indices.remove(0);
                    let tail = indices;

                    match head {
                        Access::Select(head) => {
                            statements.insert(TypedStatement::Assertion(
                                BooleanExpression::UintLt(box head.clone(), box size.into()),
                            ));

                            ArrayExpressionInner::Value(
                                (0..size)
                                    .map(|i| match inner_ty {
                                        Type::Int => unreachable!(),
                                        Type::Array(..) => ArrayExpression::if_else(
                                            BooleanExpression::UintEq(
                                                box i.into(),
                                                box head.clone(),
                                            ),
                                            match Self::choose_many(
                                                ArrayExpression::select(base.clone(), i).into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                            ) {
                                                TypedExpression::Array(e) => e,
                                                e => unreachable!(
                                            "the interior was expected to be an array, was {}",
                                            e.get_type()
                                        ),
                                            },
                                            ArrayExpression::select(base.clone(), i),
                                        )
                                        .into(),
                                        Type::Struct(..) => StructExpression::if_else(
                                            BooleanExpression::UintEq(
                                                box i.into(),
                                                box head.clone(),
                                            ),
                                            match Self::choose_many(
                                                StructExpression::select(base.clone(), i).into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                            ) {
                                                TypedExpression::Struct(e) => e,
                                                e => unreachable!(
                                            "the interior was expected to be a struct, was {}",
                                            e.get_type()
                                        ),
                                            },
                                            StructExpression::select(base.clone(), i),
                                        )
                                        .into(),
                                        Type::FieldElement => FieldElementExpression::if_else(
                                            BooleanExpression::UintEq(
                                                box i.into(),
                                                box head.clone(),
                                            ),
                                            match Self::choose_many(
                                                FieldElementExpression::select(base.clone(), i)
                                                    .into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                            ) {
                                                TypedExpression::FieldElement(e) => e,
                                                e => unreachable!(
                                            "the interior was expected to be a field, was {}",
                                            e.get_type()
                                        ),
                                            },
                                            FieldElementExpression::select(base.clone(), i),
                                        )
                                        .into(),
                                        Type::Boolean => BooleanExpression::if_else(
                                            BooleanExpression::UintEq(
                                                box i.into(),
                                                box head.clone(),
                                            ),
                                            match Self::choose_many(
                                                BooleanExpression::select(base.clone(), i).into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                            ) {
                                                TypedExpression::Boolean(e) => e,
                                                e => unreachable!(
                                            "the interior was expected to be a boolean, was {}",
                                            e.get_type()
                                        ),
                                            },
                                            BooleanExpression::select(base.clone(), i),
                                        )
                                        .into(),
                                        Type::Uint(..) => UExpression::if_else(
                                            BooleanExpression::UintEq(
                                                box i.into(),
                                                box head.clone(),
                                            ),
                                            match Self::choose_many(
                                                UExpression::select(base.clone(), i).into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                            ) {
                                                TypedExpression::Uint(e) => e,
                                                e => unreachable!(
                                            "the interior was expected to be a uint, was {}",
                                            e.get_type()
                                        ),
                                            },
                                            UExpression::select(base.clone(), i),
                                        )
                                        .into(),
                                    })
                                    .collect::<Vec<_>>()
                                    .into(),
                            )
                            .annotate(inner_ty.clone(), size)
                            .into()
                        }
                        Access::Member(..) => unreachable!("can't get a member from an array"),
                    }
                }
                TypedExpression::Struct(base) => {
                    let members = match base.get_type() {
                        Type::Struct(members) => members.clone(),
                        _ => unreachable!(),
                    };

                    let head = indices.remove(0);
                    let tail = indices;

                    match head {
                        Access::Member(head) => StructExpressionInner::Value(
                            members
                                .clone()
                                .into_iter()
                                .map(|member| match *member.ty {
                                    Type::Int => unreachable!(),
                                    Type::FieldElement => {
                                        if member.id == head {
                                            Self::choose_many(
                                                FieldElementExpression::member(
                                                    base.clone(),
                                                    head.clone(),
                                                )
                                                .into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                            )
                                        } else {
                                            FieldElementExpression::member(base.clone(), member.id)
                                                .into()
                                        }
                                    }
                                    Type::Uint(..) => {
                                        if member.id == head {
                                            Self::choose_many(
                                                UExpression::member(base.clone(), head.clone())
                                                    .into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                            )
                                        } else {
                                            UExpression::member(base.clone(), member.id).into()
                                        }
                                    }
                                    Type::Boolean => {
                                        if member.id == head {
                                            Self::choose_many(
                                                BooleanExpression::member(
                                                    base.clone(),
                                                    head.clone(),
                                                )
                                                .into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                            )
                                        } else {
                                            BooleanExpression::member(base.clone(), member.id)
                                                .into()
                                        }
                                    }
                                    Type::Array(..) => {
                                        if member.id == head {
                                            Self::choose_many(
                                                ArrayExpression::member(base.clone(), head.clone())
                                                    .into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                            )
                                        } else {
                                            ArrayExpression::member(base.clone(), member.id).into()
                                        }
                                    }
                                    Type::Struct(..) => {
                                        if member.id == head {
                                            Self::choose_many(
                                                StructExpression::member(
                                                    base.clone(),
                                                    head.clone(),
                                                )
                                                .into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                            )
                                        } else {
                                            StructExpression::member(base.clone(), member.id).into()
                                        }
                                    }
                                })
                                .collect(),
                        )
                        .annotate(members)
                        .into(),
                        Access::Select(..) => unreachable!("can't get a element from a struct"),
                    }
                }
                e => unreachable!("can't make an access on a {}", e.get_type()),
            },
        }
    }
}

#[derive(Clone, Debug)]
enum Access<'ast, T: Field> {
    Select(UExpression<'ast, T>),
    Member(MemberId),
}
/// Turn an assignee into its representation as a base variable and a list accesses
/// a[2][3][4] -> (a, [2, 3, 4])
fn linear<T: Field>(a: TypedAssignee<T>) -> (Variable<T>, Vec<Access<T>>) {
    match a {
        TypedAssignee::Identifier(v) => (v, vec![]),
        TypedAssignee::Select(box array, box index) => {
            let (v, mut indices) = linear(array);
            indices.push(Access::Select(index));
            (v, indices)
        }
        TypedAssignee::Member(box s, m) => {
            let (v, mut indices) = linear(s);
            indices.push(Access::Member(m));
            (v, indices)
        }
    }
}

fn is_constant<T>(assignee: &TypedAssignee<T>) -> bool {
    match assignee {
        TypedAssignee::Identifier(_) => true,
        TypedAssignee::Select(box assignee, box index) => match index.as_inner() {
            UExpressionInner::Value(_) => is_constant(assignee),
            _ => false,
        },
        TypedAssignee::Member(box assignee, _) => is_constant(assignee),
    }
}

impl<'ast, T: Field> Folder<'ast, T> for VariableWriteRemover {
    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        match s {
            TypedStatement::Definition(assignee, expr) => {
                if is_constant(&assignee) {
                    vec![TypedStatement::Definition(assignee, expr)]
                } else {
                    // Note: here we redefine the whole object, ideally we would only redefine some of it
                    // Example: `a[0][i] = 42` we redefine `a` but we could redefine just `a[0]`
                    let expr = self.fold_expression(expr);

                    let (variable, indices) = linear(assignee);

                    let base = match variable.get_type() {
                        Type::Int => unreachable!(),
                        Type::FieldElement => {
                            FieldElementExpression::Identifier(variable.id.clone()).into()
                        }
                        Type::Boolean => BooleanExpression::Identifier(variable.id.clone()).into(),
                        Type::Uint(bitwidth) => UExpressionInner::Identifier(variable.id.clone())
                            .annotate(bitwidth)
                            .into(),
                        Type::Array(array_type) => {
                            ArrayExpressionInner::Identifier(variable.id.clone())
                                .annotate(*array_type.ty, array_type.size)
                                .into()
                        }
                        Type::Struct(members) => {
                            StructExpressionInner::Identifier(variable.id.clone())
                                .annotate(members)
                                .into()
                        }
                    };

                    let base = self.fold_expression(base);

                    let indices = indices
                        .into_iter()
                        .map(|a| match a {
                            Access::Select(i) => Access::Select(self.fold_uint_expression(i)),
                            a => a,
                        })
                        .collect();

                    let mut range_checks = HashSet::new();
                    let e = Self::choose_many(base, indices, expr, &mut range_checks);

                    range_checks
                        .into_iter()
                        .chain(std::iter::once(TypedStatement::Definition(
                            TypedAssignee::Identifier(variable),
                            e,
                        )))
                        .collect()
                }
            }
            s => fold_statement(self, s),
        }
    }
}
