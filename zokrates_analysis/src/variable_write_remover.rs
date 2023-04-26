//! Module containing SSA reduction, including for-loop unrolling
//!
//! @file unroll.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use std::collections::HashSet;
use std::fmt;
use zokrates_ast::common::{Span, WithSpan};
use zokrates_ast::typed::result_folder::ResultFolder;
use zokrates_ast::typed::result_folder::*;
use zokrates_ast::typed::types::{MemberId, Type};
use zokrates_ast::typed::*;
use zokrates_field::Field;

#[derive(Debug)]
pub struct Error(String);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub struct VariableWriteRemover;

impl<'ast> VariableWriteRemover {
    fn new() -> Self {
        VariableWriteRemover
    }

    pub fn apply<T: Field>(p: TypedProgram<T>) -> Result<TypedProgram<T>, Error> {
        let mut remover = VariableWriteRemover::new();
        remover.fold_program(p)
    }

    fn choose_many<T: Field>(
        base: TypedExpression<'ast, T>,
        indices: Vec<Access<'ast, T>>,
        new_expression: TypedExpression<'ast, T>,
        statements: &mut HashSet<TypedStatement<'ast, T>>,
        span: Option<Span>,
    ) -> TypedExpression<'ast, T> {
        let mut indices = indices;

        match indices.len() {
            0 => new_expression,
            _ => match base {
                TypedExpression::Array(base) => {
                    let inner_ty = base.inner_type();
                    let size = base.size();

                    let size: u32 = size.try_into().unwrap();

                    let head = indices.remove(0);
                    let tail = indices;

                    match head {
                        Access::Select(head) => {
                            statements.insert(TypedStatement::assertion(
                                BooleanExpression::uint_lt(
                                    head.clone(),
                                    UExpression::from(size).span(span),
                                )
                                .span(span),
                                RuntimeError::SelectRangeCheck,
                            ));

                            ArrayExpression::value(
                                (0..size)
                                    .map(|i| match inner_ty {
                                        Type::Int => unreachable!(),
                                        Type::Array(..) => ArrayExpression::conditional(
                                            BooleanExpression::uint_eq(
                                                UExpression::from(i).span(span),
                                                head.clone(),
                                            )
                                            .span(span),
                                            match Self::choose_many(
                                                ArrayExpression::select(
                                                    base.clone(),
                                                    UExpression::from(i).span(span),
                                                )
                                                .span(span)
                                                .into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                                span,
                                            ) {
                                                TypedExpression::Array(e) => e,
                                                e => unreachable!(
                                            "the interior was expected to be an array, was {}",
                                            e.get_type()
                                        ),
                                            },
                                            ArrayExpression::select(
                                                base.clone(),
                                                UExpression::from(i).span(span),
                                            )
                                            .span(span),
                                            ConditionalKind::IfElse,
                                        )
                                        .into(),
                                        Type::Struct(..) => StructExpression::conditional(
                                            BooleanExpression::uint_eq(
                                                UExpression::from(i).span(span),
                                                head.clone(),
                                            )
                                            .span(span),
                                            match Self::choose_many(
                                                StructExpression::select(
                                                    base.clone(),
                                                    UExpression::from(i).span(span),
                                                )
                                                .span(span)
                                                .span(span)
                                                .into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                                span,
                                            ) {
                                                TypedExpression::Struct(e) => e,
                                                e => unreachable!(
                                            "the interior was expected to be a struct, was {}",
                                            e.get_type()
                                        ),
                                            },
                                            StructExpression::select(
                                                base.clone(),
                                                UExpression::from(i).span(span),
                                            )
                                            .span(span),
                                            ConditionalKind::IfElse,
                                        )
                                        .into(),
                                        Type::Tuple(..) => TupleExpression::conditional(
                                            BooleanExpression::uint_eq(
                                                UExpression::from(i).span(span),
                                                head.clone(),
                                            )
                                            .span(span),
                                            match Self::choose_many(
                                                TupleExpression::select(
                                                    base.clone(),
                                                    UExpression::from(i).span(span),
                                                )
                                                .span(span)
                                                .into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                                span,
                                            ) {
                                                TypedExpression::Tuple(e) => e,
                                                e => unreachable!(
                                            "the interior was expected to be a tuple, was {}",
                                            e.get_type()
                                        ),
                                            },
                                            TupleExpression::select(
                                                base.clone(),
                                                UExpression::from(i).span(span),
                                            )
                                            .span(span),
                                            ConditionalKind::IfElse,
                                        )
                                        .into(),
                                        Type::FieldElement => FieldElementExpression::conditional(
                                            BooleanExpression::uint_eq(
                                                UExpression::from(i).span(span),
                                                head.clone(),
                                            )
                                            .span(span),
                                            match Self::choose_many(
                                                FieldElementExpression::select(
                                                    base.clone(),
                                                    UExpression::from(i).span(span),
                                                )
                                                .span(span)
                                                .into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                                span,
                                            ) {
                                                TypedExpression::FieldElement(e) => e,
                                                e => unreachable!(
                                            "the interior was expected to be a field, was {}",
                                            e.get_type()
                                        ),
                                            },
                                            FieldElementExpression::select(
                                                base.clone(),
                                                UExpression::from(i).span(span),
                                            )
                                            .span(span),
                                            ConditionalKind::IfElse,
                                        )
                                        .into(),
                                        Type::Boolean => BooleanExpression::conditional(
                                            BooleanExpression::uint_eq(
                                                UExpression::from(i).span(span),
                                                head.clone(),
                                            )
                                            .span(span),
                                            match Self::choose_many(
                                                BooleanExpression::select(
                                                    base.clone(),
                                                    UExpression::from(i).span(span),
                                                )
                                                .span(span)
                                                .into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                                span,
                                            ) {
                                                TypedExpression::Boolean(e) => e,
                                                e => unreachable!(
                                            "the interior was expected to be a boolean, was {}",
                                            e.get_type()
                                        ),
                                            },
                                            BooleanExpression::select(
                                                base.clone(),
                                                UExpression::from(i).span(span),
                                            )
                                            .span(span),
                                            ConditionalKind::IfElse,
                                        )
                                        .into(),
                                        Type::Uint(..) => UExpression::conditional(
                                            BooleanExpression::uint_eq(
                                                UExpression::from(i).span(span),
                                                head.clone(),
                                            )
                                            .span(span),
                                            match Self::choose_many(
                                                UExpression::select(
                                                    base.clone(),
                                                    UExpression::from(i).span(span),
                                                )
                                                .span(span)
                                                .into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                                span,
                                            ) {
                                                TypedExpression::Uint(e) => e,
                                                e => unreachable!(
                                            "the interior was expected to be a uint, was {}",
                                            e.get_type()
                                        ),
                                            },
                                            UExpression::select(
                                                base.clone(),
                                                UExpression::from(i).span(span),
                                            )
                                            .span(span),
                                            ConditionalKind::IfElse,
                                        )
                                        .into(),
                                    })
                                    .collect::<Vec<_>>(),
                            )
                            .annotate(ArrayType::new(inner_ty.clone(), size))
                            .into()
                        }
                        _ => unreachable!(),
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
                                                span,
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
                                                span,
                                            )
                                        } else {
                                            UExpression::member(base.clone(), member.id)
                                                .span(span)
                                                .into()
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
                                                span,
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
                                                span,
                                            )
                                        } else {
                                            ArrayExpression::member(base.clone(), member.id)
                                                .span(span)
                                                .into()
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
                                                span,
                                            )
                                        } else {
                                            StructExpression::member(base.clone(), member.id)
                                                .span(span)
                                                .into()
                                        }
                                    }
                                    Type::Tuple(..) => {
                                        if member.id == head {
                                            Self::choose_many(
                                                TupleExpression::member(base.clone(), head.clone())
                                                    .into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                                span,
                                            )
                                        } else {
                                            TupleExpression::member(base.clone(), member.id)
                                                .span(span)
                                                .into()
                                        }
                                    }
                                })
                                .collect(),
                        )
                        .annotate(members)
                        .into(),
                        _ => unreachable!(),
                    }
                }
                TypedExpression::Tuple(base) => {
                    let tuple_ty = match base.get_type() {
                        Type::Tuple(tuple_ty) => tuple_ty.clone(),
                        _ => unreachable!(),
                    };

                    let head = indices.remove(0);
                    let tail = indices;

                    match head {
                        Access::Element(head) => TupleExpressionInner::Value(
                            tuple_ty
                                .clone()
                                .elements
                                .into_iter()
                                .enumerate()
                                .map(|(i, ty)| (i as u32, ty))
                                .map(|(i, ty)| match ty {
                                    Type::Int => unreachable!(),
                                    Type::FieldElement => {
                                        if i == head {
                                            Self::choose_many(
                                                FieldElementExpression::element(base.clone(), head)
                                                    .into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                                span,
                                            )
                                        } else {
                                            FieldElementExpression::element(base.clone(), i)
                                                .span(span)
                                                .into()
                                        }
                                    }
                                    Type::Uint(..) => {
                                        if i == head {
                                            Self::choose_many(
                                                UExpression::element(base.clone(), head).into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                                span,
                                            )
                                        } else {
                                            UExpression::element(base.clone(), i).span(span).into()
                                        }
                                    }
                                    Type::Boolean => {
                                        if i == head {
                                            Self::choose_many(
                                                BooleanExpression::element(base.clone(), head)
                                                    .into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                                span,
                                            )
                                        } else {
                                            BooleanExpression::element(base.clone(), i)
                                                .span(span)
                                                .into()
                                        }
                                    }
                                    Type::Array(..) => {
                                        if i == head {
                                            Self::choose_many(
                                                ArrayExpression::element(base.clone(), head).into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                                span,
                                            )
                                        } else {
                                            ArrayExpression::element(base.clone(), i)
                                                .span(span)
                                                .into()
                                        }
                                    }
                                    Type::Struct(..) => {
                                        if i == head {
                                            Self::choose_many(
                                                StructExpression::element(base.clone(), head)
                                                    .into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                                span,
                                            )
                                        } else {
                                            StructExpression::element(base.clone(), i)
                                                .span(span)
                                                .into()
                                        }
                                    }
                                    Type::Tuple(..) => {
                                        if i == head {
                                            Self::choose_many(
                                                TupleExpression::element(base.clone(), head).into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                                span,
                                            )
                                        } else {
                                            TupleExpression::element(base.clone(), i)
                                                .span(span)
                                                .into()
                                        }
                                    }
                                })
                                .collect(),
                        )
                        .annotate(tuple_ty)
                        .into(),
                        _ => unreachable!(),
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
    Element(u32),
}

/// Turn an assignee into its representation as a base variable and a list accesses
/// a[2][3][4] -> (a, [2, 3, 4])
fn linear<T: Field>(a: TypedAssignee<T>) -> (Variable<T>, Vec<Access<T>>) {
    match a {
        TypedAssignee::Identifier(v) => (v, vec![]),
        TypedAssignee::Select(array, index) => {
            let (v, mut indices) = linear(*array);
            indices.push(Access::Select(*index));
            (v, indices)
        }
        TypedAssignee::Member(s, m) => {
            let (v, mut indices) = linear(*s);
            indices.push(Access::Member(m));
            (v, indices)
        }
        TypedAssignee::Element(s, i) => {
            let (v, mut indices) = linear(*s);
            indices.push(Access::Element(i));
            (v, indices)
        }
    }
}

fn is_constant<T>(assignee: &TypedAssignee<T>) -> bool {
    match assignee {
        TypedAssignee::Identifier(_) => true,
        TypedAssignee::Select(assignee, index) => match index.as_inner() {
            UExpressionInner::Value(_) => is_constant(assignee),
            _ => false,
        },
        TypedAssignee::Member(ref assignee, _) => is_constant(assignee),
        TypedAssignee::Element(ref assignee, _) => is_constant(assignee),
    }
}

impl<'ast, T: Field> ResultFolder<'ast, T> for VariableWriteRemover {
    type Error = Error;

    fn fold_assembly_assignment(
        &mut self,
        s: AssemblyAssignment<'ast, T>,
    ) -> Result<Vec<TypedAssemblyStatement<'ast, T>>, Self::Error> {
        match is_constant(&s.assignee) {
            true => Ok(vec![TypedAssemblyStatement::Assignment(s)]),
            false => Err(Error(format!(
                "Cannot assign to an assignee with a variable index `{}`",
                s.assignee
            ))),
        }
    }

    fn fold_assembly_constraint(
        &mut self,
        s: AssemblyConstraint<'ast, T>,
    ) -> Result<Vec<TypedAssemblyStatement<'ast, T>>, Self::Error> {
        Ok(vec![TypedAssemblyStatement::Constraint(s)])
    }

    fn fold_definition_statement(
        &mut self,
        s: DefinitionStatement<'ast, T>,
    ) -> Result<Vec<TypedStatement<'ast, T>>, Self::Error> {
        let span = s.get_span();

        match s.rhs {
            DefinitionRhs::Expression(expr) => {
                let a = s.assignee;
                let expr = self.fold_expression(expr)?;

                if is_constant(&a) {
                    Ok(vec![TypedStatement::definition(a, expr).span(span)])
                } else {
                    // Note: here we redefine the whole object, ideally we would only redefine some of it
                    // Example: `a[0][i] = 42` we redefine `a` but we could redefine just `a[0]`

                    let (variable, indices) = linear(a);

                    let base: TypedExpression<'ast, T> = match variable.get_type() {
                        Type::Int => unreachable!(),
                        Type::FieldElement => {
                            FieldElementExpression::identifier(variable.id.clone()).into()
                        }
                        Type::Boolean => BooleanExpression::identifier(variable.id.clone()).into(),
                        Type::Uint(bitwidth) => UExpression::identifier(variable.id.clone())
                            .annotate(bitwidth)
                            .into(),
                        Type::Array(array_type) => ArrayExpression::identifier(variable.id.clone())
                            .annotate(array_type)
                            .into(),
                        Type::Struct(members) => StructExpression::identifier(variable.id.clone())
                            .annotate(members)
                            .into(),
                        Type::Tuple(tuple_ty) => TupleExpression::identifier(variable.id.clone())
                            .annotate(tuple_ty)
                            .into(),
                    };

                    let base = base.span(span);

                    let base = self.fold_expression(base)?;

                    let indices = indices
                        .into_iter()
                        .map(|a| match a {
                            Access::Select(i) => Ok(Access::Select(self.fold_uint_expression(i)?)),
                            a => Ok(a),
                        })
                        .collect::<Result<_, _>>()?;

                    let mut range_checks = HashSet::new();
                    let e = Self::choose_many(base, indices, expr, &mut range_checks, span);

                    Ok(range_checks
                        .into_iter()
                        .chain(std::iter::once(
                            TypedStatement::definition(
                                TypedAssignee::Identifier(variable.span(span)),
                                e,
                            )
                            .span(span),
                        ))
                        .collect())
                }
            }
            _ => fold_definition_statement(self, s),
        }
    }
}
