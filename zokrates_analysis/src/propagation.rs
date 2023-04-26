//! Module containing constant propagation for the typed AST
//!
//! Constant propagation on the SSA program. The constants map can be passed by the caller to allow for many passes to use
//! the same constants.
//!
//! @file propagation.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use num::traits::Pow;
use num_bigint::BigUint;
use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};
use std::fmt;
use std::ops::*;
use std::ops::{BitAnd, BitOr, BitXor, Shl, Shr, Sub};
use zokrates_ast::common::expressions::{
    BinaryExpression, BinaryOrExpression, EqExpression, ValueExpression,
};
use zokrates_ast::common::operators::OpEq;
use zokrates_ast::common::{FlatEmbed, ResultFold, WithSpan};
use zokrates_ast::typed::result_folder::*;
use zokrates_ast::typed::types::Type;
use zokrates_ast::typed::*;
use zokrates_field::Field;

pub type Constants<'ast, T> = HashMap<Identifier<'ast>, TypedExpression<'ast, T>>;

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    Type(String),
    AssertionFailed(RuntimeError),
    InvalidValue(String),
    OutOfBounds(u128, u128),
    VariableLength(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Type(s) => write!(f, "{}", s),
            Error::AssertionFailed(err) => write!(f, "Assertion failed ({})", err),
            Error::InvalidValue(s) => write!(f, "{}", s),
            Error::OutOfBounds(index, size) => write!(
                f,
                "Out of bounds index ({} >= {}) found during static analysis",
                index, size
            ),
            Error::VariableLength(message) => write!(f, "{}", message),
        }
    }
}

#[derive(Debug, Default)]
pub struct Propagator<'ast, T> {
    // constants keeps track of constant expressions
    // we currently do not support partially constant expressions: `field [x, 1][1]` is not considered constant, `field [0, 1][1]` is
    constants: Constants<'ast, T>,
}

impl<'ast, T: Field> Propagator<'ast, T> {
    pub fn propagate(p: TypedProgram<'ast, T>) -> Result<TypedProgram<'ast, T>, Error> {
        Propagator::default().fold_program(p)
    }

    pub fn clear_call_frame(&mut self, frame: usize) {
        self.constants.retain(|id, _| id.id.frame != frame);
    }

    // get a mutable reference to the constant corresponding to a given assignee if any, otherwise
    // return the identifier at the root of this assignee
    fn try_get_constant_mut<'b>(
        &mut self,
        assignee: &'b TypedAssignee<'ast, T>,
    ) -> Result<(&'b Variable<'ast, T>, &mut TypedExpression<'ast, T>), &'b Variable<'ast, T>> {
        match assignee {
            TypedAssignee::Identifier(var) => self
                .constants
                .get_mut(&var.id)
                .map(|c| Ok((var, c)))
                .unwrap_or(Err(var)),
            TypedAssignee::Select(assignee, index) => match self.try_get_constant_mut(assignee) {
                Ok((variable, constant)) => match index.as_inner() {
                    UExpressionInner::Value(n) => match constant {
                        TypedExpression::Array(a) => match a.as_inner_mut() {
                            ArrayExpressionInner::Value(value) => {
                                match value.value.get_mut(n.value as usize) {
                                    Some(TypedExpressionOrSpread::Expression(ref mut e)) => {
                                        Ok((variable, e))
                                    }
                                    None => Err(variable),
                                    _ => unreachable!(),
                                }
                            }
                            _ => unreachable!("should be an array value"),
                        },
                        _ => unreachable!("should be an array expression"),
                    },
                    _ => Err(variable),
                },
                e => e,
            },
            TypedAssignee::Member(assignee, m) => match self.try_get_constant_mut(assignee) {
                Ok((v, c)) => {
                    let ty = assignee.get_type();

                    let index = match ty {
                        Type::Struct(struct_ty) => struct_ty
                            .members
                            .iter()
                            .position(|member| *m == member.id)
                            .unwrap(),
                        _ => unreachable!("should be a struct type"),
                    };

                    match c {
                        TypedExpression::Struct(a) => match a.as_inner_mut() {
                            StructExpressionInner::Value(value) => Ok((v, &mut value.value[index])),
                            _ => unreachable!("should be a struct value"),
                        },
                        _ => unreachable!("should be a struct expression"),
                    }
                }
                e => e,
            },
            TypedAssignee::Element(assignee, index) => match self.try_get_constant_mut(assignee) {
                Ok((v, c)) => match c {
                    TypedExpression::Tuple(a) => match a.as_inner_mut() {
                        TupleExpressionInner::Value(value) => {
                            Ok((v, &mut value.value[*index as usize]))
                        }
                        _ => unreachable!("should be a tuple value"),
                    },
                    _ => unreachable!("should be a tuple expression"),
                },
                e => e,
            },
        }
    }
}

impl<'ast, T: Field> ResultFolder<'ast, T> for Propagator<'ast, T> {
    type Error = Error;

    fn fold_program(&mut self, p: TypedProgram<'ast, T>) -> Result<TypedProgram<'ast, T>, Error> {
        let main = p.main.clone();

        Ok(TypedProgram {
            modules: p
                .modules
                .into_iter()
                .map(|(module_id, module)| {
                    if module_id == main {
                        self.fold_module(module).map(|m| (module_id, m))
                    } else {
                        Ok((module_id, module))
                    }
                })
                .collect::<Result<_, _>>()?,
            ..p
        })
    }

    fn fold_function_symbol_declaration(
        &mut self,
        s: TypedFunctionSymbolDeclaration<'ast, T>,
    ) -> Result<TypedFunctionSymbolDeclaration<'ast, T>, Error> {
        if s.key.id == "main" {
            let key = s.key;
            self.fold_function_symbol(s.symbol)
                .map(|f| TypedFunctionSymbolDeclaration { key, symbol: f })
        } else {
            Ok(s)
        }
    }

    fn fold_conditional_expression<
        E: Expr<'ast, T> + Conditional<'ast, T> + PartialEq + ResultFold<Self, Self::Error>,
    >(
        &mut self,
        _: &E::Ty,
        e: ConditionalExpression<'ast, T, E>,
    ) -> Result<ConditionalOrExpression<'ast, T, E>, Self::Error> {
        Ok(
            match (
                self.fold_boolean_expression(*e.condition)?,
                e.consequence.fold(self)?,
                e.alternative.fold(self)?,
            ) {
                (BooleanExpression::Value(v), consequence, _) if v.value => {
                    ConditionalOrExpression::Expression(consequence.into_inner())
                }
                (BooleanExpression::Value(v), _, alternative) if !v.value => {
                    ConditionalOrExpression::Expression(alternative.into_inner())
                }
                (_, consequence, alternative) if consequence == alternative => {
                    ConditionalOrExpression::Expression(consequence.into_inner())
                }
                (condition, consequence, alternative) => ConditionalOrExpression::Conditional(
                    ConditionalExpression::new(condition, consequence, alternative, e.kind),
                ),
            },
        )
    }

    fn fold_assembly_assignment(
        &mut self,
        s: AssemblyAssignment<'ast, T>,
    ) -> Result<Vec<TypedAssemblyStatement<'ast, T>>, Self::Error> {
        let assignee = self.fold_assignee(s.assignee)?;
        let expr = self.fold_expression(s.expression)?;

        if expr.is_constant() {
            match assignee {
                TypedAssignee::Identifier(var) => {
                    let expr = expr.into_canonical_constant();

                    assert!(self.constants.insert(var.id, expr).is_none());

                    Ok(vec![])
                }
                assignee => match self.try_get_constant_mut(&assignee) {
                    Ok((_, c)) => {
                        *c = expr.into_canonical_constant();
                        Ok(vec![])
                    }
                    Err(v) => match self.constants.remove(&v.id) {
                        // invalidate the cache for this identifier, and define the latest
                        // version of the constant in the program, if any
                        Some(c) => Ok(vec![
                            TypedAssemblyStatement::assignment(v.clone().into(), c),
                            TypedAssemblyStatement::assignment(assignee, expr),
                        ]),
                        None => Ok(vec![TypedAssemblyStatement::assignment(assignee, expr)]),
                    },
                },
            }
        } else {
            // the expression being assigned is not constant, invalidate the cache
            let v = self
                .try_get_constant_mut(&assignee)
                .map(|(v, _)| v)
                .unwrap_or_else(|v| v);

            match self.constants.remove(&v.id) {
                Some(c) => Ok(vec![
                    TypedAssemblyStatement::assignment(v.clone().into(), c),
                    TypedAssemblyStatement::assignment(assignee, expr),
                ]),
                None => Ok(vec![TypedAssemblyStatement::assignment(assignee, expr)]),
            }
        }
    }

    fn fold_assembly_constraint(
        &mut self,
        s: AssemblyConstraint<'ast, T>,
    ) -> Result<Vec<TypedAssemblyStatement<'ast, T>>, Self::Error> {
        let span = s.get_span();

        let left = self.fold_field_expression(s.left)?;
        let right = self.fold_field_expression(s.right)?;

        // a bit hacky, but we use a fake boolean expression to check this
        let is_equal = BooleanExpression::field_eq(left.clone(), right.clone()).span(span);
        let is_equal = self.fold_boolean_expression(is_equal)?;

        match is_equal {
            BooleanExpression::Value(v) if v.value => Ok(vec![]),
            BooleanExpression::Value(v) if !v.value => {
                Err(Error::AssertionFailed(RuntimeError::SourceAssertion(
                    s.metadata
                        .message(Some(format!("In asm block: `{} !== {}`", left, right))),
                )))
            }
            _ => Ok(vec![TypedAssemblyStatement::constraint(
                left, right, s.metadata,
            )]),
        }
    }

    fn fold_definition_statement(
        &mut self,
        s: DefinitionStatement<'ast, T>,
    ) -> Result<Vec<TypedStatement<'ast, T>>, Self::Error> {
        let span = s.get_span();

        match s.rhs {
            // propagation to the defined variable if rhs is a constant
            DefinitionRhs::Expression(e) => {
                let assignee = self.fold_assignee(s.assignee)?;
                let expr = self.fold_expression(e)?;

                if let (Ok(a), Ok(e)) = (
                    ConcreteType::try_from(assignee.get_type()),
                    ConcreteType::try_from(expr.get_type()),
                ) {
                    if a != e {
                        return Err(Error::Type(format!(
                            "Cannot assign {} of type {} to {} of type {}",
                            expr, e, assignee, a
                        )));
                    }
                };

                if expr.is_constant() {
                    match assignee {
                        TypedAssignee::Identifier(var) => {
                            let expr = expr.into_canonical_constant();

                            assert!(self.constants.insert(var.id, expr).is_none());

                            Ok(vec![])
                        }
                        assignee => match self.try_get_constant_mut(&assignee) {
                            Ok((_, c)) => {
                                *c = expr.into_canonical_constant();
                                Ok(vec![])
                            }
                            Err(v) => match self.constants.remove(&v.id) {
                                // invalidate the cache for this identifier, and define the latest
                                // version of the constant in the program, if any
                                Some(c) => Ok(vec![
                                    TypedStatement::definition(v.clone().into(), c),
                                    TypedStatement::definition(assignee, expr),
                                ]),
                                None => Ok(vec![TypedStatement::definition(assignee, expr)]),
                            },
                        },
                    }
                } else {
                    // the expression being assigned is not constant, invalidate the cache
                    let v = self
                        .try_get_constant_mut(&assignee)
                        .map(|(v, _)| v)
                        .unwrap_or_else(|v| v);

                    match self.constants.remove(&v.id) {
                        Some(c) => Ok(vec![
                            TypedStatement::definition(v.clone().into(), c),
                            TypedStatement::definition(assignee, expr),
                        ]),
                        None => Ok(vec![TypedStatement::definition(assignee, expr)]),
                    }
                }
            }
            DefinitionRhs::EmbedCall(e) => {
                let assignee = self.fold_assignee(s.assignee)?;
                let embed_call = self.fold_embed_call(e)?;

                fn process_u_from_bits<'ast, T: Field>(
                    arguments: &[TypedExpression<'ast, T>],
                    bitwidth: UBitwidth,
                ) -> TypedExpression<'ast, T> {
                    assert_eq!(arguments.len(), 1);

                    let argument = arguments.last().cloned().unwrap();
                    let argument = argument.into_canonical_constant();

                    match ArrayExpression::try_from(argument)
                .unwrap()
                .into_inner()
            {
                ArrayExpressionInner::Value(v) =>
                    UExpression::value(
                        v.into_iter()
                            .map(|v| match v {
                                TypedExpressionOrSpread::Expression(
                                    TypedExpression::Boolean(
                                        BooleanExpression::Value(v),
                                    ),
                                ) => v,
                                _ => unreachable!("Should be a constant boolean expression. Spreads are not expected here, as in their presence the argument isn't constant"),
                            })
                            .enumerate()
                            .fold(0, |acc, (i, v)| {
                                if v.value {
                                    acc + 2u128.pow(
                                        (bitwidth.to_usize() - i - 1)
                                            .try_into()
                                            .unwrap(),
                                    )
                                } else {
                                    acc
                                }
                            }),
                    )
                        .annotate(bitwidth)
                        .into(),
                _ => unreachable!("should be an array value"),
            }
                }

                fn process_u_to_bits<'ast, T: Field>(
                    arguments: &[TypedExpression<'ast, T>],
                    bitwidth: UBitwidth,
                ) -> TypedExpression<'ast, T> {
                    assert_eq!(arguments.len(), 1);

                    match UExpression::try_from(arguments[0].clone())
                        .unwrap()
                        .into_inner()
                    {
                        UExpressionInner::Value(v) => {
                            let mut num = v.value;
                            let mut res = vec![];

                            for i in (0..bitwidth as u32).rev() {
                                if 2u128.pow(i) <= num {
                                    num -= 2u128.pow(i);
                                    res.push(true);
                                } else {
                                    res.push(false);
                                }
                            }
                            assert_eq!(num, 0);

                            ArrayExpression::value(
                                res.into_iter()
                                    .map(|v| BooleanExpression::value(v).into())
                                    .collect::<Vec<_>>(),
                            )
                            .annotate(ArrayType::new(Type::Boolean, bitwidth.to_usize() as u32))
                            .into()
                        }
                        _ => unreachable!("should be a uint value"),
                    }
                }

                match embed_call.arguments.iter().all(|a| a.is_constant()) {
                    true => {
                        let r: Option<TypedExpression<'ast, T>> = match embed_call.embed {
                            FlatEmbed::BitArrayLe => Ok(None), // todo
                            FlatEmbed::FieldToBoolUnsafe => {
                                match FieldElementExpression::try_from_typed(
                                    embed_call.arguments[0].clone(),
                                ) {
                                    Ok(FieldElementExpression::Value(n))
                                        if n.value == T::from(0) =>
                                    {
                                        Ok(Some(BooleanExpression::value(false).span(span).into()))
                                    }
                                    Ok(FieldElementExpression::Value(n))
                                        if n.value == T::from(1) =>
                                    {
                                        Ok(Some(BooleanExpression::value(true).span(span).into()))
                                    }
                                    Ok(FieldElementExpression::Value(n)) => {
                                        Err(Error::InvalidValue(format!(
                                            "Cannot call `{}` with value `{}`: should be 0 or 1",
                                            embed_call.embed.id(),
                                            n
                                        )))
                                    }
                                    _ => Ok(None),
                                }
                            }
                            FlatEmbed::U64FromBits => Ok(Some(process_u_from_bits(
                                &embed_call.arguments,
                                UBitwidth::B64,
                            ))),
                            FlatEmbed::U32FromBits => Ok(Some(process_u_from_bits(
                                &embed_call.arguments,
                                UBitwidth::B32,
                            ))),
                            FlatEmbed::U16FromBits => Ok(Some(process_u_from_bits(
                                &embed_call.arguments,
                                UBitwidth::B16,
                            ))),
                            FlatEmbed::U8FromBits => Ok(Some(process_u_from_bits(
                                &embed_call.arguments,
                                UBitwidth::B8,
                            ))),
                            FlatEmbed::U64ToBits => Ok(Some(process_u_to_bits(
                                &embed_call.arguments,
                                UBitwidth::B64,
                            ))),
                            FlatEmbed::U32ToBits => Ok(Some(process_u_to_bits(
                                &embed_call.arguments,
                                UBitwidth::B32,
                            ))),
                            FlatEmbed::U16ToBits => Ok(Some(process_u_to_bits(
                                &embed_call.arguments,
                                UBitwidth::B16,
                            ))),
                            FlatEmbed::U8ToBits => Ok(Some(process_u_to_bits(
                                &embed_call.arguments,
                                UBitwidth::B8,
                            ))),
                            FlatEmbed::Unpack => {
                                assert_eq!(embed_call.arguments.len(), 1);
                                assert_eq!(embed_call.generics.len(), 1);

                                let bit_width = embed_call.generics[0];

                                match FieldElementExpression::<T>::try_from(
                                    embed_call.arguments[0].clone(),
                                )
                                .unwrap()
                                {
                                    FieldElementExpression::Value(num) => {
                                        let mut acc = num.value;
                                        let mut res = vec![];

                                        for i in (0..bit_width as usize).rev() {
                                            if T::from(2).pow(i) <= acc {
                                                acc = acc - T::from(2).pow(i);
                                                res.push(true);
                                            } else {
                                                res.push(false);
                                            }
                                        }

                                        if acc != T::zero() {
                                            Err(Error::InvalidValue(format!(
                                                "Cannot unpack `{}` to `{}`: value is too large",
                                                num,
                                                assignee.get_type()
                                            )))
                                        } else {
                                            Ok(Some(
                                                ArrayExpression::value(
                                                    res.into_iter()
                                                        .map(|v| {
                                                            BooleanExpression::value(v)
                                                                .span(span)
                                                                .into()
                                                        })
                                                        .collect::<Vec<_>>(),
                                                )
                                                .annotate(ArrayType::new(Type::Boolean, bit_width))
                                                .span(span)
                                                .into(),
                                            ))
                                        }
                                    }
                                    _ => unreachable!("should be a field value"),
                                }
                            }
                            #[cfg(feature = "bellman")]
                            FlatEmbed::Sha256Round => Ok(None),
                            #[cfg(feature = "ark")]
                            FlatEmbed::SnarkVerifyBls12377 => Ok(None),
                        }?;

                        Ok(match r {
                            // if the function call returns a constant
                            Some(expr) => match assignee {
                                TypedAssignee::Identifier(var) => {
                                    self.constants.insert(var.id, expr);
                                    vec![]
                                }
                                assignee => match self.try_get_constant_mut(&assignee) {
                                    Ok((_, c)) => {
                                        *c = expr;
                                        vec![]
                                    }
                                    Err(v) => match self.constants.remove(&v.id) {
                                        Some(c) => vec![
                                            TypedStatement::definition(v.clone().into(), c),
                                            TypedStatement::definition(assignee, expr),
                                        ],
                                        None => {
                                            vec![TypedStatement::definition(assignee, expr)]
                                        }
                                    },
                                },
                            },
                            None => {
                                // if the function call does not return a constant, invalidate the cache
                                // this happens because we only propagate certain calls here

                                let v = self
                                    .try_get_constant_mut(&assignee)
                                    .map(|(v, _)| v)
                                    .unwrap_or_else(|v| v);

                                match self.constants.remove(&v.id) {
                                    Some(c) => vec![
                                        TypedStatement::definition(v.clone().into(), c),
                                        TypedStatement::embed_call_definition(assignee, embed_call),
                                    ],
                                    None => vec![TypedStatement::embed_call_definition(
                                        assignee, embed_call,
                                    )],
                                }
                            }
                        })
                    }
                    false => {
                        // if the function arguments are not constant, invalidate the cache
                        // for the return assignees
                        let def =
                            TypedStatement::embed_call_definition(assignee.clone(), embed_call);

                        let v = self
                            .try_get_constant_mut(&assignee)
                            .map(|(v, _)| v)
                            .unwrap_or_else(|v| v);

                        Ok(match self.constants.remove(&v.id) {
                            Some(c) => {
                                vec![TypedStatement::definition(v.clone().into(), c), def]
                            }
                            None => vec![def],
                        })
                    }
                }
            }
        }
    }

    fn fold_assembly_block(
        &mut self,
        s: AssemblyBlockStatement<'ast, T>,
    ) -> Result<Vec<TypedStatement<'ast, T>>, Self::Error> {
        Ok(fold_assembly_block(self, s)?
            .into_iter()
            .filter(|s| match s {
                TypedStatement::Assembly(s) => !s.inner.is_empty(),
                _ => true,
            })
            .collect())
    }

    fn fold_for_statement(
        &mut self,
        s: ForStatement<'ast, T>,
    ) -> Result<Vec<TypedStatement<'ast, T>>, Self::Error> {
        // we do not visit the for-loop statements
        let from = self.fold_uint_expression(s.from)?;
        let to = self.fold_uint_expression(s.to)?;

        Ok(vec![TypedStatement::for_(s.var, from, to, s.statements)])
    }

    fn fold_assertion_statement(
        &mut self,
        s: AssertionStatement<'ast, T>,
    ) -> Result<Vec<TypedStatement<'ast, T>>, Self::Error> {
        let _e_str = s.expression.to_string();
        let expr = self.fold_boolean_expression(s.expression)?;

        match expr {
            BooleanExpression::Value(v) if !v.value => Err(Error::AssertionFailed(s.error)),
            BooleanExpression::Value(v) if v.value => Ok(vec![]),
            _ => Ok(vec![TypedStatement::assertion(expr, s.error)]),
        }
    }

    fn fold_uint_expression_cases(
        &mut self,
        bitwidth: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> Result<UExpressionInner<'ast, T>, Error> {
        match e {
            UExpressionInner::Add(e) => match (
                self.fold_uint_expression(*e.left)?.into_inner(),
                self.fold_uint_expression(*e.right)?.into_inner(),
            ) {
                (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                    Ok(UExpression::value(
                        (v1.value + v2.value) % 2_u128.pow(bitwidth.to_usize().try_into().unwrap()),
                    ))
                }
                (e, UExpressionInner::Value(v)) | (UExpressionInner::Value(v), e) => {
                    match v.value {
                        0 => Ok(e),
                        _ => Ok(UExpression::add(
                            e.annotate(bitwidth),
                            UExpression::value(v.value).annotate(bitwidth),
                        )
                        .into_inner()),
                    }
                }
                (e1, e2) => {
                    Ok(UExpression::add(e1.annotate(bitwidth), e2.annotate(bitwidth)).into_inner())
                }
            },
            UExpressionInner::Sub(e) => match (
                self.fold_uint_expression(*e.left)?.into_inner(),
                self.fold_uint_expression(*e.right)?.into_inner(),
            ) {
                (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                    Ok(UExpression::value(
                        (v1.value.wrapping_sub(v2.value))
                            % 2_u128.pow(bitwidth.to_usize().try_into().unwrap()),
                    ))
                }
                (e, UExpressionInner::Value(v)) => match v.value {
                    0 => Ok(e),
                    _ => Ok(UExpression::sub(
                        e.annotate(bitwidth),
                        UExpressionInner::Value(v).annotate(bitwidth),
                    )
                    .into_inner()),
                },
                (e1, e2) => {
                    Ok(UExpression::sub(e1.annotate(bitwidth), e2.annotate(bitwidth)).into_inner())
                }
            },
            UExpressionInner::FloorSub(e) => match (
                self.fold_uint_expression(*e.left)?.into_inner(),
                self.fold_uint_expression(*e.right)?.into_inner(),
            ) {
                (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                    Ok(UExpression::value(
                        v1.value.saturating_sub(v2.value)
                            % 2_u128.pow(bitwidth.to_usize().try_into().unwrap()),
                    ))
                }
                (e, UExpressionInner::Value(v)) => match v.value {
                    0 => Ok(e),
                    _ => Ok(UExpression::floor_sub(
                        e.annotate(bitwidth),
                        UExpressionInner::Value(v).annotate(bitwidth),
                    )
                    .into_inner()),
                },
                (e1, e2) => {
                    Ok(UExpression::sub(e1.annotate(bitwidth), e2.annotate(bitwidth)).into_inner())
                }
            },
            UExpressionInner::Mult(e) => match (
                self.fold_uint_expression(*e.left)?.into_inner(),
                self.fold_uint_expression(*e.right)?.into_inner(),
            ) {
                (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                    Ok(UExpression::value(
                        (v1.value * v2.value) % 2_u128.pow(bitwidth.to_usize().try_into().unwrap()),
                    ))
                }
                (e, UExpressionInner::Value(v)) | (UExpressionInner::Value(v), e) => {
                    match v.value {
                        0 => Ok(UExpression::value(0)),
                        1 => Ok(e),
                        _ => Ok(UExpression::mul(
                            e.annotate(bitwidth),
                            UExpressionInner::Value(v).annotate(bitwidth),
                        )
                        .into_inner()),
                    }
                }
                (e1, e2) => {
                    Ok(UExpression::mul(e1.annotate(bitwidth), e2.annotate(bitwidth)).into_inner())
                }
            },
            UExpressionInner::Div(e) => match (
                self.fold_uint_expression(*e.left)?.into_inner(),
                self.fold_uint_expression(*e.right)?.into_inner(),
            ) {
                (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                    Ok(UExpression::value(
                        (v1.value / v2.value) % 2_u128.pow(bitwidth.to_usize().try_into().unwrap()),
                    ))
                }
                (e, UExpressionInner::Value(v)) => match v.value {
                    1 => Ok(e),
                    _ => Ok(UExpression::div(
                        e.annotate(bitwidth),
                        UExpressionInner::Value(v).annotate(bitwidth),
                    )
                    .into_inner()),
                },
                (e1, e2) => {
                    Ok(UExpression::div(e1.annotate(bitwidth), e2.annotate(bitwidth)).into_inner())
                }
            },
            UExpressionInner::Rem(e) => match (
                self.fold_uint_expression(*e.left)?.into_inner(),
                self.fold_uint_expression(*e.right)?.into_inner(),
            ) {
                (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                    Ok(UExpression::value(
                        (v1.value % v2.value) % 2_u128.pow(bitwidth.to_usize().try_into().unwrap()),
                    ))
                }
                (e, UExpressionInner::Value(v)) => match v.value {
                    1 => Ok(UExpression::value(0)),
                    _ => Ok(UExpression::rem(
                        e.annotate(bitwidth),
                        UExpressionInner::Value(v).annotate(bitwidth),
                    )
                    .into_inner()),
                },
                (e1, e2) => {
                    Ok(UExpression::rem(e1.annotate(bitwidth), e2.annotate(bitwidth)).into_inner())
                }
            },
            UExpressionInner::RightShift(e) => {
                let left = self.fold_uint_expression(*e.left)?;
                let right = self.fold_uint_expression(*e.right)?;
                match (left.into_inner(), right.into_inner()) {
                    (UExpressionInner::Value(v), UExpressionInner::Value(by)) => {
                        Ok(UExpression::value(v.value >> by.value))
                    }
                    (e, by) => Ok(UExpression::right_shift(
                        e.annotate(bitwidth),
                        by.annotate(UBitwidth::B32),
                    )
                    .into_inner()),
                }
            }
            UExpressionInner::LeftShift(e) => {
                let left = self.fold_uint_expression(*e.left)?;
                let right = self.fold_uint_expression(*e.right)?;
                match (left.into_inner(), right.into_inner()) {
                    (UExpressionInner::Value(v), UExpressionInner::Value(by)) => {
                        Ok(UExpression::value(
                            (v.value << by.value) & (2_u128.pow(bitwidth as u32) - 1),
                        ))
                    }
                    (e, by) => Ok(UExpression::left_shift(
                        e.annotate(bitwidth),
                        by.annotate(UBitwidth::B32),
                    )
                    .into_inner()),
                }
            }
            UExpressionInner::Xor(e) => match (
                self.fold_uint_expression(*e.left)?.into_inner(),
                self.fold_uint_expression(*e.right)?.into_inner(),
            ) {
                (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                    Ok(UExpression::value(v1.value ^ v2.value))
                }
                (UExpressionInner::Value(v), e2) | (e2, UExpressionInner::Value(v))
                    if v.value == 0 =>
                {
                    Ok(e2)
                }
                (e1, e2) => {
                    if e1 == e2 {
                        Ok(UExpression::value(0))
                    } else {
                        Ok(
                            UExpression::xor(e1.annotate(bitwidth), e2.annotate(bitwidth))
                                .into_inner(),
                        )
                    }
                }
            },
            UExpressionInner::And(e) => match (
                self.fold_uint_expression(*e.left)?.into_inner(),
                self.fold_uint_expression(*e.right)?.into_inner(),
            ) {
                (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                    Ok(UExpression::value(v1.value & v2.value))
                }
                (UExpressionInner::Value(v), _) | (_, UExpressionInner::Value(v))
                    if v.value == 0 =>
                {
                    Ok(UExpression::value(0))
                }
                (e1, e2) => {
                    Ok(UExpression::and(e1.annotate(bitwidth), e2.annotate(bitwidth)).into_inner())
                }
            },
            UExpressionInner::Not(e) => {
                let e = self.fold_uint_expression(*e.inner)?.into_inner();
                match e {
                    UExpressionInner::Value(v) => Ok(UExpression::value(
                        (!v.value) & (2_u128.pow(bitwidth as u32) - 1),
                    )),
                    e => Ok(UExpression::not(e.annotate(bitwidth)).into_inner()),
                }
            }
            UExpressionInner::Neg(e) => {
                let e = self.fold_uint_expression(*e.inner)?.into_inner();
                match e {
                    UExpressionInner::Value(v) => Ok(UExpression::value(
                        (0u128.wrapping_sub(v.value))
                            % 2_u128.pow(bitwidth.to_usize().try_into().unwrap()),
                    )),
                    e => Ok(UExpression::neg(e.annotate(bitwidth)).into_inner()),
                }
            }
            UExpressionInner::Pos(e) => {
                let e = self.fold_uint_expression(*e.inner)?.into_inner();
                match e {
                    UExpressionInner::Value(v) => Ok(UExpression::value(v.value)),
                    e => Ok(UExpression::pos(e.annotate(bitwidth)).into_inner()),
                }
            }
            e => fold_uint_expression_cases(self, bitwidth, e),
        }
    }

    fn fold_field_expression_cases(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> Result<FieldElementExpression<'ast, T>, Error> {
        match e {
            FieldElementExpression::Add(e) => {
                let left = self.fold_field_expression(*e.left)?;
                let right = self.fold_field_expression(*e.right)?;

                Ok(match (left, right) {
                    (FieldElementExpression::Value(n1), FieldElementExpression::Value(n2)) => {
                        FieldElementExpression::Value(ValueExpression::new(n1.value + n2.value))
                    }
                    (e1, e2) => e1 + e2,
                })
            }
            FieldElementExpression::Sub(e) => {
                let left = self.fold_field_expression(*e.left)?;
                let right = self.fold_field_expression(*e.right)?;

                Ok(match (left, right) {
                    (FieldElementExpression::Value(n1), FieldElementExpression::Value(n2)) => {
                        FieldElementExpression::Value(ValueExpression::new(n1.value - n2.value))
                    }
                    (e1, e2) => e1 - e2,
                })
            }
            FieldElementExpression::Mult(e) => {
                let left = self.fold_field_expression(*e.left)?;
                let right = self.fold_field_expression(*e.right)?;

                Ok(match (left, right) {
                    (FieldElementExpression::Value(n1), FieldElementExpression::Value(n2)) => {
                        FieldElementExpression::Value(ValueExpression::new(n1.value * n2.value))
                    }
                    (e1, e2) => e1 * e2,
                })
            }
            FieldElementExpression::Div(e) => {
                let left = self.fold_field_expression(*e.left)?;
                let right = self.fold_field_expression(*e.right)?;

                Ok(match (left, right) {
                    (FieldElementExpression::Value(n1), FieldElementExpression::Value(n2)) => {
                        FieldElementExpression::Value(ValueExpression::new(n1.value / n2.value))
                    }
                    (e1, e2) => e1 / e2,
                })
            }
            FieldElementExpression::Neg(e) => match self.fold_field_expression(*e.inner)? {
                FieldElementExpression::Value(n) => {
                    Ok(FieldElementExpression::value(T::zero() - n.value))
                }
                e => Ok(FieldElementExpression::neg(e)),
            },
            FieldElementExpression::Pos(e) => match self.fold_field_expression(*e.inner)? {
                FieldElementExpression::Value(n) => Ok(FieldElementExpression::Value(n)),
                e => Ok(FieldElementExpression::pos(e)),
            },
            FieldElementExpression::Pow(e) => {
                let e1 = self.fold_field_expression(*e.left)?;
                let e2 = self.fold_uint_expression(*e.right)?;
                match (e1, e2.into_inner()) {
                    (_, UExpressionInner::Value(ref n2)) if n2.value == 0 => {
                        Ok(FieldElementExpression::value(T::from(1)))
                    }
                    (FieldElementExpression::Value(n1), UExpressionInner::Value(n2)) => Ok(
                        FieldElementExpression::value(n1.value.pow(n2.value as usize)),
                    ),
                    (e1, e2) => Ok(FieldElementExpression::pow(e1, e2.annotate(UBitwidth::B32))),
                }
            }
            FieldElementExpression::Xor(e) => {
                let e1 = self.fold_field_expression(*e.left)?;
                let e2 = self.fold_field_expression(*e.right)?;

                match (e1, e2) {
                    (FieldElementExpression::Value(n1), FieldElementExpression::Value(n2)) => {
                        Ok(FieldElementExpression::value(
                            T::try_from(n1.value.to_biguint().bitxor(n2.value.to_biguint()))
                                .unwrap(),
                        ))
                    }
                    (FieldElementExpression::Value(n), e)
                    | (e, FieldElementExpression::Value(n))
                        if n.value == T::from(0) =>
                    {
                        Ok(e)
                    }
                    (e1, e2) if e1.eq(&e2) => Ok(FieldElementExpression::value(T::from(0))),
                    (e1, e2) => Ok(FieldElementExpression::bitxor(e1, e2)),
                }
            }
            FieldElementExpression::And(e) => {
                let e1 = self.fold_field_expression(*e.left)?;
                let e2 = self.fold_field_expression(*e.right)?;

                match (e1, e2) {
                    (_, FieldElementExpression::Value(n))
                    | (FieldElementExpression::Value(n), _)
                        if n.value == T::from(0) =>
                    {
                        Ok(FieldElementExpression::Value(n))
                    }
                    (FieldElementExpression::Value(n1), FieldElementExpression::Value(n2)) => {
                        Ok(FieldElementExpression::value(
                            T::try_from(n1.value.to_biguint().bitand(n2.value.to_biguint()))
                                .unwrap(),
                        ))
                    }
                    (e1, e2) => Ok(FieldElementExpression::bitand(e1, e2)),
                }
            }
            FieldElementExpression::Or(e) => {
                let e1 = self.fold_field_expression(*e.left)?;
                let e2 = self.fold_field_expression(*e.right)?;

                match (e1, e2) {
                    (e, FieldElementExpression::Value(n))
                    | (FieldElementExpression::Value(n), e)
                        if n.value == T::from(0) =>
                    {
                        Ok(e)
                    }
                    (FieldElementExpression::Value(n1), FieldElementExpression::Value(n2)) => {
                        Ok(FieldElementExpression::value(
                            T::try_from(n1.value.to_biguint().bitor(n2.value.to_biguint()))
                                .unwrap(),
                        ))
                    }
                    (e1, e2) => Ok(FieldElementExpression::bitor(e1, e2)),
                }
            }
            FieldElementExpression::LeftShift(e) => {
                let expr = self.fold_field_expression(*e.left)?;
                let by = self.fold_uint_expression(*e.right)?;
                match (expr, by) {
                    (
                        e,
                        UExpression {
                            inner: UExpressionInner::Value(by),
                            ..
                        },
                    ) if by.value == 0 => Ok(e),
                    (
                        _,
                        UExpression {
                            inner: UExpressionInner::Value(by),
                            ..
                        },
                    ) if by.value as usize >= T::get_required_bits() => {
                        Ok(FieldElementExpression::value(T::from(0)))
                    }
                    (
                        FieldElementExpression::Value(n),
                        UExpression {
                            inner: UExpressionInner::Value(by),
                            ..
                        },
                    ) => {
                        let two = BigUint::from(2usize);
                        let mask: BigUint = two.pow(T::get_required_bits()).sub(1usize);

                        Ok(FieldElementExpression::value(
                            T::try_from(n.value.to_biguint().shl(by.value as usize).bitand(mask))
                                .unwrap(),
                        ))
                    }
                    (e, by) => Ok(FieldElementExpression::left_shift(e, by)),
                }
            }
            FieldElementExpression::RightShift(e) => {
                let expr = self.fold_field_expression(*e.left)?;
                let by = self.fold_uint_expression(*e.right)?;
                match (expr, by) {
                    (
                        e,
                        UExpression {
                            inner: UExpressionInner::Value(by),
                            ..
                        },
                    ) if by.value == 0 => Ok(e),
                    (
                        _,
                        UExpression {
                            inner: UExpressionInner::Value(by),
                            ..
                        },
                    ) if by.value as usize >= T::get_required_bits() => {
                        Ok(FieldElementExpression::value(T::from(0)))
                    }
                    (
                        FieldElementExpression::Value(n),
                        UExpression {
                            inner: UExpressionInner::Value(by),
                            ..
                        },
                    ) => Ok(FieldElementExpression::value(
                        T::try_from(n.value.to_biguint().shr(by.value as usize)).unwrap(),
                    )),
                    (e, by) => Ok(FieldElementExpression::right_shift(e, by)),
                }
            }
            e => fold_field_expression_cases(self, e),
        }
    }

    fn fold_member_expression<
        E: Expr<'ast, T> + Member<'ast, T> + From<TypedExpression<'ast, T>>,
    >(
        &mut self,
        _: &E::Ty,
        m: MemberExpression<'ast, T, E>,
    ) -> Result<MemberOrExpression<'ast, T, E>, Self::Error> {
        let id = m.id;

        let struc = self.fold_struct_expression(*m.struc)?;

        let ty = struc.ty().clone();

        match struc.into_inner() {
            StructExpressionInner::Value(v) => Ok(MemberOrExpression::Expression(
                E::from(
                    ty.members
                        .iter()
                        .zip(v)
                        .find(|(member, _)| member.id == id)
                        .unwrap()
                        .1,
                )
                .into_inner(),
            )),
            inner => Ok(MemberOrExpression::Member(MemberExpression::new(
                inner.annotate(ty),
                id,
            ))),
        }
    }

    fn fold_element_expression<
        E: Expr<'ast, T> + Element<'ast, T> + From<TypedExpression<'ast, T>>,
    >(
        &mut self,
        _: &E::Ty,
        m: ElementExpression<'ast, T, E>,
    ) -> Result<ElementOrExpression<'ast, T, E>, Self::Error> {
        let index = m.index;

        let tuple = self.fold_tuple_expression(*m.tuple)?;

        let ty = tuple.ty().clone();

        match tuple.into_inner() {
            TupleExpressionInner::Value(v) => Ok(ElementOrExpression::Expression(
                E::from(v[index as usize].clone()).into_inner(),
            )),
            inner => Ok(ElementOrExpression::Element(ElementExpression::new(
                inner.annotate(ty),
                index,
            ))),
        }
    }

    fn fold_select_expression<
        E: Expr<'ast, T>
            + Select<'ast, T>
            + From<TypedExpression<'ast, T>>
            + Into<TypedExpression<'ast, T>>,
    >(
        &mut self,
        _: &E::Ty,
        e: SelectExpression<'ast, T, E>,
    ) -> Result<SelectOrExpression<'ast, T, E>, Self::Error> {
        let index = self.fold_uint_expression(*e.index)?;
        let array = *e.array;

        let ty = self.fold_array_type(*array.ty)?;
        let size = match ty.size.as_inner() {
            UExpressionInner::Value(v) => Ok(v),
            _ => unreachable!("array size was checked when folding array type"),
        }?;

        match (array.inner, index.into_inner()) {
            // special case if the array is an identifier: check the cache and only clone the element, not the whole array
            (ArrayExpressionInner::Identifier(id), UExpressionInner::Value(n)) => {
                match self.constants.get(&id.id) {
                    Some(v) => {
                        // get the constant array. it was guaranteed to be a value when it was inserted
                        let v = match v {
                            TypedExpression::Array(a) => match a.as_inner() {
                                ArrayExpressionInner::Value(v) => v,
                                _ => unreachable!(),
                            },
                            _ => unreachable!(),
                        };

                        // sanity check that the value does not contain spreads
                        assert!(v
                            .value
                            .iter()
                            .all(|e| matches!(e, TypedExpressionOrSpread::Expression(_))));

                        if n.value < size.value {
                            Ok(SelectOrExpression::Expression(
                                // clone only the element
                                match v.value[n.value as usize].clone() {
                                    TypedExpressionOrSpread::Expression(e) => {
                                        E::try_from(e).unwrap().into_inner()
                                    }
                                    _ => unreachable!(),
                                },
                            ))
                        } else {
                            Err(Error::OutOfBounds(n.value, size.value))
                        }
                    }
                    _ => Ok(SelectOrExpression::Select(SelectExpression::new(
                        ArrayExpressionInner::Identifier(id).annotate(ty),
                        UExpressionInner::Value(n).annotate(UBitwidth::B32),
                    ))),
                }
            }
            (array, index) => {
                let array = self.fold_array_expression_inner(&ty, array)?;

                match (array, index) {
                    (ArrayExpressionInner::Value(v), UExpressionInner::Value(n)) => {
                        if n.value < size.value {
                            Ok(SelectOrExpression::Expression(
                                v.expression_at::<E>(n.value as usize).into_inner(),
                            ))
                        } else {
                            Err(Error::OutOfBounds(n.value, size.value))
                        }
                    }
                    (a, i) => Ok(SelectOrExpression::Select(SelectExpression::new(
                        a.annotate(ty),
                        i.annotate(UBitwidth::B32),
                    ))),
                }
            }
        }
    }

    fn fold_array_type(
        &mut self,
        t: ArrayType<'ast, T>,
    ) -> Result<ArrayType<'ast, T>, Self::Error> {
        let size = self.fold_uint_expression(*t.size)?;

        if !size.is_constant() {
            return Err(Error::VariableLength(format!(
                "Array length should be fixed, found {}",
                size
            )));
        }

        Ok(ArrayType::new(self.fold_type(*t.ty)?, size))
    }

    fn fold_array_expression_cases(
        &mut self,
        ty: &ArrayType<'ast, T>,
        e: ArrayExpressionInner<'ast, T>,
    ) -> Result<ArrayExpressionInner<'ast, T>, Error> {
        match e {
            ArrayExpressionInner::Value(exprs) => {
                Ok(ArrayExpressionInner::Value(
                    exprs
                        .into_iter()
                        .map(|e| self.fold_expression_or_spread(e))
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .flat_map(|e| {
                            match e {
                                // simplify `...[a, b]` to `a, b`
                                TypedExpressionOrSpread::Spread(TypedSpread {
                                    array:
                                        ArrayExpression {
                                            inner: ArrayExpressionInner::Value(v),
                                            ..
                                        },
                                }) => v.value,
                                e => vec![e],
                            }
                        })
                        // ignore spreads over empty arrays
                        .filter_map(|e| match e {
                            // clippy makes a wrong suggestion here:
                            // ```
                            // this creates an owned instance just for comparison
                            // UExpression::from(0u32)
                            // help: try: `0u32`
                            // ```
                            // But for `UExpression`, `PartialEq<Self>` is different from `PartialEq<u32>` (the latter is too optimistic in this case)
                            #[allow(clippy::cmp_owned)]
                            TypedExpressionOrSpread::Spread(s)
                                if s.array.size() == UExpression::from(0u32) =>
                            {
                                None
                            }
                            e => Some(e),
                        })
                        .collect(),
                ))
            }
            e => fold_array_expression_cases(self, ty, e),
        }
    }

    fn fold_struct_expression_cases(
        &mut self,
        ty: &StructType<'ast, T>,
        e: StructExpressionInner<'ast, T>,
    ) -> Result<StructExpressionInner<'ast, T>, Error> {
        match e {
            StructExpressionInner::Value(v) => {
                let v = v.into_iter().zip(ty.iter()).map(|(v, member)|
                    match self.fold_expression(v) {
                        Ok(v) => match (ConcreteType::try_from(v.get_type().clone()), ConcreteType::try_from(*member.ty.clone())) {
                            (Ok(t1), Ok(t2)) => if t1 == t2 { Ok(v) } else { Err(Error::Type(format!(
                                "Struct member `{}` in struct `{}/{}` expected to have type `{}`, found type `{}`",
                                member.id, ty.canonical_location.clone().module.display(), ty.canonical_location.clone().name, t2, t1
                            ))) },
                            _ => Ok(v)
                        }
                        e => e
                    }
                ).collect::<Result<_, _>>()?;

                Ok(StructExpressionInner::Value(v))
            }
            e => fold_struct_expression_cases(self, ty, e),
        }
    }

    fn fold_identifier_expression<
        E: Expr<'ast, T> + Id<'ast, T> + ResultFold<Self, Self::Error>,
    >(
        &mut self,
        _: &E::Ty,
        id: IdentifierExpression<'ast, E>,
    ) -> Result<IdentifierOrExpression<'ast, T, E>, Self::Error> {
        match self.constants.get(&id.id).cloned() {
            Some(e) => Ok(IdentifierOrExpression::Expression(E::from(e).into_inner())),
            None => Ok(IdentifierOrExpression::Identifier(id)),
        }
    }

    fn fold_tuple_expression_cases(
        &mut self,
        ty: &TupleType<'ast, T>,
        e: TupleExpressionInner<'ast, T>,
    ) -> Result<TupleExpressionInner<'ast, T>, Error> {
        match e {
            TupleExpressionInner::Value(v) => {
                let v = v.into_iter().zip(ty.elements.iter().enumerate()).map(|(v, (index, element_ty))|
                    match self.fold_expression(v) {
                        Ok(v) => match (ConcreteType::try_from(v.get_type().clone()), ConcreteType::try_from(element_ty.clone())) {
                            (Ok(t1), Ok(t2)) => if t1 == t2 { Ok(v) } else { Err(Error::Type(format!(
                                "Tuple element `{}` in tuple `{}` expected to have type `{}`, found type `{}`",
                                index, ty, t2, t1
                            ))) },
                            _ => Ok(v)
                        }
                        e => e
                    }
                ).collect::<Result<_, _>>()?;

                Ok(TupleExpressionInner::Value(v))
            }
            e => fold_tuple_expression_cases(self, ty, e),
        }
    }

    fn fold_eq_expression<
        E: Expr<'ast, T> + PartialEq + Constant + Typed<'ast, T> + ResultFold<Self, Self::Error>,
    >(
        &mut self,
        e: EqExpression<E, BooleanExpression<'ast, T>>,
    ) -> Result<
        BinaryOrExpression<OpEq, E, E, BooleanExpression<'ast, T>, BooleanExpression<'ast, T>>,
        Self::Error,
    > {
        let left = e.left.fold(self)?;
        let right = e.right.fold(self)?;

        if let (Ok(t_left), Ok(t_right)) = (
            ConcreteType::try_from(left.get_type()),
            ConcreteType::try_from(right.get_type()),
        ) {
            if t_left != t_right {
                return Err(Error::Type(format!(
                    "Cannot compare {} of type {} to {} of type {}",
                    left, t_left, right, t_right
                )));
            }
        };

        // if the two expressions are the same, we can reduce to `true`.
        // Note that if they are different we cannot reduce to `false`: `a == 1` may still be `true` even though `a` and `1` are different expressions
        if left == right {
            return Ok(BinaryOrExpression::Expression(BooleanExpression::value(
                true,
            )));
        }

        // if both expressions are constant, we can reduce the equality check after we put them in canonical form
        if left.is_constant() && right.is_constant() {
            let left = left.into_canonical_constant();
            let right = right.into_canonical_constant();
            Ok(BinaryOrExpression::Expression(BooleanExpression::value(
                left == right,
            )))
        } else {
            Ok(BinaryOrExpression::Binary(BinaryExpression::new(
                left, right,
            )))
        }
    }

    fn fold_boolean_expression_cases(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> Result<BooleanExpression<'ast, T>, Error> {
        // Note: we only propagate when we see constants, as comparing of arbitrary expressions would lead to
        // a lot of false negatives due to expressions not being in a canonical form
        // For example, `2 * a` is equivalent to `a + a`, but our notion of equality would not detect that here
        // These kind of reduction rules are easier to apply later in the process, when we have canonical representations
        // of expressions, ie `a + a` would always be written `2 * a`
        match e {
            BooleanExpression::FieldLt(e) => {
                let e1 = self.fold_field_expression(*e.left)?;
                let e2 = self.fold_field_expression(*e.right)?;

                match (e1, e2) {
                    (FieldElementExpression::Value(n1), FieldElementExpression::Value(n2)) => {
                        Ok(BooleanExpression::value(n1.value < n2.value))
                    }
                    (e1, e2) => Ok(BooleanExpression::field_lt(e1, e2)),
                }
            }
            BooleanExpression::FieldLe(e) => {
                let e1 = self.fold_field_expression(*e.left)?;
                let e2 = self.fold_field_expression(*e.right)?;

                match (e1, e2) {
                    (FieldElementExpression::Value(n1), FieldElementExpression::Value(n2)) => {
                        Ok(BooleanExpression::value(n1.value <= n2.value))
                    }
                    (e1, e2) => Ok(BooleanExpression::field_le(e1, e2)),
                }
            }
            BooleanExpression::UintLt(e) => {
                let e1 = self.fold_uint_expression(*e.left)?;
                let e2 = self.fold_uint_expression(*e.right)?;

                match (e1.as_inner(), e2.as_inner()) {
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        Ok(BooleanExpression::value(n1.value < n2.value))
                    }
                    _ => Ok(BooleanExpression::uint_lt(e1, e2)),
                }
            }
            BooleanExpression::UintLe(e) => {
                let e1 = self.fold_uint_expression(*e.left)?;
                let e2 = self.fold_uint_expression(*e.right)?;

                match (e1.as_inner(), e2.as_inner()) {
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        Ok(BooleanExpression::value(n1.value <= n2.value))
                    }
                    _ => Ok(BooleanExpression::uint_le(e1, e2)),
                }
            }
            BooleanExpression::Or(e) => {
                let e1 = self.fold_boolean_expression(*e.left)?;
                let e2 = self.fold_boolean_expression(*e.right)?;

                match (e1, e2) {
                    // reduction of constants
                    (BooleanExpression::Value(v1), BooleanExpression::Value(v2)) => {
                        Ok(BooleanExpression::value(v1.value || v2.value))
                    }
                    // x || true == true
                    (_, BooleanExpression::Value(v)) | (BooleanExpression::Value(v), _)
                        if v.value =>
                    {
                        Ok(BooleanExpression::value(true))
                    }
                    // x || false == x
                    (e, BooleanExpression::Value(v)) | (BooleanExpression::Value(v), e)
                        if !v.value =>
                    {
                        Ok(e)
                    }
                    (e1, e2) => Ok(BooleanExpression::bitor(e1, e2)),
                }
            }
            BooleanExpression::And(e) => {
                let e1 = self.fold_boolean_expression(*e.left)?;
                let e2 = self.fold_boolean_expression(*e.right)?;

                match (e1, e2) {
                    // reduction of constants
                    (BooleanExpression::Value(v1), BooleanExpression::Value(v2)) => {
                        Ok(BooleanExpression::value(v1.value && v2.value))
                    }
                    // x && true == x
                    (e, BooleanExpression::Value(v)) | (BooleanExpression::Value(v), e)
                        if v.value =>
                    {
                        Ok(e)
                    }
                    // x && false == false
                    (_, BooleanExpression::Value(v)) | (BooleanExpression::Value(v), _)
                        if !v.value =>
                    {
                        Ok(BooleanExpression::value(false))
                    }
                    (e1, e2) => Ok(BooleanExpression::bitand(e1, e2)),
                }
            }
            BooleanExpression::Not(e) => {
                let e = self.fold_boolean_expression(*e.inner)?;
                match e {
                    BooleanExpression::Value(v) => Ok(BooleanExpression::value(!v.value)),
                    e => Ok(BooleanExpression::not(e)),
                }
            }
            e => fold_boolean_expression_cases(self, e),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::Bn128Field;

    #[cfg(test)]
    mod expression {
        use super::*;

        #[cfg(test)]
        mod field {
            use super::*;

            #[test]
            fn add() {
                let e = FieldElementExpression::add(
                    FieldElementExpression::value(Bn128Field::from(2)),
                    FieldElementExpression::value(Bn128Field::from(3)),
                );

                assert_eq!(
                    Propagator::default().fold_field_expression(e),
                    Ok(FieldElementExpression::value(Bn128Field::from(5)))
                );
            }

            #[test]
            fn sub() {
                let e = FieldElementExpression::sub(
                    FieldElementExpression::value(Bn128Field::from(3)),
                    FieldElementExpression::value(Bn128Field::from(2)),
                );

                assert_eq!(
                    Propagator::default().fold_field_expression(e),
                    Ok(FieldElementExpression::value(Bn128Field::from(1)))
                );
            }

            #[test]
            fn mult() {
                let e = FieldElementExpression::mul(
                    FieldElementExpression::value(Bn128Field::from(3)),
                    FieldElementExpression::value(Bn128Field::from(2)),
                );

                assert_eq!(
                    Propagator::default().fold_field_expression(e),
                    Ok(FieldElementExpression::value(Bn128Field::from(6)))
                );
            }

            #[test]
            fn div() {
                let e = FieldElementExpression::div(
                    FieldElementExpression::value(Bn128Field::from(6)),
                    FieldElementExpression::value(Bn128Field::from(2)),
                );

                assert_eq!(
                    Propagator::default().fold_field_expression(e),
                    Ok(FieldElementExpression::value(Bn128Field::from(3)))
                );
            }

            #[test]
            fn pow() {
                let e = FieldElementExpression::pow(
                    FieldElementExpression::value(Bn128Field::from(2)),
                    3u32.into(),
                );

                assert_eq!(
                    Propagator::default().fold_field_expression(e),
                    Ok(FieldElementExpression::value(Bn128Field::from(8)))
                );
            }

            #[test]
            fn left_shift() {
                let mut propagator = Propagator::default();

                assert_eq!(
                    propagator.fold_field_expression(FieldElementExpression::left_shift(
                        FieldElementExpression::identifier("a".into()),
                        0u32.into(),
                    )),
                    Ok(FieldElementExpression::identifier("a".into()))
                );

                assert_eq!(
                    propagator.fold_field_expression(FieldElementExpression::left_shift(
                        FieldElementExpression::value(Bn128Field::from(2)),
                        2u32.into(),
                    )),
                    Ok(FieldElementExpression::value(Bn128Field::from(8)))
                );

                assert_eq!(
                    propagator.fold_field_expression(FieldElementExpression::left_shift(
                        FieldElementExpression::value(Bn128Field::from(1)),
                        ((Bn128Field::get_required_bits() - 1) as u32).into(),
                    )),
                    Ok(FieldElementExpression::value(Bn128Field::try_from_dec_str("14474011154664524427946373126085988481658748083205070504932198000989141204992").unwrap()))
                );

                assert_eq!(
                    propagator.fold_field_expression(FieldElementExpression::left_shift(
                        FieldElementExpression::value(Bn128Field::from(3)),
                        ((Bn128Field::get_required_bits() - 3) as u32).into(),
                    )),
                    Ok(FieldElementExpression::value(Bn128Field::try_from_dec_str("10855508365998393320959779844564491361244061062403802878699148500741855903744").unwrap()))
                );

                assert_eq!(
                    propagator.fold_field_expression(FieldElementExpression::left_shift(
                        FieldElementExpression::value(Bn128Field::from(1)),
                        (Bn128Field::get_required_bits() as u32).into(),
                    )),
                    Ok(FieldElementExpression::value(Bn128Field::from(0)))
                );
            }

            #[test]
            fn right_shift() {
                let mut propagator = Propagator::default();

                assert_eq!(
                    propagator.fold_field_expression(FieldElementExpression::right_shift(
                        FieldElementExpression::identifier("a".into()),
                        0u32.into(),
                    )),
                    Ok(FieldElementExpression::identifier("a".into()))
                );

                assert_eq!(
                    propagator.fold_field_expression(FieldElementExpression::right_shift(
                        FieldElementExpression::identifier("a".into()),
                        (Bn128Field::get_required_bits() as u32).into(),
                    )),
                    Ok(FieldElementExpression::value(Bn128Field::from(0)))
                );

                assert_eq!(
                    propagator.fold_field_expression(FieldElementExpression::right_shift(
                        FieldElementExpression::value(Bn128Field::from(3)),
                        1u32.into(),
                    )),
                    Ok(FieldElementExpression::value(Bn128Field::from(1)))
                );

                assert_eq!(
                    propagator.fold_field_expression(FieldElementExpression::right_shift(
                        FieldElementExpression::value(Bn128Field::from(2)),
                        2u32.into(),
                    )),
                    Ok(FieldElementExpression::value(Bn128Field::from(0)))
                );
                assert_eq!(
                    propagator.fold_field_expression(FieldElementExpression::right_shift(
                        FieldElementExpression::value(Bn128Field::from(2)),
                        4u32.into(),
                    )),
                    Ok(FieldElementExpression::value(Bn128Field::from(0)))
                );

                assert_eq!(
                    propagator.fold_field_expression(FieldElementExpression::right_shift(
                        FieldElementExpression::value(Bn128Field::max_value()),
                        ((Bn128Field::get_required_bits() - 1) as u32).into(),
                    )),
                    Ok(FieldElementExpression::value(Bn128Field::from(1)))
                );

                assert_eq!(
                    propagator.fold_field_expression(FieldElementExpression::right_shift(
                        FieldElementExpression::value(Bn128Field::max_value()),
                        (Bn128Field::get_required_bits() as u32).into(),
                    )),
                    Ok(FieldElementExpression::value(Bn128Field::from(0)))
                );
            }

            #[test]
            fn if_else_true() {
                let e = FieldElementExpression::conditional(
                    BooleanExpression::value(true),
                    FieldElementExpression::value(Bn128Field::from(2)),
                    FieldElementExpression::value(Bn128Field::from(3)),
                    ConditionalKind::IfElse,
                );

                assert_eq!(
                    Propagator::default().fold_field_expression(e),
                    Ok(FieldElementExpression::value(Bn128Field::from(2)))
                );
            }

            #[test]
            fn if_else_false() {
                let e = FieldElementExpression::conditional(
                    BooleanExpression::value(false),
                    FieldElementExpression::value(Bn128Field::from(2)),
                    FieldElementExpression::value(Bn128Field::from(3)),
                    ConditionalKind::IfElse,
                );

                assert_eq!(
                    Propagator::default().fold_field_expression(e),
                    Ok(FieldElementExpression::value(Bn128Field::from(3)))
                );
            }

            #[test]
            fn select() {
                let e = FieldElementExpression::select(
                    ArrayExpression::value(vec![
                        FieldElementExpression::value(Bn128Field::from(1)).into(),
                        FieldElementExpression::value(Bn128Field::from(2)).into(),
                        FieldElementExpression::value(Bn128Field::from(3)).into(),
                    ])
                    .annotate(ArrayType::new(Type::FieldElement, 3u32)),
                    UExpression::add(1u32.into(), 1u32.into()),
                );

                assert_eq!(
                    Propagator::default().fold_field_expression(e),
                    Ok(FieldElementExpression::value(Bn128Field::from(3)))
                );
            }
        }

        #[cfg(test)]
        mod boolean {
            use super::*;

            #[test]
            fn not() {
                let e_true: BooleanExpression<Bn128Field> =
                    BooleanExpression::not(BooleanExpression::value(false));

                let e_false: BooleanExpression<Bn128Field> =
                    BooleanExpression::not(BooleanExpression::value(true));

                let e_default: BooleanExpression<Bn128Field> =
                    BooleanExpression::not(BooleanExpression::identifier("a".into()));

                assert_eq!(
                    Propagator::default().fold_boolean_expression(e_true),
                    Ok(BooleanExpression::value(true))
                );
                assert_eq!(
                    Propagator::default().fold_boolean_expression(e_false),
                    Ok(BooleanExpression::value(false))
                );
                assert_eq!(
                    Propagator::default().fold_boolean_expression(e_default.clone()),
                    Ok(e_default)
                );
            }

            #[test]
            fn field_eq() {
                let e_constant_true = BooleanExpression::FieldEq(BinaryExpression::new(
                    FieldElementExpression::value(Bn128Field::from(2)),
                    FieldElementExpression::value(Bn128Field::from(2)),
                ));

                let e_constant_false = BooleanExpression::FieldEq(BinaryExpression::new(
                    FieldElementExpression::value(Bn128Field::from(4)),
                    FieldElementExpression::value(Bn128Field::from(2)),
                ));

                let e_identifier_true: BooleanExpression<Bn128Field> =
                    BooleanExpression::FieldEq(BinaryExpression::new(
                        FieldElementExpression::identifier("a".into()),
                        FieldElementExpression::identifier("a".into()),
                    ));

                let e_identifier_unchanged: BooleanExpression<Bn128Field> =
                    BooleanExpression::FieldEq(BinaryExpression::new(
                        FieldElementExpression::identifier("a".into()),
                        FieldElementExpression::identifier("b".into()),
                    ));

                assert_eq!(
                    Propagator::default().fold_boolean_expression(e_constant_true),
                    Ok(BooleanExpression::value(true))
                );
                assert_eq!(
                    Propagator::default().fold_boolean_expression(e_constant_false),
                    Ok(BooleanExpression::value(false))
                );
                assert_eq!(
                    Propagator::default().fold_boolean_expression(e_identifier_true),
                    Ok(BooleanExpression::value(true))
                );
                assert_eq!(
                    Propagator::default().fold_boolean_expression(e_identifier_unchanged.clone()),
                    Ok(e_identifier_unchanged)
                );
            }

            #[test]
            fn bool_eq() {
                assert_eq!(
                    Propagator::<Bn128Field>::default().fold_boolean_expression(
                        BooleanExpression::BoolEq(EqExpression::new(
                            BooleanExpression::value(false),
                            BooleanExpression::value(false)
                        ))
                    ),
                    Ok(BooleanExpression::value(true))
                );

                assert_eq!(
                    Propagator::<Bn128Field>::default().fold_boolean_expression(
                        BooleanExpression::BoolEq(EqExpression::new(
                            BooleanExpression::value(true),
                            BooleanExpression::value(true)
                        ))
                    ),
                    Ok(BooleanExpression::value(true))
                );

                assert_eq!(
                    Propagator::<Bn128Field>::default().fold_boolean_expression(
                        BooleanExpression::BoolEq(EqExpression::new(
                            BooleanExpression::value(true),
                            BooleanExpression::value(false)
                        ))
                    ),
                    Ok(BooleanExpression::value(false))
                );

                assert_eq!(
                    Propagator::<Bn128Field>::default().fold_boolean_expression(
                        BooleanExpression::BoolEq(EqExpression::new(
                            BooleanExpression::value(false),
                            BooleanExpression::value(true)
                        ))
                    ),
                    Ok(BooleanExpression::value(false))
                );
            }

            #[test]
            fn array_eq() {
                let e_constant_true = BooleanExpression::ArrayEq(BinaryExpression::new(
                    ArrayExpression::value(vec![TypedExpressionOrSpread::Expression(
                        FieldElementExpression::value(Bn128Field::from(2usize)).into(),
                    )])
                    .annotate(ArrayType::new(Type::FieldElement, 1u32)),
                    ArrayExpression::value(vec![TypedExpressionOrSpread::Expression(
                        FieldElementExpression::value(Bn128Field::from(2usize)).into(),
                    )])
                    .annotate(ArrayType::new(Type::FieldElement, 1u32)),
                ));

                let e_constant_false = BooleanExpression::ArrayEq(BinaryExpression::new(
                    ArrayExpression::value(vec![TypedExpressionOrSpread::Expression(
                        FieldElementExpression::value(Bn128Field::from(2usize)).into(),
                    )])
                    .annotate(ArrayType::new(Type::FieldElement, 1u32)),
                    ArrayExpression::value(vec![TypedExpressionOrSpread::Expression(
                        FieldElementExpression::value(Bn128Field::from(4usize)).into(),
                    )])
                    .annotate(ArrayType::new(Type::FieldElement, 1u32)),
                ));

                let e_identifier_true: BooleanExpression<Bn128Field> =
                    BooleanExpression::ArrayEq(BinaryExpression::new(
                        ArrayExpression::identifier("a".into())
                            .annotate(ArrayType::new(Type::FieldElement, 1u32)),
                        ArrayExpression::identifier("a".into())
                            .annotate(ArrayType::new(Type::FieldElement, 1u32)),
                    ));

                let e_identifier_unchanged: BooleanExpression<Bn128Field> =
                    BooleanExpression::ArrayEq(BinaryExpression::new(
                        ArrayExpression::identifier("a".into())
                            .annotate(ArrayType::new(Type::FieldElement, 1u32)),
                        ArrayExpression::identifier("b".into())
                            .annotate(ArrayType::new(Type::FieldElement, 1u32)),
                    ));

                let e_non_canonical_true = BooleanExpression::ArrayEq(BinaryExpression::new(
                    ArrayExpression::value(vec![TypedExpressionOrSpread::Spread(
                        ArrayExpression::value(vec![TypedExpressionOrSpread::Expression(
                            FieldElementExpression::value(Bn128Field::from(2usize)).into(),
                        )])
                        .annotate(ArrayType::new(Type::FieldElement, 1u32))
                        .into(),
                    )])
                    .annotate(ArrayType::new(Type::FieldElement, 1u32)),
                    ArrayExpression::value(vec![TypedExpressionOrSpread::Expression(
                        FieldElementExpression::value(Bn128Field::from(2usize)).into(),
                    )])
                    .annotate(ArrayType::new(Type::FieldElement, 1u32)),
                ));

                let e_non_canonical_false = BooleanExpression::ArrayEq(BinaryExpression::new(
                    ArrayExpression::value(vec![TypedExpressionOrSpread::Spread(
                        ArrayExpression::value(vec![TypedExpressionOrSpread::Expression(
                            FieldElementExpression::value(Bn128Field::from(2usize)).into(),
                        )])
                        .annotate(ArrayType::new(Type::FieldElement, 1u32))
                        .into(),
                    )])
                    .annotate(ArrayType::new(Type::FieldElement, 1u32)),
                    ArrayExpression::value(vec![TypedExpressionOrSpread::Expression(
                        FieldElementExpression::value(Bn128Field::from(4usize)).into(),
                    )])
                    .annotate(ArrayType::new(Type::FieldElement, 1u32)),
                ));

                assert_eq!(
                    Propagator::default().fold_boolean_expression(e_constant_true),
                    Ok(BooleanExpression::value(true))
                );
                assert_eq!(
                    Propagator::default().fold_boolean_expression(e_constant_false),
                    Ok(BooleanExpression::value(false))
                );
                assert_eq!(
                    Propagator::default().fold_boolean_expression(e_identifier_true),
                    Ok(BooleanExpression::value(true))
                );
                assert_eq!(
                    Propagator::default().fold_boolean_expression(e_identifier_unchanged.clone()),
                    Ok(e_identifier_unchanged)
                );
                assert_eq!(
                    Propagator::default().fold_boolean_expression(e_non_canonical_true),
                    Ok(BooleanExpression::value(true))
                );
                assert_eq!(
                    Propagator::default().fold_boolean_expression(e_non_canonical_false),
                    Ok(BooleanExpression::value(false))
                );
            }

            #[test]
            fn lt() {
                let e_true = BooleanExpression::field_lt(
                    FieldElementExpression::value(Bn128Field::from(2)),
                    FieldElementExpression::value(Bn128Field::from(4)),
                );

                let e_false = BooleanExpression::field_lt(
                    FieldElementExpression::value(Bn128Field::from(4)),
                    FieldElementExpression::value(Bn128Field::from(2)),
                );

                assert_eq!(
                    Propagator::default().fold_boolean_expression(e_true),
                    Ok(BooleanExpression::value(true))
                );
                assert_eq!(
                    Propagator::default().fold_boolean_expression(e_false),
                    Ok(BooleanExpression::value(false))
                );
            }

            #[test]
            fn le() {
                let e_true = BooleanExpression::field_le(
                    FieldElementExpression::value(Bn128Field::from(2)),
                    FieldElementExpression::value(Bn128Field::from(2)),
                );

                let e_false = BooleanExpression::field_le(
                    FieldElementExpression::value(Bn128Field::from(4)),
                    FieldElementExpression::value(Bn128Field::from(2)),
                );

                assert_eq!(
                    Propagator::default().fold_boolean_expression(e_true),
                    Ok(BooleanExpression::value(true))
                );
                assert_eq!(
                    Propagator::default().fold_boolean_expression(e_false),
                    Ok(BooleanExpression::value(false))
                );
            }

            #[test]
            fn gt() {
                let e_true = BooleanExpression::field_gt(
                    FieldElementExpression::value(Bn128Field::from(5)),
                    FieldElementExpression::value(Bn128Field::from(4)),
                );

                let e_false = BooleanExpression::field_gt(
                    FieldElementExpression::value(Bn128Field::from(4)),
                    FieldElementExpression::value(Bn128Field::from(5)),
                );

                assert_eq!(
                    Propagator::default().fold_boolean_expression(e_true),
                    Ok(BooleanExpression::value(true))
                );
                assert_eq!(
                    Propagator::default().fold_boolean_expression(e_false),
                    Ok(BooleanExpression::value(false))
                );
            }

            #[test]
            fn ge() {
                let e_true = BooleanExpression::field_ge(
                    FieldElementExpression::value(Bn128Field::from(5)),
                    FieldElementExpression::value(Bn128Field::from(5)),
                );

                let e_false = BooleanExpression::field_ge(
                    FieldElementExpression::value(Bn128Field::from(4)),
                    FieldElementExpression::value(Bn128Field::from(5)),
                );

                assert_eq!(
                    Propagator::default().fold_boolean_expression(e_true),
                    Ok(BooleanExpression::value(true))
                );
                assert_eq!(
                    Propagator::default().fold_boolean_expression(e_false),
                    Ok(BooleanExpression::value(false))
                );
            }

            #[test]
            fn and() {
                let a_bool: Identifier = "a".into();

                assert_eq!(
                    Propagator::<Bn128Field>::default().fold_boolean_expression(
                        BooleanExpression::bitand(
                            BooleanExpression::value(true),
                            BooleanExpression::identifier(a_bool.clone())
                        )
                    ),
                    Ok(BooleanExpression::identifier(a_bool.clone()))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::default().fold_boolean_expression(
                        BooleanExpression::bitand(
                            BooleanExpression::identifier(a_bool.clone()),
                            BooleanExpression::value(true),
                        )
                    ),
                    Ok(BooleanExpression::identifier(a_bool.clone()))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::default().fold_boolean_expression(
                        BooleanExpression::bitand(
                            BooleanExpression::value(false),
                            BooleanExpression::identifier(a_bool.clone())
                        )
                    ),
                    Ok(BooleanExpression::value(false))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::default().fold_boolean_expression(
                        BooleanExpression::bitand(
                            BooleanExpression::identifier(a_bool.clone()),
                            BooleanExpression::value(false),
                        )
                    ),
                    Ok(BooleanExpression::value(false))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::default().fold_boolean_expression(
                        BooleanExpression::bitand(
                            BooleanExpression::value(true),
                            BooleanExpression::value(false),
                        )
                    ),
                    Ok(BooleanExpression::value(false))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::default().fold_boolean_expression(
                        BooleanExpression::bitand(
                            BooleanExpression::value(false),
                            BooleanExpression::value(true),
                        )
                    ),
                    Ok(BooleanExpression::value(false))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::default().fold_boolean_expression(
                        BooleanExpression::bitand(
                            BooleanExpression::value(true),
                            BooleanExpression::value(true),
                        )
                    ),
                    Ok(BooleanExpression::value(true))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::default().fold_boolean_expression(
                        BooleanExpression::bitand(
                            BooleanExpression::value(false),
                            BooleanExpression::value(false),
                        )
                    ),
                    Ok(BooleanExpression::value(false))
                );
            }

            #[test]
            fn or() {
                let a_bool: Identifier = "a".into();

                assert_eq!(
                    Propagator::<Bn128Field>::default().fold_boolean_expression(
                        BooleanExpression::bitor(
                            BooleanExpression::value(true),
                            BooleanExpression::identifier(a_bool.clone())
                        )
                    ),
                    Ok(BooleanExpression::value(true))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::default().fold_boolean_expression(
                        BooleanExpression::bitor(
                            BooleanExpression::identifier(a_bool.clone()),
                            BooleanExpression::value(true),
                        )
                    ),
                    Ok(BooleanExpression::value(true))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::default().fold_boolean_expression(
                        BooleanExpression::bitor(
                            BooleanExpression::value(false),
                            BooleanExpression::identifier(a_bool.clone())
                        )
                    ),
                    Ok(BooleanExpression::identifier(a_bool.clone()))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::default().fold_boolean_expression(
                        BooleanExpression::bitor(
                            BooleanExpression::identifier(a_bool.clone()),
                            BooleanExpression::value(false),
                        )
                    ),
                    Ok(BooleanExpression::identifier(a_bool.clone()))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::default().fold_boolean_expression(
                        BooleanExpression::bitor(
                            BooleanExpression::value(true),
                            BooleanExpression::value(false),
                        )
                    ),
                    Ok(BooleanExpression::value(true))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::default().fold_boolean_expression(
                        BooleanExpression::bitor(
                            BooleanExpression::value(false),
                            BooleanExpression::value(true),
                        )
                    ),
                    Ok(BooleanExpression::value(true))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::default().fold_boolean_expression(
                        BooleanExpression::bitor(
                            BooleanExpression::value(true),
                            BooleanExpression::value(true),
                        )
                    ),
                    Ok(BooleanExpression::value(true))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::default().fold_boolean_expression(
                        BooleanExpression::bitor(
                            BooleanExpression::value(false),
                            BooleanExpression::value(false),
                        )
                    ),
                    Ok(BooleanExpression::value(false))
                );
            }
        }
    }
}
