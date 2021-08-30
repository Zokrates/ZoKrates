//! Module containing constant propagation for the typed AST
//!
//! Constant propagation on the SSA program. The constants map can be passed by the caller to allow for many passes to use
//! the same constants.
//!
//! @file propagation.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use crate::embed::FlatEmbed;
use crate::typed_absy::result_folder::*;
use crate::typed_absy::types::Type;
use crate::typed_absy::*;
use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};
use std::fmt;
use zokrates_field::Field;

type Constants<'ast, T> = HashMap<Identifier<'ast>, TypedExpression<'ast, T>>;

#[derive(Debug, PartialEq)]
pub enum Error {
    Type(String),
    AssertionFailed(String),
    OutOfBounds(u128, u128),
    NonConstantExponent(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Type(s) => write!(f, "{}", s),
            Error::AssertionFailed(s) => write!(f, "{}", s),
            Error::OutOfBounds(index, size) => write!(
                f,
                "Out of bounds index ({} >= {}) found during static analysis",
                index, size
            ),
            Error::NonConstantExponent(s) => write!(
                f,
                "Non-constant exponent `{}` detected during static analysis",
                s
            ),
        }
    }
}

pub struct Propagator<'ast, 'a, T: Field> {
    // constants keeps track of constant expressions
    // we currently do not support partially constant expressions: `field [x, 1][1]` is not considered constant, `field [0, 1][1]` is
    constants: &'a mut Constants<'ast, T>,
}

impl<'ast, 'a, T: Field> Propagator<'ast, 'a, T> {
    pub fn with_constants(constants: &'a mut Constants<'ast, T>) -> Self {
        Propagator { constants }
    }

    pub fn propagate(p: TypedProgram<'ast, T>) -> Result<TypedProgram<'ast, T>, Error> {
        let mut constants = Constants::new();

        Propagator {
            constants: &mut constants,
        }
        .fold_program(p)
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
            TypedAssignee::Select(box assignee, box index) => {
                match self.try_get_constant_mut(&assignee) {
                    Ok((variable, constant)) => match index.as_inner() {
                        UExpressionInner::Value(n) => match constant {
                            TypedExpression::Array(a) => match a.as_inner_mut() {
                                ArrayExpressionInner::Value(value) => {
                                    match value.0.get_mut(*n as usize) {
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
                }
            }
            TypedAssignee::Member(box assignee, m) => match self.try_get_constant_mut(&assignee) {
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
                            StructExpressionInner::Value(value) => Ok((v, &mut value[index])),
                            _ => unreachable!("should be a struct value"),
                        },
                        _ => unreachable!("should be a struct expression"),
                    }
                }
                e => e,
            },
        }
    }
}

impl<'ast, 'a, T: Field> ResultFolder<'ast, T> for Propagator<'ast, 'a, T> {
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
            main: p.main,
        })
    }

    fn fold_module(&mut self, m: TypedModule<'ast, T>) -> Result<TypedModule<'ast, T>, Error> {
        Ok(TypedModule {
            functions: m
                .functions
                .into_iter()
                .map(|(key, fun)| {
                    if key.id == "main" {
                        self.fold_function_symbol(fun).map(|f| (key, f))
                    } else {
                        Ok((key, fun))
                    }
                })
                .collect::<Result<_, _>>()?,
            ..m
        })
    }

    fn fold_function(
        &mut self,
        f: TypedFunction<'ast, T>,
    ) -> Result<TypedFunction<'ast, T>, Error> {
        fold_function(self, f)
    }

    fn fold_if_else_expression<
        E: Expr<'ast, T> + IfElse<'ast, T> + PartialEq + ResultFold<'ast, T>,
    >(
        &mut self,
        _: &E::Ty,
        e: IfElseExpression<'ast, T, E>,
    ) -> Result<IfElseOrExpression<'ast, T, E>, Self::Error> {
        Ok(
            match (
                self.fold_boolean_expression(*e.condition)?,
                e.consequence.fold(self)?,
                e.alternative.fold(self)?,
            ) {
                (BooleanExpression::Value(true), consequence, _) => {
                    IfElseOrExpression::Expression(consequence.into_inner())
                }
                (BooleanExpression::Value(false), _, alternative) => {
                    IfElseOrExpression::Expression(alternative.into_inner())
                }
                (_, consequence, alternative) if consequence == alternative => {
                    IfElseOrExpression::Expression(consequence.into_inner())
                }
                (condition, consequence, alternative) => IfElseOrExpression::IfElse(
                    IfElseExpression::new(condition, consequence, alternative),
                ),
            },
        )
    }

    fn fold_statement(
        &mut self,
        s: TypedStatement<'ast, T>,
    ) -> Result<Vec<TypedStatement<'ast, T>>, Error> {
        match s {
            // propagation to the defined variable if rhs is a constant
            TypedStatement::Definition(assignee, expr) => {
                let expr = self.fold_expression(expr)?;
                let assignee = self.fold_assignee(assignee)?;

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
                                    TypedStatement::Definition(v.clone().into(), c),
                                    TypedStatement::Definition(assignee, expr),
                                ]),
                                None => Ok(vec![TypedStatement::Definition(assignee, expr)]),
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
                            TypedStatement::Definition(v.clone().into(), c),
                            TypedStatement::Definition(assignee, expr),
                        ]),
                        None => Ok(vec![TypedStatement::Definition(assignee, expr)]),
                    }
                }
            }
            // we do not visit the for-loop statements
            TypedStatement::For(v, from, to, statements) => {
                let from = self.fold_uint_expression(from)?;
                let to = self.fold_uint_expression(to)?;

                Ok(vec![TypedStatement::For(v, from, to, statements)])
            }
            TypedStatement::MultipleDefinition(assignees, expression_list) => {
                let assignees: Vec<TypedAssignee<'ast, T>> = assignees
                    .into_iter()
                    .map(|a| self.fold_assignee(a))
                    .collect::<Result<_, _>>()?;
                let expression_list = self.fold_expression_list(expression_list)?;

                let types = Types {
                    inner: expression_list
                        .types
                        .clone()
                        .inner
                        .into_iter()
                        .map(|t| self.fold_type(t))
                        .collect::<Result<_, _>>()?,
                };

                let statements = match expression_list.into_inner() {
                    TypedExpressionListInner::EmbedCall(embed, generics, arguments) => {
                        let arguments: Vec<_> = arguments
                            .into_iter()
                            .map(|a| self.fold_expression(a))
                            .collect::<Result<_, _>>()?;

                        fn process_u_from_bits<'ast, T: Field>(
                            variables: Vec<TypedAssignee<'ast, T>>,
                            mut arguments: Vec<TypedExpression<'ast, T>>,
                            bitwidth: UBitwidth,
                        ) -> TypedExpression<'ast, T> {
                            assert_eq!(variables.len(), 1);
                            assert_eq!(arguments.len(), 1);

                            let argument = arguments.pop().unwrap();

                            let argument = argument.into_canonical_constant();

                            match ArrayExpression::try_from(argument)
                                .unwrap()
                                .into_inner()
                            {
                                ArrayExpressionInner::Value(v) =>
                                    UExpressionInner::Value(
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
                                                if v {
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
                            variables: Vec<TypedAssignee<'ast, T>>,
                            arguments: Vec<TypedExpression<'ast, T>>,
                            bitwidth: UBitwidth,
                        ) -> TypedExpression<'ast, T> {
                            assert_eq!(variables.len(), 1);
                            assert_eq!(arguments.len(), 1);

                            match UExpression::try_from(arguments[0].clone())
                                .unwrap()
                                .into_inner()
                            {
                                UExpressionInner::Value(v) => {
                                    let mut num = v;
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

                                    ArrayExpressionInner::Value(
                                        res.into_iter()
                                            .map(|v| BooleanExpression::Value(v).into())
                                            .collect::<Vec<_>>()
                                            .into(),
                                    )
                                    .annotate(Type::Boolean, bitwidth.to_usize() as u32)
                                    .into()
                                }
                                _ => unreachable!("should be a uint value"),
                            }
                        }

                        match arguments.iter().all(|a| a.is_constant()) {
                            true => {
                                let r: Option<TypedExpression<'ast, T>> = match embed {
                                    FlatEmbed::BitArrayLe => None, // todo
                                    FlatEmbed::U64FromBits => Some(process_u_from_bits(
                                        assignees.clone(),
                                        arguments.clone(),
                                        UBitwidth::B64,
                                    )),
                                    FlatEmbed::U32FromBits => Some(process_u_from_bits(
                                        assignees.clone(),
                                        arguments.clone(),
                                        UBitwidth::B32,
                                    )),
                                    FlatEmbed::U16FromBits => Some(process_u_from_bits(
                                        assignees.clone(),
                                        arguments.clone(),
                                        UBitwidth::B16,
                                    )),
                                    FlatEmbed::U8FromBits => Some(process_u_from_bits(
                                        assignees.clone(),
                                        arguments.clone(),
                                        UBitwidth::B8,
                                    )),
                                    FlatEmbed::U64ToBits => Some(process_u_to_bits(
                                        assignees.clone(),
                                        arguments.clone(),
                                        UBitwidth::B64,
                                    )),
                                    FlatEmbed::U32ToBits => Some(process_u_to_bits(
                                        assignees.clone(),
                                        arguments.clone(),
                                        UBitwidth::B32,
                                    )),
                                    FlatEmbed::U16ToBits => Some(process_u_to_bits(
                                        assignees.clone(),
                                        arguments.clone(),
                                        UBitwidth::B16,
                                    )),
                                    FlatEmbed::U8ToBits => Some(process_u_to_bits(
                                        assignees.clone(),
                                        arguments.clone(),
                                        UBitwidth::B8,
                                    )),
                                    FlatEmbed::Unpack => {
                                        assert_eq!(assignees.len(), 1);
                                        assert_eq!(arguments.len(), 1);
                                        assert_eq!(generics.len(), 1);

                                        let bit_width = generics[0];

                                        match FieldElementExpression::try_from(arguments[0].clone())
                                            .unwrap()
                                        {
                                            FieldElementExpression::Number(num) => {
                                                let mut num = num;
                                                let mut res = vec![];

                                                for i in (0..bit_width as usize).rev() {
                                                    if T::from(2).pow(i) <= num {
                                                        num = num - T::from(2).pow(i);
                                                        res.push(true);
                                                    } else {
                                                        res.push(false);
                                                    }
                                                }
                                                assert_eq!(num, T::zero());

                                                Some(
                                                    ArrayExpressionInner::Value(
                                                        res.into_iter()
                                                            .map(|v| {
                                                                BooleanExpression::Value(v).into()
                                                            })
                                                            .collect::<Vec<_>>()
                                                            .into(),
                                                    )
                                                    .annotate(Type::Boolean, bit_width)
                                                    .into(),
                                                )
                                            }
                                            _ => unreachable!("should be a field value"),
                                        }
                                    }
                                    #[cfg(feature = "bellman")]
                                    FlatEmbed::Sha256Round => None,
                                    #[cfg(feature = "ark")]
                                    FlatEmbed::SnarkVerifyBls12377 => None,
                                };

                                match r {
                                    // if the function call returns a constant
                                    Some(expr) => {
                                        let mut assignees = assignees;

                                        match assignees.pop().unwrap() {
                                            TypedAssignee::Identifier(var) => {
                                                self.constants.insert(var.id, expr);
                                                vec![]
                                            }
                                            assignee => {
                                                match self.try_get_constant_mut(&assignee) {
                                                    Ok((_, c)) => {
                                                        *c = expr;
                                                        vec![]
                                                    }
                                                    Err(v) => match self.constants.remove(&v.id) {
                                                        Some(c) => vec![
                                                            TypedStatement::Definition(
                                                                v.clone().into(),
                                                                c,
                                                            ),
                                                            TypedStatement::Definition(
                                                                assignee, expr,
                                                            ),
                                                        ],
                                                        None => vec![TypedStatement::Definition(
                                                            assignee, expr,
                                                        )],
                                                    },
                                                }
                                            }
                                        }
                                    }
                                    None => {
                                        // if the function call does not return a constant, invalidate the cache
                                        // this happpens because we only propagate certain calls here
                                        let mut assignees = assignees;

                                        let assignee = assignees.pop().unwrap();

                                        let v = self
                                            .try_get_constant_mut(&assignee)
                                            .map(|(v, _)| v)
                                            .unwrap_or_else(|v| v);

                                        match self.constants.remove(&v.id) {
                                            Some(c) => vec![
                                                TypedStatement::Definition(v.clone().into(), c),
                                                TypedStatement::MultipleDefinition(
                                                    vec![assignee],
                                                    TypedExpressionListInner::EmbedCall(
                                                        embed, generics, arguments,
                                                    )
                                                    .annotate(types),
                                                ),
                                            ],
                                            None => vec![TypedStatement::MultipleDefinition(
                                                vec![assignee],
                                                TypedExpressionListInner::EmbedCall(
                                                    embed, generics, arguments,
                                                )
                                                .annotate(types),
                                            )],
                                        }
                                    }
                                }
                            }
                            false => {
                                // if the function arguments are not constant, invalidate the cache
                                // for the return assignees

                                let def = TypedStatement::MultipleDefinition(
                                    assignees.clone(),
                                    TypedExpressionListInner::EmbedCall(embed, generics, arguments)
                                        .annotate(types),
                                );

                                let invalidations = assignees.iter().flat_map(|assignee| {
                                    let v = self
                                        .try_get_constant_mut(&assignee)
                                        .map(|(v, _)| v)
                                        .unwrap_or_else(|v| v);
                                    match self.constants.remove(&v.id) {
                                        Some(c) => {
                                            vec![TypedStatement::Definition(v.clone().into(), c)]
                                        }
                                        None => vec![],
                                    }
                                });

                                invalidations.chain(std::iter::once(def)).collect()
                            }
                        }
                    }
                    TypedExpressionListInner::FunctionCall(function_call) => {
                        let generics = function_call
                            .generics
                            .into_iter()
                            .map(|g| g.map(|g| self.fold_uint_expression(g)).transpose())
                            .collect::<Result<_, _>>()?;

                        let arguments: Vec<_> = function_call
                            .arguments
                            .into_iter()
                            .map(|a| self.fold_expression(a))
                            .collect::<Result<_, _>>()?;

                        // invalidate the cache for the return assignees as this call mutates them

                        let def = TypedStatement::MultipleDefinition(
                            assignees.clone(),
                            TypedExpressionList::function_call(
                                function_call.function_key,
                                generics,
                                arguments,
                            )
                            .annotate(types),
                        );

                        let invalidations = assignees.iter().flat_map(|assignee| {
                            let v = self
                                .try_get_constant_mut(&assignee)
                                .map(|(v, _)| v)
                                .unwrap_or_else(|v| v);
                            match self.constants.remove(&v.id) {
                                Some(c) => {
                                    vec![TypedStatement::Definition(v.clone().into(), c)]
                                }
                                None => vec![],
                            }
                        });

                        invalidations.chain(std::iter::once(def)).collect()
                    }
                };

                Ok(statements)
            }
            TypedStatement::Assertion(e) => {
                let e_str = e.to_string();
                let expr = self.fold_boolean_expression(e)?;
                match expr {
                    BooleanExpression::Value(v) if !v => Err(Error::AssertionFailed(format!(
                        "Assertion failed on expression `{}`",
                        e_str
                    ))),
                    _ => Ok(vec![TypedStatement::Assertion(expr)]),
                }
            }
            s @ TypedStatement::PushCallLog(..) => Ok(vec![s]),
            s @ TypedStatement::PopCallLog => Ok(vec![s]),
            s => fold_statement(self, s),
        }
    }

    fn fold_uint_expression_inner(
        &mut self,
        bitwidth: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> Result<UExpressionInner<'ast, T>, Error> {
        match e {
            UExpressionInner::Identifier(id) => match self.constants.get(&id) {
                Some(e) => match e {
                    TypedExpression::Uint(e) => Ok(e.as_inner().clone()),
                    _ => unreachable!("constant stored for a uint should be a uint"),
                },
                None => Ok(UExpressionInner::Identifier(id)),
            },
            UExpressionInner::Add(box e1, box e2) => match (
                self.fold_uint_expression(e1)?.into_inner(),
                self.fold_uint_expression(e2)?.into_inner(),
            ) {
                (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                    Ok(UExpressionInner::Value(
                        (v1 + v2) % 2_u128.pow(bitwidth.to_usize().try_into().unwrap()),
                    ))
                }
                (e, UExpressionInner::Value(v)) | (UExpressionInner::Value(v), e) => match v {
                    0 => Ok(e),
                    _ => Ok(UExpressionInner::Add(
                        box e.annotate(bitwidth),
                        box UExpressionInner::Value(v).annotate(bitwidth),
                    )),
                },
                (e1, e2) => Ok(UExpressionInner::Add(
                    box e1.annotate(bitwidth),
                    box e2.annotate(bitwidth),
                )),
            },
            UExpressionInner::Sub(box e1, box e2) => match (
                self.fold_uint_expression(e1)?.into_inner(),
                self.fold_uint_expression(e2)?.into_inner(),
            ) {
                (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                    Ok(UExpressionInner::Value(
                        (v1.wrapping_sub(v2)) % 2_u128.pow(bitwidth.to_usize().try_into().unwrap()),
                    ))
                }
                (e, UExpressionInner::Value(v)) => match v {
                    0 => Ok(e),
                    _ => Ok(UExpressionInner::Sub(
                        box e.annotate(bitwidth),
                        box UExpressionInner::Value(v).annotate(bitwidth),
                    )),
                },
                (e1, e2) => Ok(UExpressionInner::Sub(
                    box e1.annotate(bitwidth),
                    box e2.annotate(bitwidth),
                )),
            },
            UExpressionInner::FloorSub(box e1, box e2) => match (
                self.fold_uint_expression(e1)?.into_inner(),
                self.fold_uint_expression(e2)?.into_inner(),
            ) {
                (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                    Ok(UExpressionInner::Value(
                        v1.saturating_sub(v2) % 2_u128.pow(bitwidth.to_usize().try_into().unwrap()),
                    ))
                }
                (e, UExpressionInner::Value(v)) => match v {
                    0 => Ok(e),
                    _ => Ok(UExpressionInner::FloorSub(
                        box e.annotate(bitwidth),
                        box UExpressionInner::Value(v).annotate(bitwidth),
                    )),
                },
                (e1, e2) => Ok(UExpressionInner::Sub(
                    box e1.annotate(bitwidth),
                    box e2.annotate(bitwidth),
                )),
            },
            UExpressionInner::Mult(box e1, box e2) => match (
                self.fold_uint_expression(e1)?.into_inner(),
                self.fold_uint_expression(e2)?.into_inner(),
            ) {
                (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                    Ok(UExpressionInner::Value(
                        (v1 * v2) % 2_u128.pow(bitwidth.to_usize().try_into().unwrap()),
                    ))
                }
                (e, UExpressionInner::Value(v)) | (UExpressionInner::Value(v), e) => match v {
                    0 => Ok(UExpressionInner::Value(0)),
                    1 => Ok(e),
                    _ => Ok(UExpressionInner::Mult(
                        box e.annotate(bitwidth),
                        box UExpressionInner::Value(v).annotate(bitwidth),
                    )),
                },
                (e1, e2) => Ok(UExpressionInner::Mult(
                    box e1.annotate(bitwidth),
                    box e2.annotate(bitwidth),
                )),
            },
            UExpressionInner::Div(box e1, box e2) => match (
                self.fold_uint_expression(e1)?.into_inner(),
                self.fold_uint_expression(e2)?.into_inner(),
            ) {
                (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                    Ok(UExpressionInner::Value(
                        (v1 / v2) % 2_u128.pow(bitwidth.to_usize().try_into().unwrap()),
                    ))
                }
                (e, UExpressionInner::Value(v)) => match v {
                    1 => Ok(e),
                    _ => Ok(UExpressionInner::Div(
                        box e.annotate(bitwidth),
                        box UExpressionInner::Value(v).annotate(bitwidth),
                    )),
                },
                (e1, e2) => Ok(UExpressionInner::Div(
                    box e1.annotate(bitwidth),
                    box e2.annotate(bitwidth),
                )),
            },
            UExpressionInner::Rem(box e1, box e2) => match (
                self.fold_uint_expression(e1)?.into_inner(),
                self.fold_uint_expression(e2)?.into_inner(),
            ) {
                (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                    Ok(UExpressionInner::Value(
                        (v1 % v2) % 2_u128.pow(bitwidth.to_usize().try_into().unwrap()),
                    ))
                }
                (e, UExpressionInner::Value(v)) => match v {
                    1 => Ok(UExpressionInner::Value(0)),
                    _ => Ok(UExpressionInner::Rem(
                        box e.annotate(bitwidth),
                        box UExpressionInner::Value(v).annotate(bitwidth),
                    )),
                },
                (e1, e2) => Ok(UExpressionInner::Rem(
                    box e1.annotate(bitwidth),
                    box e2.annotate(bitwidth),
                )),
            },
            UExpressionInner::RightShift(box e, box by) => {
                let e = self.fold_uint_expression(e)?;
                let by = self.fold_uint_expression(by)?;
                match (e.into_inner(), by.into_inner()) {
                    (UExpressionInner::Value(v), UExpressionInner::Value(by)) => {
                        Ok(UExpressionInner::Value(v >> by))
                    }
                    (e, by) => Ok(UExpressionInner::RightShift(
                        box e.annotate(bitwidth),
                        box by.annotate(UBitwidth::B32),
                    )),
                }
            }
            UExpressionInner::LeftShift(box e, box by) => {
                let e = self.fold_uint_expression(e)?;
                let by = self.fold_uint_expression(by)?;
                match (e.into_inner(), by.into_inner()) {
                    (UExpressionInner::Value(v), UExpressionInner::Value(by)) => Ok(
                        UExpressionInner::Value((v << by) & (2_u128.pow(bitwidth as u32) - 1)),
                    ),
                    (e, by) => Ok(UExpressionInner::LeftShift(
                        box e.annotate(bitwidth),
                        box by.annotate(UBitwidth::B32),
                    )),
                }
            }
            UExpressionInner::Xor(box e1, box e2) => match (
                self.fold_uint_expression(e1)?.into_inner(),
                self.fold_uint_expression(e2)?.into_inner(),
            ) {
                (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                    Ok(UExpressionInner::Value(v1 ^ v2))
                }
                (UExpressionInner::Value(0), e2) => Ok(e2),
                (e1, UExpressionInner::Value(0)) => Ok(e1),
                (e1, e2) => {
                    if e1 == e2 {
                        Ok(UExpressionInner::Value(0))
                    } else {
                        Ok(UExpressionInner::Xor(
                            box e1.annotate(bitwidth),
                            box e2.annotate(bitwidth),
                        ))
                    }
                }
            },
            UExpressionInner::And(box e1, box e2) => match (
                self.fold_uint_expression(e1)?.into_inner(),
                self.fold_uint_expression(e2)?.into_inner(),
            ) {
                (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                    Ok(UExpressionInner::Value(v1 & v2))
                }
                (UExpressionInner::Value(0), _) | (_, UExpressionInner::Value(0)) => {
                    Ok(UExpressionInner::Value(0))
                }
                (e1, e2) => Ok(UExpressionInner::And(
                    box e1.annotate(bitwidth),
                    box e2.annotate(bitwidth),
                )),
            },
            UExpressionInner::Not(box e) => {
                let e = self.fold_uint_expression(e)?.into_inner();
                match e {
                    UExpressionInner::Value(v) => Ok(UExpressionInner::Value(
                        (!v) & (2_u128.pow(bitwidth as u32) - 1),
                    )),
                    e => Ok(UExpressionInner::Not(box e.annotate(bitwidth))),
                }
            }
            UExpressionInner::Neg(box e) => {
                let e = self.fold_uint_expression(e)?.into_inner();
                match e {
                    UExpressionInner::Value(v) => Ok(UExpressionInner::Value(
                        (0u128.wrapping_sub(v))
                            % 2_u128.pow(bitwidth.to_usize().try_into().unwrap()),
                    )),
                    e => Ok(UExpressionInner::Neg(box e.annotate(bitwidth))),
                }
            }
            UExpressionInner::Pos(box e) => {
                let e = self.fold_uint_expression(e)?.into_inner();
                match e {
                    UExpressionInner::Value(v) => Ok(UExpressionInner::Value(v)),
                    e => Ok(UExpressionInner::Pos(box e.annotate(bitwidth))),
                }
            }
            e => fold_uint_expression_inner(self, bitwidth, e),
        }
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> Result<FieldElementExpression<'ast, T>, Error> {
        match e {
            FieldElementExpression::Identifier(id) => match self.constants.get(&id) {
                Some(e) => match e {
                    TypedExpression::FieldElement(e) => Ok(e.clone()),
                    _ => unreachable!(
                        "constant stored for a field element should be a field element"
                    ),
                },
                None => Ok(FieldElementExpression::Identifier(id)),
            },
            FieldElementExpression::Add(box e1, box e2) => match (
                self.fold_field_expression(e1)?,
                self.fold_field_expression(e2)?,
            ) {
                (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                    Ok(FieldElementExpression::Number(n1 + n2))
                }
                (e1, e2) => Ok(FieldElementExpression::Add(box e1, box e2)),
            },
            FieldElementExpression::Sub(box e1, box e2) => match (
                self.fold_field_expression(e1)?,
                self.fold_field_expression(e2)?,
            ) {
                (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                    Ok(FieldElementExpression::Number(n1 - n2))
                }
                (e1, e2) => Ok(FieldElementExpression::Sub(box e1, box e2)),
            },
            FieldElementExpression::Mult(box e1, box e2) => match (
                self.fold_field_expression(e1)?,
                self.fold_field_expression(e2)?,
            ) {
                (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                    Ok(FieldElementExpression::Number(n1 * n2))
                }
                (e1, e2) => Ok(FieldElementExpression::Mult(box e1, box e2)),
            },
            FieldElementExpression::Div(box e1, box e2) => match (
                self.fold_field_expression(e1)?,
                self.fold_field_expression(e2)?,
            ) {
                (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                    Ok(FieldElementExpression::Number(n1 / n2))
                }
                (e1, e2) => Ok(FieldElementExpression::Div(box e1, box e2)),
            },
            FieldElementExpression::Neg(box e) => match self.fold_field_expression(e)? {
                FieldElementExpression::Number(n) => {
                    Ok(FieldElementExpression::Number(T::zero() - n))
                }
                e => Ok(FieldElementExpression::Neg(box e)),
            },
            FieldElementExpression::Pos(box e) => match self.fold_field_expression(e)? {
                FieldElementExpression::Number(n) => Ok(FieldElementExpression::Number(n)),
                e => Ok(FieldElementExpression::Pos(box e)),
            },
            FieldElementExpression::Pow(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1)?;
                let e2 = self.fold_uint_expression(e2)?;
                match (e1, e2.into_inner()) {
                    (_, UExpressionInner::Value(ref n2)) if *n2 == 0 => {
                        Ok(FieldElementExpression::Number(T::from(1)))
                    }
                    (FieldElementExpression::Number(n1), UExpressionInner::Value(n2)) => {
                        Ok(FieldElementExpression::Number(n1.pow(n2 as usize)))
                    }
                    (e1, UExpressionInner::Value(n2)) => Ok(FieldElementExpression::Pow(
                        box e1,
                        box UExpressionInner::Value(n2).annotate(UBitwidth::B32),
                    )),
                    (_, e2) => Err(Error::NonConstantExponent(
                        e2.annotate(UBitwidth::B32).to_string(),
                    )),
                }
            }
            e => fold_field_expression(self, e),
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

    fn fold_select_expression<
        E: Expr<'ast, T> + Select<'ast, T> + From<TypedExpression<'ast, T>>,
    >(
        &mut self,
        _: &E::Ty,
        e: SelectExpression<'ast, T, E>,
    ) -> Result<SelectOrExpression<'ast, T, E>, Self::Error> {
        let array = self.fold_array_expression(*e.array)?;
        let index = self.fold_uint_expression(*e.index)?;

        let inner_type = array.inner_type().clone();
        let size = array.size();

        match size.into_inner() {
            UExpressionInner::Value(size) => match (array.into_inner(), index.into_inner()) {
                (ArrayExpressionInner::Value(v), UExpressionInner::Value(n)) => {
                    if n < size {
                        Ok(SelectOrExpression::Expression(
                            E::from(
                                v.expression_at::<StructExpression<'ast, T>>(n as usize)
                                    .unwrap()
                                    .clone(),
                            )
                            .into_inner(),
                        ))
                    } else {
                        Err(Error::OutOfBounds(n, size))
                    }
                }
                (ArrayExpressionInner::Identifier(id), UExpressionInner::Value(n)) => {
                    match self.constants.get(&id) {
                        Some(a) => match a {
                            TypedExpression::Array(a) => match a.as_inner() {
                                ArrayExpressionInner::Value(v) => {
                                    Ok(SelectOrExpression::Expression(
                                        E::from(
                                            v.expression_at::<StructExpression<'ast, T>>(
                                                n as usize,
                                            )
                                            .unwrap()
                                            .clone(),
                                        )
                                        .into_inner(),
                                    ))
                                }
                                _ => unreachable!("should be an array value"),
                            },
                            _ => unreachable!("should be an array expression"),
                        },
                        None => Ok(SelectOrExpression::Expression(
                            E::select(
                                ArrayExpressionInner::Identifier(id)
                                    .annotate(inner_type, size as u32),
                                UExpressionInner::Value(n).annotate(UBitwidth::B32),
                            )
                            .into_inner(),
                        )),
                    }
                }
                (a, i) => Ok(SelectOrExpression::Select(SelectExpression::new(
                    a.annotate(inner_type, size as u32),
                    i.annotate(UBitwidth::B32),
                ))),
            },
            _ => Ok(SelectOrExpression::Select(SelectExpression::new(
                array, index,
            ))),
        }
    }

    fn fold_array_expression_inner(
        &mut self,
        ty: &ArrayType<'ast, T>,
        e: ArrayExpressionInner<'ast, T>,
    ) -> Result<ArrayExpressionInner<'ast, T>, Error> {
        match e {
            ArrayExpressionInner::Identifier(id) => match self.constants.get(&id) {
                Some(e) => match e {
                    TypedExpression::Array(e) => Ok(e.as_inner().clone()),
                    _ => panic!("constant stored for an array should be an array"),
                },
                None => Ok(ArrayExpressionInner::Identifier(id)),
            },
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
                                }) => v.0,
                                e => vec![e],
                            }
                        })
                        // ignore spreads over empty arrays
                        .filter_map(|e| match e {
                            TypedExpressionOrSpread::Spread(s) if s.array.size() == UExpression::from(0u32) => None,
                            e => Some(e),
                        })
                        .collect(),
                ))
            }
            e => fold_array_expression_inner(self, ty, e),
        }
    }

    fn fold_struct_expression_inner(
        &mut self,
        ty: &StructType<'ast, T>,
        e: StructExpressionInner<'ast, T>,
    ) -> Result<StructExpressionInner<'ast, T>, Error> {
        match e {
            StructExpressionInner::Identifier(id) => match self.constants.get(&id) {
                Some(e) => match e {
                    TypedExpression::Struct(e) => Ok(e.as_inner().clone()),
                    _ => panic!("constant stored for an array should be an array"),
                },
                None => Ok(StructExpressionInner::Identifier(id)),
            },
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
            e => fold_struct_expression_inner(self, ty, e),
        }
    }

    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> Result<BooleanExpression<'ast, T>, Error> {
        // Note: we only propagate when we see constants, as comparing of arbitrary expressions would lead to
        // a lot of false negatives due to expressions not being in a canonical form
        // For example, `2 * a` is equivalent to `a + a`, but our notion of equality would not detect that here
        // These kind of reduction rules are easier to apply later in the process, when we have canonical representations
        // of expressions, ie `a + a` would always be written `2 * a`
        match e {
            BooleanExpression::Identifier(id) => match self.constants.get(&id) {
                Some(e) => match e {
                    TypedExpression::Boolean(e) => Ok(e.clone()),
                    _ => panic!("constant stored for a boolean should be a boolean"),
                },
                None => Ok(BooleanExpression::Identifier(id)),
            },
            BooleanExpression::FieldEq(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1)?;
                let e2 = self.fold_field_expression(e2)?;

                match (e1, e2) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        Ok(BooleanExpression::Value(n1 == n2))
                    }
                    (e1, e2) => Ok(BooleanExpression::FieldEq(box e1, box e2)),
                }
            }
            BooleanExpression::UintEq(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1)?;
                let e2 = self.fold_uint_expression(e2)?;

                match (e1.as_inner(), e2.as_inner()) {
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        Ok(BooleanExpression::Value(n1 == n2))
                    }
                    _ => Ok(BooleanExpression::UintEq(box e1, box e2)),
                }
            }
            BooleanExpression::BoolEq(box e1, box e2) => {
                let e1 = self.fold_boolean_expression(e1)?;
                let e2 = self.fold_boolean_expression(e2)?;

                match (e1, e2) {
                    (BooleanExpression::Value(n1), BooleanExpression::Value(n2)) => {
                        Ok(BooleanExpression::Value(n1 == n2))
                    }
                    (e1, e2) => Ok(BooleanExpression::BoolEq(box e1, box e2)),
                }
            }
            BooleanExpression::ArrayEq(box e1, box e2) => {
                let e1 = self.fold_array_expression(e1)?;
                let e2 = self.fold_array_expression(e2)?;

                if let (Ok(t1), Ok(t2)) = (
                    ConcreteType::try_from(e1.get_type()),
                    ConcreteType::try_from(e2.get_type()),
                ) {
                    if t1 != t2 {
                        return Err(Error::Type(format!(
                            "Cannot compare {} of type {} to {} of type {}",
                            e1, t1, e2, t2
                        )));
                    }
                };

                Ok(BooleanExpression::ArrayEq(box e1, box e2))
            }
            BooleanExpression::StructEq(box e1, box e2) => {
                let e1 = self.fold_struct_expression(e1)?;
                let e2 = self.fold_struct_expression(e2)?;

                if let (Ok(t1), Ok(t2)) = (
                    ConcreteType::try_from(e1.get_type()),
                    ConcreteType::try_from(e2.get_type()),
                ) {
                    if t1 != t2 {
                        return Err(Error::Type(format!(
                            "Cannot compare {} of type {} to {} of type {}",
                            e1, t1, e2, t2
                        )));
                    }
                };

                Ok(BooleanExpression::StructEq(box e1, box e2))
            }
            BooleanExpression::FieldLt(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1)?;
                let e2 = self.fold_field_expression(e2)?;

                match (e1, e2) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        Ok(BooleanExpression::Value(n1 < n2))
                    }
                    (e1, e2) => Ok(BooleanExpression::FieldLt(box e1, box e2)),
                }
            }
            BooleanExpression::FieldLe(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1)?;
                let e2 = self.fold_field_expression(e2)?;

                match (e1, e2) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        Ok(BooleanExpression::Value(n1 <= n2))
                    }
                    (e1, e2) => Ok(BooleanExpression::FieldLe(box e1, box e2)),
                }
            }
            BooleanExpression::FieldGt(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1)?;
                let e2 = self.fold_field_expression(e2)?;

                match (e1, e2) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        Ok(BooleanExpression::Value(n1 > n2))
                    }
                    (e1, e2) => Ok(BooleanExpression::FieldGt(box e1, box e2)),
                }
            }
            BooleanExpression::FieldGe(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1)?;
                let e2 = self.fold_field_expression(e2)?;

                match (e1, e2) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        Ok(BooleanExpression::Value(n1 >= n2))
                    }
                    (e1, e2) => Ok(BooleanExpression::FieldGe(box e1, box e2)),
                }
            }
            BooleanExpression::UintLt(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1)?;
                let e2 = self.fold_uint_expression(e2)?;

                match (e1.as_inner(), e2.as_inner()) {
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        Ok(BooleanExpression::Value(n1 < n2))
                    }
                    _ => Ok(BooleanExpression::UintLt(box e1, box e2)),
                }
            }
            BooleanExpression::UintLe(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1)?;
                let e2 = self.fold_uint_expression(e2)?;

                match (e1.as_inner(), e2.as_inner()) {
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        Ok(BooleanExpression::Value(n1 <= n2))
                    }
                    _ => Ok(BooleanExpression::UintLe(box e1, box e2)),
                }
            }
            BooleanExpression::UintGt(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1)?;
                let e2 = self.fold_uint_expression(e2)?;

                match (e1.as_inner(), e2.as_inner()) {
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        Ok(BooleanExpression::Value(n1 > n2))
                    }
                    _ => Ok(BooleanExpression::UintGt(box e1, box e2)),
                }
            }
            BooleanExpression::UintGe(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1)?;
                let e2 = self.fold_uint_expression(e2)?;

                match (e1.as_inner(), e2.as_inner()) {
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        Ok(BooleanExpression::Value(n1 >= n2))
                    }
                    _ => Ok(BooleanExpression::UintGe(box e1, box e2)),
                }
            }
            BooleanExpression::Or(box e1, box e2) => {
                let e1 = self.fold_boolean_expression(e1)?;
                let e2 = self.fold_boolean_expression(e2)?;

                match (e1, e2) {
                    // reduction of constants
                    (BooleanExpression::Value(v1), BooleanExpression::Value(v2)) => {
                        Ok(BooleanExpression::Value(v1 || v2))
                    }
                    // x || true == true
                    (_, BooleanExpression::Value(true)) | (BooleanExpression::Value(true), _) => {
                        Ok(BooleanExpression::Value(true))
                    }
                    // x || false == x
                    (e, BooleanExpression::Value(false)) | (BooleanExpression::Value(false), e) => {
                        Ok(e)
                    }
                    (e1, e2) => Ok(BooleanExpression::Or(box e1, box e2)),
                }
            }
            BooleanExpression::And(box e1, box e2) => {
                let e1 = self.fold_boolean_expression(e1)?;
                let e2 = self.fold_boolean_expression(e2)?;

                match (e1, e2) {
                    // reduction of constants
                    (BooleanExpression::Value(v1), BooleanExpression::Value(v2)) => {
                        Ok(BooleanExpression::Value(v1 && v2))
                    }
                    // x && true == x
                    (e, BooleanExpression::Value(true)) | (BooleanExpression::Value(true), e) => {
                        Ok(e)
                    }
                    // x && false == false
                    (_, BooleanExpression::Value(false)) | (BooleanExpression::Value(false), _) => {
                        Ok(BooleanExpression::Value(false))
                    }
                    (e1, e2) => Ok(BooleanExpression::And(box e1, box e2)),
                }
            }
            BooleanExpression::Not(box e) => {
                let e = self.fold_boolean_expression(e)?;
                match e {
                    BooleanExpression::Value(v) => Ok(BooleanExpression::Value(!v)),
                    e => Ok(BooleanExpression::Not(box e)),
                }
            }
            e => fold_boolean_expression(self, e),
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
                let e = FieldElementExpression::Add(
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                );

                assert_eq!(
                    Propagator::with_constants(&mut Constants::new()).fold_field_expression(e),
                    Ok(FieldElementExpression::Number(Bn128Field::from(5)))
                );
            }

            #[test]
            fn sub() {
                let e = FieldElementExpression::Sub(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                );

                assert_eq!(
                    Propagator::with_constants(&mut Constants::new()).fold_field_expression(e),
                    Ok(FieldElementExpression::Number(Bn128Field::from(1)))
                );
            }

            #[test]
            fn mult() {
                let e = FieldElementExpression::Mult(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                );

                assert_eq!(
                    Propagator::with_constants(&mut Constants::new()).fold_field_expression(e),
                    Ok(FieldElementExpression::Number(Bn128Field::from(6)))
                );
            }

            #[test]
            fn div() {
                let e = FieldElementExpression::Div(
                    box FieldElementExpression::Number(Bn128Field::from(6)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                );

                assert_eq!(
                    Propagator::with_constants(&mut Constants::new()).fold_field_expression(e),
                    Ok(FieldElementExpression::Number(Bn128Field::from(3)))
                );
            }

            #[test]
            fn pow() {
                let e = FieldElementExpression::Pow(
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                    box 3u32.into(),
                );

                assert_eq!(
                    Propagator::with_constants(&mut Constants::new()).fold_field_expression(e),
                    Ok(FieldElementExpression::Number(Bn128Field::from(8)))
                );
            }

            #[test]
            fn if_else_true() {
                let e = FieldElementExpression::if_else(
                    BooleanExpression::Value(true),
                    FieldElementExpression::Number(Bn128Field::from(2)),
                    FieldElementExpression::Number(Bn128Field::from(3)),
                );

                assert_eq!(
                    Propagator::with_constants(&mut Constants::new()).fold_field_expression(e),
                    Ok(FieldElementExpression::Number(Bn128Field::from(2)))
                );
            }

            #[test]
            fn if_else_false() {
                let e = FieldElementExpression::if_else(
                    BooleanExpression::Value(false),
                    FieldElementExpression::Number(Bn128Field::from(2)),
                    FieldElementExpression::Number(Bn128Field::from(3)),
                );

                assert_eq!(
                    Propagator::with_constants(&mut Constants::new()).fold_field_expression(e),
                    Ok(FieldElementExpression::Number(Bn128Field::from(3)))
                );
            }

            #[test]
            fn select() {
                let e = FieldElementExpression::select(
                    ArrayExpressionInner::Value(
                        vec![
                            FieldElementExpression::Number(Bn128Field::from(1)).into(),
                            FieldElementExpression::Number(Bn128Field::from(2)).into(),
                            FieldElementExpression::Number(Bn128Field::from(3)).into(),
                        ]
                        .into(),
                    )
                    .annotate(Type::FieldElement, 3usize),
                    UExpressionInner::Add(box 1u32.into(), box 1u32.into())
                        .annotate(UBitwidth::B32),
                );

                assert_eq!(
                    Propagator::with_constants(&mut Constants::new()).fold_field_expression(e),
                    Ok(FieldElementExpression::Number(Bn128Field::from(3)))
                );
            }
        }

        #[cfg(test)]
        mod boolean {
            use super::*;

            #[test]
            fn not() {
                let e_true: BooleanExpression<Bn128Field> =
                    BooleanExpression::Not(box BooleanExpression::Value(false));

                let e_false: BooleanExpression<Bn128Field> =
                    BooleanExpression::Not(box BooleanExpression::Value(true));

                let e_default: BooleanExpression<Bn128Field> =
                    BooleanExpression::Not(box BooleanExpression::Identifier("a".into()));

                assert_eq!(
                    Propagator::with_constants(&mut Constants::new())
                        .fold_boolean_expression(e_true),
                    Ok(BooleanExpression::Value(true))
                );
                assert_eq!(
                    Propagator::with_constants(&mut Constants::new())
                        .fold_boolean_expression(e_false),
                    Ok(BooleanExpression::Value(false))
                );
                assert_eq!(
                    Propagator::with_constants(&mut Constants::new())
                        .fold_boolean_expression(e_default.clone()),
                    Ok(e_default)
                );
            }

            #[test]
            fn field_eq() {
                let e_true = BooleanExpression::FieldEq(
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                );

                let e_false = BooleanExpression::FieldEq(
                    box FieldElementExpression::Number(Bn128Field::from(4)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                );

                assert_eq!(
                    Propagator::with_constants(&mut Constants::new())
                        .fold_boolean_expression(e_true),
                    Ok(BooleanExpression::Value(true))
                );
                assert_eq!(
                    Propagator::with_constants(&mut Constants::new())
                        .fold_boolean_expression(e_false),
                    Ok(BooleanExpression::Value(false))
                );
            }

            #[test]
            fn bool_eq() {
                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::BoolEq(
                            box BooleanExpression::Value(false),
                            box BooleanExpression::Value(false)
                        )),
                    Ok(BooleanExpression::Value(true))
                );

                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::BoolEq(
                            box BooleanExpression::Value(true),
                            box BooleanExpression::Value(true)
                        )),
                    Ok(BooleanExpression::Value(true))
                );

                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::BoolEq(
                            box BooleanExpression::Value(true),
                            box BooleanExpression::Value(false)
                        )),
                    Ok(BooleanExpression::Value(false))
                );

                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::BoolEq(
                            box BooleanExpression::Value(false),
                            box BooleanExpression::Value(true)
                        )),
                    Ok(BooleanExpression::Value(false))
                );
            }

            #[test]
            fn lt() {
                let e_true = BooleanExpression::FieldLt(
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                    box FieldElementExpression::Number(Bn128Field::from(4)),
                );

                let e_false = BooleanExpression::FieldLt(
                    box FieldElementExpression::Number(Bn128Field::from(4)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                );

                assert_eq!(
                    Propagator::with_constants(&mut Constants::new())
                        .fold_boolean_expression(e_true),
                    Ok(BooleanExpression::Value(true))
                );
                assert_eq!(
                    Propagator::with_constants(&mut Constants::new())
                        .fold_boolean_expression(e_false),
                    Ok(BooleanExpression::Value(false))
                );
            }

            #[test]
            fn le() {
                let e_true = BooleanExpression::FieldLe(
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                );

                let e_false = BooleanExpression::FieldLe(
                    box FieldElementExpression::Number(Bn128Field::from(4)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                );

                assert_eq!(
                    Propagator::with_constants(&mut Constants::new())
                        .fold_boolean_expression(e_true),
                    Ok(BooleanExpression::Value(true))
                );
                assert_eq!(
                    Propagator::with_constants(&mut Constants::new())
                        .fold_boolean_expression(e_false),
                    Ok(BooleanExpression::Value(false))
                );
            }

            #[test]
            fn gt() {
                let e_true = BooleanExpression::FieldGt(
                    box FieldElementExpression::Number(Bn128Field::from(5)),
                    box FieldElementExpression::Number(Bn128Field::from(4)),
                );

                let e_false = BooleanExpression::FieldGt(
                    box FieldElementExpression::Number(Bn128Field::from(4)),
                    box FieldElementExpression::Number(Bn128Field::from(5)),
                );

                assert_eq!(
                    Propagator::with_constants(&mut Constants::new())
                        .fold_boolean_expression(e_true),
                    Ok(BooleanExpression::Value(true))
                );
                assert_eq!(
                    Propagator::with_constants(&mut Constants::new())
                        .fold_boolean_expression(e_false),
                    Ok(BooleanExpression::Value(false))
                );
            }

            #[test]
            fn ge() {
                let e_true = BooleanExpression::FieldGe(
                    box FieldElementExpression::Number(Bn128Field::from(5)),
                    box FieldElementExpression::Number(Bn128Field::from(5)),
                );

                let e_false = BooleanExpression::FieldGe(
                    box FieldElementExpression::Number(Bn128Field::from(4)),
                    box FieldElementExpression::Number(Bn128Field::from(5)),
                );

                assert_eq!(
                    Propagator::with_constants(&mut Constants::new())
                        .fold_boolean_expression(e_true),
                    Ok(BooleanExpression::Value(true))
                );
                assert_eq!(
                    Propagator::with_constants(&mut Constants::new())
                        .fold_boolean_expression(e_false),
                    Ok(BooleanExpression::Value(false))
                );
            }

            #[test]
            fn and() {
                let a_bool: Identifier = "a".into();

                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::And(
                            box BooleanExpression::Value(true),
                            box BooleanExpression::Identifier(a_bool.clone())
                        )),
                    Ok(BooleanExpression::Identifier(a_bool.clone()))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::And(
                            box BooleanExpression::Identifier(a_bool.clone()),
                            box BooleanExpression::Value(true),
                        )),
                    Ok(BooleanExpression::Identifier(a_bool.clone()))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::And(
                            box BooleanExpression::Value(false),
                            box BooleanExpression::Identifier(a_bool.clone())
                        )),
                    Ok(BooleanExpression::Value(false))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::And(
                            box BooleanExpression::Identifier(a_bool.clone()),
                            box BooleanExpression::Value(false),
                        )),
                    Ok(BooleanExpression::Value(false))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::And(
                            box BooleanExpression::Value(true),
                            box BooleanExpression::Value(false),
                        )),
                    Ok(BooleanExpression::Value(false))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::And(
                            box BooleanExpression::Value(false),
                            box BooleanExpression::Value(true),
                        )),
                    Ok(BooleanExpression::Value(false))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::And(
                            box BooleanExpression::Value(true),
                            box BooleanExpression::Value(true),
                        )),
                    Ok(BooleanExpression::Value(true))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::And(
                            box BooleanExpression::Value(false),
                            box BooleanExpression::Value(false),
                        )),
                    Ok(BooleanExpression::Value(false))
                );
            }

            #[test]
            fn or() {
                let a_bool: Identifier = "a".into();

                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::Or(
                            box BooleanExpression::Value(true),
                            box BooleanExpression::Identifier(a_bool.clone())
                        )),
                    Ok(BooleanExpression::Value(true))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::Or(
                            box BooleanExpression::Identifier(a_bool.clone()),
                            box BooleanExpression::Value(true),
                        )),
                    Ok(BooleanExpression::Value(true))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::Or(
                            box BooleanExpression::Value(false),
                            box BooleanExpression::Identifier(a_bool.clone())
                        )),
                    Ok(BooleanExpression::Identifier(a_bool.clone()))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::Or(
                            box BooleanExpression::Identifier(a_bool.clone()),
                            box BooleanExpression::Value(false),
                        )),
                    Ok(BooleanExpression::Identifier(a_bool.clone()))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::Or(
                            box BooleanExpression::Value(true),
                            box BooleanExpression::Value(false),
                        )),
                    Ok(BooleanExpression::Value(true))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::Or(
                            box BooleanExpression::Value(false),
                            box BooleanExpression::Value(true),
                        )),
                    Ok(BooleanExpression::Value(true))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::Or(
                            box BooleanExpression::Value(true),
                            box BooleanExpression::Value(true),
                        )),
                    Ok(BooleanExpression::Value(true))
                );
                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::Or(
                            box BooleanExpression::Value(false),
                            box BooleanExpression::Value(false),
                        )),
                    Ok(BooleanExpression::Value(false))
                );
            }
        }
    }
}
