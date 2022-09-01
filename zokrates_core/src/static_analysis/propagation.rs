//! Module containing constant propagation for the typed AST
//!
//! Constant propagation on the SSA program. The constants map can be passed by the caller to allow for many passes to use
//! the same constants.
//!
//! @file propagation.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};
use std::fmt;
use zokrates_ast::common::FlatEmbed;
use zokrates_ast::typed::result_folder::*;
use zokrates_ast::typed::types::Type;
use zokrates_ast::typed::*;
use zokrates_field::Field;

pub type Constants<'ast, T> = HashMap<Identifier<'ast>, TypedExpression<'ast, T>>;

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    Type(String),
    AssertionFailed(String),
    ValueTooLarge(String),
    OutOfBounds(u128, u128),
    NonConstantExponent(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Type(s) => write!(f, "{}", s),
            Error::AssertionFailed(s) => write!(f, "{}", s),
            Error::ValueTooLarge(s) => write!(f, "{}", s),
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

#[derive(Debug)]
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
                match self.try_get_constant_mut(assignee) {
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
            TypedAssignee::Member(box assignee, m) => match self.try_get_constant_mut(assignee) {
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
            TypedAssignee::Element(box assignee, index) => {
                match self.try_get_constant_mut(assignee) {
                    Ok((v, c)) => match c {
                        TypedExpression::Tuple(a) => match a.as_inner_mut() {
                            TupleExpressionInner::Value(value) => {
                                Ok((v, &mut value[*index as usize]))
                            }
                            _ => unreachable!("should be a tuple value"),
                        },
                        _ => unreachable!("should be a tuple expression"),
                    },
                    e => e,
                }
            }
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

    fn fold_function(
        &mut self,
        f: TypedFunction<'ast, T>,
    ) -> Result<TypedFunction<'ast, T>, Error> {
        fold_function(self, f)
    }

    fn fold_conditional_expression<
        E: Expr<'ast, T> + Conditional<'ast, T> + PartialEq + ResultFold<'ast, T>,
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
                (BooleanExpression::Value(true), consequence, _) => {
                    ConditionalOrExpression::Expression(consequence.into_inner())
                }
                (BooleanExpression::Value(false), _, alternative) => {
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

    fn fold_statement(
        &mut self,
        s: TypedStatement<'ast, T>,
    ) -> Result<Vec<TypedStatement<'ast, T>>, Error> {
        match s {
            // propagation to the defined variable if rhs is a constant
            TypedStatement::Definition(assignee, DefinitionRhs::Expression(expr)) => {
                let assignee = self.fold_assignee(assignee)?;
                let expr = self.fold_expression(expr)?;

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
                                    TypedStatement::Definition(v.clone().into(), c.into()),
                                    TypedStatement::Definition(assignee, expr.into()),
                                ]),
                                None => Ok(vec![TypedStatement::Definition(assignee, expr.into())]),
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
                            TypedStatement::Definition(v.clone().into(), c.into()),
                            TypedStatement::Definition(assignee, expr.into()),
                        ]),
                        None => Ok(vec![TypedStatement::Definition(assignee, expr.into())]),
                    }
                }
            }
            // we do not visit the for-loop statements
            TypedStatement::For(v, from, to, statements) => {
                let from = self.fold_uint_expression(from)?;
                let to = self.fold_uint_expression(to)?;

                Ok(vec![TypedStatement::For(v, from, to, statements)])
            }
            TypedStatement::Definition(assignee, DefinitionRhs::EmbedCall(embed_call)) => {
                let assignee = self.fold_assignee(assignee)?;
                let embed_call = self.fold_embed_call(embed_call)?;

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
                    arguments: &[TypedExpression<'ast, T>],
                    bitwidth: UBitwidth,
                ) -> TypedExpression<'ast, T> {
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

                match embed_call.arguments.iter().all(|a| a.is_constant()) {
                    true => {
                        let r: Option<TypedExpression<'ast, T>> = match embed_call.embed {
                            FlatEmbed::BitArrayLe => Ok(None), // todo
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
                                    FieldElementExpression::Number(num) => {
                                        let mut acc = num.clone();
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
                                            Err(Error::ValueTooLarge(format!(
                                                "Cannot unpack `{}` to `{}`: value is too large",
                                                num,
                                                assignee.get_type()
                                            )))
                                        } else {
                                            Ok(Some(
                                                ArrayExpressionInner::Value(
                                                    res.into_iter()
                                                        .map(|v| BooleanExpression::Value(v).into())
                                                        .collect::<Vec<_>>()
                                                        .into(),
                                                )
                                                .annotate(Type::Boolean, bit_width)
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
                                            TypedStatement::Definition(v.clone().into(), c.into()),
                                            TypedStatement::Definition(assignee, expr.into()),
                                        ],
                                        None => {
                                            vec![TypedStatement::Definition(assignee, expr.into())]
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
                                        TypedStatement::Definition(v.clone().into(), c.into()),
                                        TypedStatement::Definition(assignee, embed_call.into()),
                                    ],
                                    None => vec![TypedStatement::Definition(
                                        assignee,
                                        embed_call.into(),
                                    )],
                                }
                            }
                        })
                    }
                    false => {
                        // if the function arguments are not constant, invalidate the cache
                        // for the return assignees
                        let def = TypedStatement::Definition(assignee.clone(), embed_call.into());

                        let v = self
                            .try_get_constant_mut(&assignee)
                            .map(|(v, _)| v)
                            .unwrap_or_else(|v| v);

                        Ok(match self.constants.remove(&v.id) {
                            Some(c) => {
                                vec![TypedStatement::Definition(v.clone().into(), c.into()), def]
                            }
                            None => vec![def],
                        })
                    }
                }
            }
            TypedStatement::Assertion(e, ty) => {
                let e_str = e.to_string();
                let expr = self.fold_boolean_expression(e)?;
                match expr {
                    BooleanExpression::Value(false) => {
                        Err(Error::AssertionFailed(format!("{}: ({})", ty, e_str)))
                    }
                    BooleanExpression::Value(true) => Ok(vec![]),
                    _ => Ok(vec![TypedStatement::Assertion(expr, ty)]),
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
        let array = self.fold_array_expression(*e.array)?;
        let index = self.fold_uint_expression(*e.index)?;

        let inner_type = array.inner_type().clone();
        let size = array.size();

        match size.into_inner() {
            UExpressionInner::Value(size) => match (array.into_inner(), index.into_inner()) {
                (ArrayExpressionInner::Value(v), UExpressionInner::Value(n)) => {
                    if n < size {
                        Ok(SelectOrExpression::Expression(
                            v.expression_at::<E>(n as usize).unwrap().into_inner(),
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
                                        v.expression_at::<E>(n as usize).unwrap().into_inner(),
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

    fn fold_tuple_expression_inner(
        &mut self,
        ty: &TupleType<'ast, T>,
        e: TupleExpressionInner<'ast, T>,
    ) -> Result<TupleExpressionInner<'ast, T>, Error> {
        match e {
            TupleExpressionInner::Identifier(id) => match self.constants.get(&id) {
                Some(e) => match e {
                    TypedExpression::Tuple(e) => Ok(e.as_inner().clone()),
                    _ => panic!("constant stored for an tuple should be an tuple"),
                },
                None => Ok(TupleExpressionInner::Identifier(id)),
            },
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
            e => fold_tuple_expression_inner(self, ty, e),
        }
    }

    fn fold_eq_expression<
        E: Expr<'ast, T> + PartialEq + Constant + Typed<'ast, T> + ResultFold<'ast, T>,
    >(
        &mut self,
        e: EqExpression<E>,
    ) -> Result<EqOrBoolean<'ast, T, E>, Self::Error> {
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
            return Ok(EqOrBoolean::Boolean(BooleanExpression::Value(true)));
        }

        // if both expressions are constant, we can reduce the equality check after we put them in canonical form
        if left.is_constant() && right.is_constant() {
            let left = left.into_canonical_constant();
            let right = right.into_canonical_constant();
            Ok(EqOrBoolean::Boolean(BooleanExpression::Value(
                left == right,
            )))
        } else {
            Ok(EqOrBoolean::Eq(EqExpression::new(left, right)))
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
                let e = FieldElementExpression::conditional(
                    BooleanExpression::Value(true),
                    FieldElementExpression::Number(Bn128Field::from(2)),
                    FieldElementExpression::Number(Bn128Field::from(3)),
                    ConditionalKind::IfElse,
                );

                assert_eq!(
                    Propagator::with_constants(&mut Constants::new()).fold_field_expression(e),
                    Ok(FieldElementExpression::Number(Bn128Field::from(2)))
                );
            }

            #[test]
            fn if_else_false() {
                let e = FieldElementExpression::conditional(
                    BooleanExpression::Value(false),
                    FieldElementExpression::Number(Bn128Field::from(2)),
                    FieldElementExpression::Number(Bn128Field::from(3)),
                    ConditionalKind::IfElse,
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
                    .annotate(Type::FieldElement, 3u32),
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
                let e_constant_true = BooleanExpression::FieldEq(EqExpression::new(
                    FieldElementExpression::Number(Bn128Field::from(2)),
                    FieldElementExpression::Number(Bn128Field::from(2)),
                ));

                let e_constant_false = BooleanExpression::FieldEq(EqExpression::new(
                    FieldElementExpression::Number(Bn128Field::from(4)),
                    FieldElementExpression::Number(Bn128Field::from(2)),
                ));

                let e_identifier_true: BooleanExpression<Bn128Field> =
                    BooleanExpression::FieldEq(EqExpression::new(
                        FieldElementExpression::Identifier("a".into()),
                        FieldElementExpression::Identifier("a".into()),
                    ));

                let e_identifier_unchanged: BooleanExpression<Bn128Field> =
                    BooleanExpression::FieldEq(EqExpression::new(
                        FieldElementExpression::Identifier("a".into()),
                        FieldElementExpression::Identifier("b".into()),
                    ));

                assert_eq!(
                    Propagator::with_constants(&mut Constants::new())
                        .fold_boolean_expression(e_constant_true),
                    Ok(BooleanExpression::Value(true))
                );
                assert_eq!(
                    Propagator::with_constants(&mut Constants::new())
                        .fold_boolean_expression(e_constant_false),
                    Ok(BooleanExpression::Value(false))
                );
                assert_eq!(
                    Propagator::with_constants(&mut Constants::new())
                        .fold_boolean_expression(e_identifier_true),
                    Ok(BooleanExpression::Value(true))
                );
                assert_eq!(
                    Propagator::with_constants(&mut Constants::new())
                        .fold_boolean_expression(e_identifier_unchanged.clone()),
                    Ok(e_identifier_unchanged)
                );
            }

            #[test]
            fn bool_eq() {
                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::BoolEq(EqExpression::new(
                            BooleanExpression::Value(false),
                            BooleanExpression::Value(false)
                        ))),
                    Ok(BooleanExpression::Value(true))
                );

                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::BoolEq(EqExpression::new(
                            BooleanExpression::Value(true),
                            BooleanExpression::Value(true)
                        ))),
                    Ok(BooleanExpression::Value(true))
                );

                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::BoolEq(EqExpression::new(
                            BooleanExpression::Value(true),
                            BooleanExpression::Value(false)
                        ))),
                    Ok(BooleanExpression::Value(false))
                );

                assert_eq!(
                    Propagator::<Bn128Field>::with_constants(&mut Constants::new())
                        .fold_boolean_expression(BooleanExpression::BoolEq(EqExpression::new(
                            BooleanExpression::Value(false),
                            BooleanExpression::Value(true)
                        ))),
                    Ok(BooleanExpression::Value(false))
                );
            }

            #[test]
            fn array_eq() {
                let e_constant_true = BooleanExpression::ArrayEq(EqExpression::new(
                    ArrayExpressionInner::Value(
                        vec![TypedExpressionOrSpread::Expression(
                            FieldElementExpression::Number(Bn128Field::from(2usize)).into(),
                        )]
                        .into(),
                    )
                    .annotate(Type::FieldElement, 1u32),
                    ArrayExpressionInner::Value(
                        vec![TypedExpressionOrSpread::Expression(
                            FieldElementExpression::Number(Bn128Field::from(2usize)).into(),
                        )]
                        .into(),
                    )
                    .annotate(Type::FieldElement, 1u32),
                ));

                let e_constant_false = BooleanExpression::ArrayEq(EqExpression::new(
                    ArrayExpressionInner::Value(
                        vec![TypedExpressionOrSpread::Expression(
                            FieldElementExpression::Number(Bn128Field::from(2usize)).into(),
                        )]
                        .into(),
                    )
                    .annotate(Type::FieldElement, 1u32),
                    ArrayExpressionInner::Value(
                        vec![TypedExpressionOrSpread::Expression(
                            FieldElementExpression::Number(Bn128Field::from(4usize)).into(),
                        )]
                        .into(),
                    )
                    .annotate(Type::FieldElement, 1u32),
                ));

                let e_identifier_true: BooleanExpression<Bn128Field> =
                    BooleanExpression::ArrayEq(EqExpression::new(
                        ArrayExpressionInner::Identifier("a".into())
                            .annotate(Type::FieldElement, 1u32),
                        ArrayExpressionInner::Identifier("a".into())
                            .annotate(Type::FieldElement, 1u32),
                    ));

                let e_identifier_unchanged: BooleanExpression<Bn128Field> =
                    BooleanExpression::ArrayEq(EqExpression::new(
                        ArrayExpressionInner::Identifier("a".into())
                            .annotate(Type::FieldElement, 1u32),
                        ArrayExpressionInner::Identifier("b".into())
                            .annotate(Type::FieldElement, 1u32),
                    ));

                let e_non_canonical_true = BooleanExpression::ArrayEq(EqExpression::new(
                    ArrayExpressionInner::Value(
                        vec![TypedExpressionOrSpread::Spread(
                            ArrayExpressionInner::Value(
                                vec![TypedExpressionOrSpread::Expression(
                                    FieldElementExpression::Number(Bn128Field::from(2usize)).into(),
                                )]
                                .into(),
                            )
                            .annotate(Type::FieldElement, 1u32)
                            .into(),
                        )]
                        .into(),
                    )
                    .annotate(Type::FieldElement, 1u32),
                    ArrayExpressionInner::Value(
                        vec![TypedExpressionOrSpread::Expression(
                            FieldElementExpression::Number(Bn128Field::from(2usize)).into(),
                        )]
                        .into(),
                    )
                    .annotate(Type::FieldElement, 1u32),
                ));

                let e_non_canonical_false = BooleanExpression::ArrayEq(EqExpression::new(
                    ArrayExpressionInner::Value(
                        vec![TypedExpressionOrSpread::Spread(
                            ArrayExpressionInner::Value(
                                vec![TypedExpressionOrSpread::Expression(
                                    FieldElementExpression::Number(Bn128Field::from(2usize)).into(),
                                )]
                                .into(),
                            )
                            .annotate(Type::FieldElement, 1u32)
                            .into(),
                        )]
                        .into(),
                    )
                    .annotate(Type::FieldElement, 1u32),
                    ArrayExpressionInner::Value(
                        vec![TypedExpressionOrSpread::Expression(
                            FieldElementExpression::Number(Bn128Field::from(4usize)).into(),
                        )]
                        .into(),
                    )
                    .annotate(Type::FieldElement, 1u32),
                ));

                assert_eq!(
                    Propagator::with_constants(&mut Constants::new())
                        .fold_boolean_expression(e_constant_true),
                    Ok(BooleanExpression::Value(true))
                );
                assert_eq!(
                    Propagator::with_constants(&mut Constants::new())
                        .fold_boolean_expression(e_constant_false),
                    Ok(BooleanExpression::Value(false))
                );
                assert_eq!(
                    Propagator::with_constants(&mut Constants::new())
                        .fold_boolean_expression(e_identifier_true),
                    Ok(BooleanExpression::Value(true))
                );
                assert_eq!(
                    Propagator::with_constants(&mut Constants::new())
                        .fold_boolean_expression(e_identifier_unchanged.clone()),
                    Ok(e_identifier_unchanged)
                );
                assert_eq!(
                    Propagator::with_constants(&mut Constants::new())
                        .fold_boolean_expression(e_non_canonical_true),
                    Ok(BooleanExpression::Value(true))
                );
                assert_eq!(
                    Propagator::with_constants(&mut Constants::new())
                        .fold_boolean_expression(e_non_canonical_false),
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
