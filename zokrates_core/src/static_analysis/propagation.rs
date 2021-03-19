//! Module containing constant propagation for the typed AST
//!
//! On top of the usual behavior of removing statements which assign a constant to a variable (as the variable can simply be
//! substituted for the constant whenever used), we provide a `verbose` mode which does not remove such statements. This is done
//! as for partial passes which do not visit the whole program, the variables being defined may be be used in parts of the program
//! that are not visited. Keeping the statements is semantically equivalent and enables rebuilding the set of constants at the
//! next pass.
//!
//! @file propagation.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use crate::typed_absy::folder::*;
use crate::typed_absy::types::Type;
use crate::typed_absy::*;
use std::collections::HashMap;
use std::convert::TryFrom;
use zokrates_field::Field;

pub struct Propagator<'ast, T: Field> {
    // constants keeps track of constant expressions
    // we currently do not support partially constant expressions: `field [x, 1][1]` is not considered constant, `field [0, 1][1]` is
    constants: HashMap<Identifier<'ast>, TypedExpression<'ast, T>>,
    // the verbose mode doesn't remove statements which assign constants to variables
    // it's required when using propagation in combination with unrolling
    verbose: bool,
}

impl<'ast, T: Field> Propagator<'ast, T> {
    fn verbose() -> Self {
        Propagator {
            constants: HashMap::new(),
            verbose: true,
        }
    }

    fn new() -> Self {
        Propagator {
            constants: HashMap::new(),
            verbose: false,
        }
    }

    pub fn propagate(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        Propagator::new().fold_program(p)
    }

    pub fn propagate_verbose(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        Propagator::verbose().fold_program(p)
    }

    // get a mutable reference to the constant corresponding to a given assignee if any, otherwise
    // return the identifier at the root of this assignee
    fn try_get_constant_mut<'a>(
        &mut self,
        assignee: &'a TypedAssignee<'ast, T>,
    ) -> Result<(&'a Variable<'ast>, &mut TypedExpression<'ast, T>), &'a Variable<'ast>> {
        match assignee {
            TypedAssignee::Identifier(var) => self
                .constants
                .get_mut(&var.id)
                .map(|c| Ok((var, c)))
                .unwrap_or(Err(var)),
            TypedAssignee::Select(box assignee, box index) => {
                match self.try_get_constant_mut(&assignee) {
                    Ok((v, c)) => match index {
                        FieldElementExpression::Number(n) => {
                            let n = n.to_dec_string().parse::<usize>().unwrap();

                            match c {
                                TypedExpression::Array(a) => match a.as_inner_mut() {
                                    ArrayExpressionInner::Value(value) => Ok((v, &mut value[n])),
                                    _ => unreachable!(),
                                },
                                _ => unreachable!(),
                            }
                        }
                        _ => Err(v),
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
                        _ => unreachable!(),
                    };

                    match c {
                        TypedExpression::Struct(a) => match a.as_inner_mut() {
                            StructExpressionInner::Value(value) => Ok((v, &mut value[index])),
                            _ => unreachable!(),
                        },
                        _ => unreachable!(),
                    }
                }
                e => e,
            },
        }
    }
}

fn is_constant<'ast, T: Field>(e: &TypedExpression<'ast, T>) -> bool {
    match e {
        TypedExpression::FieldElement(FieldElementExpression::Number(..)) => true,
        TypedExpression::Boolean(BooleanExpression::Value(..)) => true,
        TypedExpression::Array(a) => match a.as_inner() {
            ArrayExpressionInner::Value(v) => v.iter().all(|e| is_constant(e)),
            _ => false,
        },
        TypedExpression::Struct(a) => match a.as_inner() {
            StructExpressionInner::Value(v) => v.iter().all(|e| is_constant(e)),
            _ => false,
        },
        TypedExpression::Uint(a) => match a.as_inner() {
            UExpressionInner::Value(..) => true,
            _ => false,
        },
        _ => false,
    }
}

impl<'ast, T: Field> Folder<'ast, T> for Propagator<'ast, T> {
    fn fold_function(&mut self, f: TypedFunction<'ast, T>) -> TypedFunction<'ast, T> {
        self.constants = HashMap::new();
        fold_function(self, f)
    }

    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        let res = match s {
            TypedStatement::Declaration(v) => vec![TypedStatement::Declaration(v)],
            TypedStatement::Return(expressions) => vec![TypedStatement::Return(
                expressions
                    .into_iter()
                    .map(|e| self.fold_expression(e))
                    .collect(),
            )],
            // propagation to the defined variable if rhs is a constant
            TypedStatement::Definition(assignee, expr) => {
                let expr = self.fold_expression(expr);
                let assignee = self.fold_assignee(assignee);

                if is_constant(&expr) {
                    let verbose = self.verbose;

                    match assignee {
                        TypedAssignee::Identifier(var) => match verbose {
                            true => {
                                assert!(self
                                    .constants
                                    .insert(var.id.clone(), expr.clone())
                                    .is_none());
                                vec![TypedStatement::Definition(
                                    TypedAssignee::Identifier(var),
                                    expr,
                                )]
                            }
                            false => {
                                assert!(self.constants.insert(var.id, expr).is_none());

                                vec![]
                            }
                        },
                        assignee => match self.try_get_constant_mut(&assignee) {
                            Ok((_, c)) => match verbose {
                                true => {
                                    *c = expr.clone();
                                    vec![TypedStatement::Definition(assignee, expr)]
                                }
                                false => {
                                    *c = expr;
                                    vec![]
                                }
                            },
                            Err(v) => match self.constants.remove(&v.id) {
                                // invalidate the cache for this identifier, and define the latest
                                // version of the constant in the program, if any
                                Some(c) => vec![
                                    TypedStatement::Definition(v.clone().into(), c),
                                    TypedStatement::Definition(assignee, expr),
                                ],
                                None => vec![TypedStatement::Definition(assignee, expr)],
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
                        Some(c) => vec![
                            TypedStatement::Definition(v.clone().into(), c),
                            TypedStatement::Definition(assignee, expr),
                        ],
                        None => vec![TypedStatement::Definition(assignee, expr)],
                    }
                }
            }
            // propagate the boolean
            TypedStatement::Assertion(e) => {
                // could stop execution here if condition is known to fail
                vec![TypedStatement::Assertion(self.fold_boolean_expression(e))]
            }
            // only loops with variable bounds are expected here
            // we stop propagation here as constants maybe be modified inside the loop body
            // which we do not visit
            TypedStatement::For(v, from, to, statements) => {
                let from = self.fold_field_expression(from);
                let to = self.fold_field_expression(to);

                // invalidate the constants map as any constant could be modified inside the loop body, which we don't visit
                self.constants.clear();

                vec![TypedStatement::For(v, from, to, statements)]
            }
            TypedStatement::MultipleDefinition(assignees, expression_list) => {
                let assignees: Vec<TypedAssignee<'ast, T>> = assignees
                    .into_iter()
                    .map(|a| self.fold_assignee(a))
                    .collect();
                let expression_list = self.fold_expression_list(expression_list);

                match expression_list {
                    TypedExpressionList::FunctionCall(key, arguments, types) => {
                        let arguments: Vec<_> = arguments
                            .into_iter()
                            .map(|a| self.fold_expression(a))
                            .collect();

                        fn process_u_from_bits<'ast, T: Field>(
                            variables: Vec<TypedAssignee<'ast, T>>,
                            arguments: Vec<TypedExpression<'ast, T>>,
                            bitwidth: UBitwidth,
                        ) -> TypedExpression<'ast, T> {
                            assert_eq!(variables.len(), 1);
                            assert_eq!(arguments.len(), 1);

                            use std::convert::TryInto;

                            match ArrayExpression::try_from(arguments[0].clone())
                                .unwrap()
                                .into_inner()
                            {
                                ArrayExpressionInner::Value(v) => {
                                    assert_eq!(v.len(), bitwidth.to_usize());
                                    UExpressionInner::Value(
                                        v.into_iter()
                                            .map(|v| match v {
                                                TypedExpression::Boolean(
                                                    BooleanExpression::Value(v),
                                                ) => v,
                                                _ => unreachable!("should be a boolean value"),
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
                                    .into()
                                }
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
                                            num = num - 2u128.pow(i);
                                            res.push(true);
                                        } else {
                                            res.push(false);
                                        }
                                    }
                                    assert_eq!(num, 0);

                                    ArrayExpressionInner::Value(
                                        res.into_iter()
                                            .map(|v| BooleanExpression::Value(v).into())
                                            .collect(),
                                    )
                                    .annotate(Type::Boolean, bitwidth.to_usize())
                                    .into()
                                }
                                _ => unreachable!("should be a uint value"),
                            }
                        }

                        match arguments.iter().all(|a| is_constant(a)) {
                            true => {
                                let r: Option<TypedExpression<'ast, T>> = match key.id {
                                    "_U32_FROM_BITS" => Some(process_u_from_bits(
                                        assignees.clone(),
                                        arguments.clone(),
                                        UBitwidth::B32,
                                    )),
                                    "_U16_FROM_BITS" => Some(process_u_from_bits(
                                        assignees.clone(),
                                        arguments.clone(),
                                        UBitwidth::B16,
                                    )),
                                    "_U8_FROM_BITS" => Some(process_u_from_bits(
                                        assignees.clone(),
                                        arguments.clone(),
                                        UBitwidth::B8,
                                    )),
                                    "_U32_TO_BITS" => Some(process_u_to_bits(
                                        assignees.clone(),
                                        arguments.clone(),
                                        UBitwidth::B32,
                                    )),
                                    "_U16_TO_BITS" => Some(process_u_to_bits(
                                        assignees.clone(),
                                        arguments.clone(),
                                        UBitwidth::B16,
                                    )),
                                    "_U8_TO_BITS" => Some(process_u_to_bits(
                                        assignees.clone(),
                                        arguments.clone(),
                                        UBitwidth::B8,
                                    )),
                                    "_UNPACK" => {
                                        assert_eq!(assignees.len(), 1);
                                        assert_eq!(arguments.len(), 1);

                                        match FieldElementExpression::try_from(arguments[0].clone())
                                            .unwrap()
                                        {
                                            FieldElementExpression::Number(num) => {
                                                let mut num = num;
                                                let mut res = vec![];

                                                for i in (0..T::get_required_bits()).rev() {
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
                                                            .collect(),
                                                    )
                                                    .annotate(Type::Boolean, T::get_required_bits())
                                                    .into(),
                                                )
                                            }
                                            _ => unreachable!("should be a field value"),
                                        }
                                    }
                                    "_SHA256_ROUND" => None,
                                    _ => None,
                                };

                                match r {
                                    // if the function call returns a constant
                                    Some(expr) => {
                                        let verbose = self.verbose;

                                        let mut assignees = assignees;

                                        match assignees.pop().unwrap() {
                                            TypedAssignee::Identifier(var) => match verbose {
                                                true => {
                                                    self.constants
                                                        .insert(var.id.clone(), expr.clone());
                                                    vec![TypedStatement::Definition(
                                                        TypedAssignee::Identifier(var),
                                                        expr,
                                                    )]
                                                }
                                                false => {
                                                    self.constants.insert(var.id, expr);

                                                    vec![]
                                                }
                                            },
                                            assignee => {
                                                match self.try_get_constant_mut(&assignee) {
                                                    Ok((_, c)) => match verbose {
                                                        true => {
                                                            *c = expr.clone();
                                                            vec![TypedStatement::Definition(
                                                                assignee, expr,
                                                            )]
                                                        }
                                                        false => {
                                                            *c = expr;
                                                            vec![]
                                                        }
                                                    },
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
                                                    TypedExpressionList::FunctionCall(
                                                        key, arguments, types,
                                                    ),
                                                ),
                                            ],
                                            None => vec![TypedStatement::MultipleDefinition(
                                                vec![assignee],
                                                TypedExpressionList::FunctionCall(
                                                    key, arguments, types,
                                                ),
                                            )],
                                        }
                                    }
                                }
                            }
                            false => {
                                // if the function arguments are not constant, invalidate the cache
                                // for the return assignees

                                let invalidations = assignees
                                    .iter()
                                    .flat_map(|assignee| {
                                        let v = self
                                            .try_get_constant_mut(&assignee)
                                            .map(|(v, _)| v)
                                            .unwrap_or_else(|v| v);
                                        match self.constants.remove(&v.id) {
                                            Some(c) => vec![TypedStatement::Definition(
                                                v.clone().into(),
                                                c,
                                            )],
                                            None => vec![],
                                        }
                                    })
                                    .collect::<Vec<_>>();

                                let l = TypedExpressionList::FunctionCall(key, arguments, types);
                                invalidations
                                    .into_iter()
                                    .chain(std::iter::once(TypedStatement::MultipleDefinition(
                                        assignees, l,
                                    )))
                                    .collect()
                            }
                        }
                    }
                }
            }
        };

        // In verbose mode, we always return at least a statement
        assert!(res.len() > 0 || !self.verbose);

        res
    }

    fn fold_uint_expression_inner(
        &mut self,
        bitwidth: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> UExpressionInner<'ast, T> {
        match e {
            UExpressionInner::Identifier(id) => match self.constants.get(&id) {
                Some(e) => match e {
                    TypedExpression::Uint(e) => e.as_inner().clone(),
                    _ => unreachable!("constant stored for a uint should be a uint"),
                },
                None => UExpressionInner::Identifier(id),
            },
            UExpressionInner::Add(box e1, box e2) => match (
                self.fold_uint_expression(e1).into_inner(),
                self.fold_uint_expression(e2).into_inner(),
            ) {
                (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                    use std::convert::TryInto;
                    UExpressionInner::Value(
                        (v1 + v2) % 2_u128.pow(bitwidth.to_usize().try_into().unwrap()),
                    )
                }
                (e, UExpressionInner::Value(v)) | (UExpressionInner::Value(v), e) => match v {
                    0 => e,
                    _ => UExpressionInner::Add(
                        box e.annotate(bitwidth),
                        box UExpressionInner::Value(v).annotate(bitwidth),
                    ),
                },
                (e1, e2) => {
                    UExpressionInner::Add(box e1.annotate(bitwidth), box e2.annotate(bitwidth))
                }
            },
            UExpressionInner::Sub(box e1, box e2) => match (
                self.fold_uint_expression(e1).into_inner(),
                self.fold_uint_expression(e2).into_inner(),
            ) {
                (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                    use std::convert::TryInto;
                    UExpressionInner::Value(
                        (v1.wrapping_sub(v2)) % 2_u128.pow(bitwidth.to_usize().try_into().unwrap()),
                    )
                }
                (e, UExpressionInner::Value(v)) | (UExpressionInner::Value(v), e) => match v {
                    0 => e,
                    _ => UExpressionInner::Sub(
                        box e.annotate(bitwidth),
                        box UExpressionInner::Value(v).annotate(bitwidth),
                    ),
                },
                (e1, e2) => {
                    UExpressionInner::Sub(box e1.annotate(bitwidth), box e2.annotate(bitwidth))
                }
            },
            UExpressionInner::Mult(box e1, box e2) => match (
                self.fold_uint_expression(e1).into_inner(),
                self.fold_uint_expression(e2).into_inner(),
            ) {
                (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                    use std::convert::TryInto;
                    UExpressionInner::Value(
                        (v1 * v2) % 2_u128.pow(bitwidth.to_usize().try_into().unwrap()),
                    )
                }
                (e, UExpressionInner::Value(v)) | (UExpressionInner::Value(v), e) => match v {
                    0 => UExpressionInner::Value(0),
                    1 => e,
                    _ => UExpressionInner::Mult(
                        box e.annotate(bitwidth),
                        box UExpressionInner::Value(v).annotate(bitwidth),
                    ),
                },
                (e1, e2) => {
                    UExpressionInner::Mult(box e1.annotate(bitwidth), box e2.annotate(bitwidth))
                }
            },
            UExpressionInner::Div(box e1, box e2) => match (
                self.fold_uint_expression(e1).into_inner(),
                self.fold_uint_expression(e2).into_inner(),
            ) {
                (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                    use std::convert::TryInto;
                    UExpressionInner::Value(
                        (v1 / v2) % 2_u128.pow(bitwidth.to_usize().try_into().unwrap()),
                    )
                }
                (e, UExpressionInner::Value(v)) => match v {
                    1 => e,
                    _ => UExpressionInner::Div(
                        box e.annotate(bitwidth),
                        box UExpressionInner::Value(v).annotate(bitwidth),
                    ),
                },
                (e1, e2) => {
                    UExpressionInner::Div(box e1.annotate(bitwidth), box e2.annotate(bitwidth))
                }
            },
            UExpressionInner::Rem(box e1, box e2) => match (
                self.fold_uint_expression(e1).into_inner(),
                self.fold_uint_expression(e2).into_inner(),
            ) {
                (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                    use std::convert::TryInto;
                    UExpressionInner::Value(
                        (v1 % v2) % 2_u128.pow(bitwidth.to_usize().try_into().unwrap()),
                    )
                }
                (e, UExpressionInner::Value(v)) => match v {
                    1 => UExpressionInner::Value(0),
                    _ => UExpressionInner::Rem(
                        box e.annotate(bitwidth),
                        box UExpressionInner::Value(v).annotate(bitwidth),
                    ),
                },
                (e1, e2) => {
                    UExpressionInner::Rem(box e1.annotate(bitwidth), box e2.annotate(bitwidth))
                }
            },
            UExpressionInner::RightShift(box e, box by) => {
                let e = self.fold_uint_expression(e);
                let by = self.fold_field_expression(by);
                match (e.into_inner(), by) {
                    (UExpressionInner::Value(v), FieldElementExpression::Number(by)) => {
                        let by_as_usize = by.to_dec_string().parse::<usize>().unwrap();
                        UExpressionInner::Value(v >> by_as_usize)
                    }
                    (e, FieldElementExpression::Number(by)) => UExpressionInner::RightShift(
                        box e.annotate(bitwidth),
                        box FieldElementExpression::Number(by),
                    ),
                    (_, e2) => unreachable!(format!(
                        "non-constant shift {} detected during static analysis",
                        e2
                    )),
                }
            }
            UExpressionInner::LeftShift(box e, box by) => {
                let e = self.fold_uint_expression(e);
                let by = self.fold_field_expression(by);
                match (e.into_inner(), by) {
                    (UExpressionInner::Value(v), FieldElementExpression::Number(by)) => {
                        let by_as_usize = by.to_dec_string().parse::<usize>().unwrap();
                        UExpressionInner::Value((v << by_as_usize) & 0xffffffff)
                    }
                    (e, FieldElementExpression::Number(by)) => UExpressionInner::LeftShift(
                        box e.annotate(bitwidth),
                        box FieldElementExpression::Number(by),
                    ),
                    (_, e2) => unreachable!(format!(
                        "non-constant shift {} detected during static analysis",
                        e2
                    )),
                }
            }
            UExpressionInner::Xor(box e1, box e2) => match (
                self.fold_uint_expression(e1).into_inner(),
                self.fold_uint_expression(e2).into_inner(),
            ) {
                (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                    UExpressionInner::Value(v1 ^ v2)
                }
                (UExpressionInner::Value(0), e2) => e2,
                (e1, UExpressionInner::Value(0)) => e1,
                (e1, e2) => {
                    if e1 == e2 {
                        UExpressionInner::Value(0)
                    } else {
                        UExpressionInner::Xor(box e1.annotate(bitwidth), box e2.annotate(bitwidth))
                    }
                }
            },
            UExpressionInner::And(box e1, box e2) => match (
                self.fold_uint_expression(e1).into_inner(),
                self.fold_uint_expression(e2).into_inner(),
            ) {
                (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                    UExpressionInner::Value(v1 & v2)
                }
                (UExpressionInner::Value(0), _) | (_, UExpressionInner::Value(0)) => {
                    UExpressionInner::Value(0)
                }
                (e1, e2) => {
                    UExpressionInner::And(box e1.annotate(bitwidth), box e2.annotate(bitwidth))
                }
            },
            UExpressionInner::IfElse(box condition, box consequence, box alternative) => {
                let consequence = self.fold_uint_expression(consequence);
                let alternative = self.fold_uint_expression(alternative);
                match self.fold_boolean_expression(condition) {
                    BooleanExpression::Value(true) => consequence.into_inner(),
                    BooleanExpression::Value(false) => alternative.into_inner(),
                    c => UExpressionInner::IfElse(box c, box consequence, box alternative),
                }
            }
            UExpressionInner::Not(box e) => {
                let e = self.fold_uint_expression(e).into_inner();
                match e {
                    UExpressionInner::Value(v) => UExpressionInner::Value((!v) & 0xffffffff),
                    e => UExpressionInner::Not(box e.annotate(bitwidth)),
                }
            }
            UExpressionInner::Select(box array, box index) => {
                let array = self.fold_array_expression(array);
                let index = self.fold_field_expression(index);

                let inner_type = array.inner_type().clone();
                let size = array.size();

                match (array.into_inner(), index) {
                    (ArrayExpressionInner::Value(v), FieldElementExpression::Number(n)) => {
                        let n_as_usize = n.to_dec_string().parse::<usize>().unwrap();
                        if n_as_usize < size {
                            UExpression::try_from(v[n_as_usize].clone())
                                .unwrap()
                                .into_inner()
                        } else {
                            unreachable!(
                                "out of bounds index ({} >= {}) found during static analysis",
                                n_as_usize, size
                            );
                        }
                    }
                    (ArrayExpressionInner::Identifier(id), FieldElementExpression::Number(n)) => {
                        match self.constants.get(&id) {
                            Some(a) => match a {
                                TypedExpression::Array(a) => match a.as_inner() {
                                    ArrayExpressionInner::Value(v) => UExpression::try_from(
                                        v[n.to_dec_string().parse::<usize>().unwrap()].clone(),
                                    )
                                    .unwrap()
                                    .into_inner(),
                                    _ => unreachable!(),
                                },
                                _ => unreachable!(""),
                            },
                            None => UExpressionInner::Select(
                                box ArrayExpressionInner::Identifier(id).annotate(inner_type, size),
                                box FieldElementExpression::Number(n),
                            ),
                        }
                    }
                    (a, i) => UExpressionInner::Select(box a.annotate(inner_type, size), box i),
                }
            }
            UExpressionInner::FunctionCall(key, arguments) => {
                assert!(
                    self.verbose,
                    "function calls should only exist out of multidef in verbose mode"
                );
                fold_uint_expression_inner(
                    self,
                    bitwidth,
                    UExpressionInner::FunctionCall(key, arguments),
                )
            }
            e => fold_uint_expression_inner(self, bitwidth, e),
        }
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        match e {
            FieldElementExpression::Identifier(id) => match self.constants.get(&id) {
                Some(e) => match e {
                    TypedExpression::FieldElement(e) => e.clone(),
                    _ => unreachable!(
                        "constant stored for a field element should be a field element"
                    ),
                },
                None => FieldElementExpression::Identifier(id),
            },
            FieldElementExpression::Add(box e1, box e2) => match (
                self.fold_field_expression(e1),
                self.fold_field_expression(e2),
            ) {
                (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                    FieldElementExpression::Number(n1 + n2)
                }
                (e1, e2) => FieldElementExpression::Add(box e1, box e2),
            },
            FieldElementExpression::Sub(box e1, box e2) => match (
                self.fold_field_expression(e1),
                self.fold_field_expression(e2),
            ) {
                (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                    FieldElementExpression::Number(n1 - n2)
                }
                (e1, e2) => FieldElementExpression::Sub(box e1, box e2),
            },
            FieldElementExpression::Mult(box e1, box e2) => match (
                self.fold_field_expression(e1),
                self.fold_field_expression(e2),
            ) {
                (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                    FieldElementExpression::Number(n1 * n2)
                }
                (e1, e2) => FieldElementExpression::Mult(box e1, box e2),
            },
            FieldElementExpression::Div(box e1, box e2) => match (
                self.fold_field_expression(e1),
                self.fold_field_expression(e2),
            ) {
                (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                    FieldElementExpression::Number(n1 / n2)
                }
                (e1, e2) => FieldElementExpression::Div(box e1, box e2),
            },
            FieldElementExpression::Pow(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1);
                let e2 = self.fold_field_expression(e2);
                match (e1, e2) {
                    (_, FieldElementExpression::Number(ref n2)) if *n2 == T::from(0) => {
                        FieldElementExpression::Number(T::from(1))
                    }
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        FieldElementExpression::Number(n1.pow(n2))
                    }
                    (e1, FieldElementExpression::Number(n2)) => {
                        FieldElementExpression::Pow(box e1, box FieldElementExpression::Number(n2))
                    }
                    (_, e2) => unreachable!(format!(
                        "non-constant exponent {} detected during static analysis",
                        e2
                    )),
                }
            }
            FieldElementExpression::IfElse(box condition, box consequence, box alternative) => {
                let consequence = self.fold_field_expression(consequence);
                let alternative = self.fold_field_expression(alternative);
                match self.fold_boolean_expression(condition) {
                    BooleanExpression::Value(true) => consequence,
                    BooleanExpression::Value(false) => alternative,
                    c => FieldElementExpression::IfElse(box c, box consequence, box alternative),
                }
            }
            FieldElementExpression::Select(box array, box index) => {
                let array = self.fold_array_expression(array);
                let index = self.fold_field_expression(index);

                let inner_type = array.inner_type().clone();
                let size = array.size();

                match (array.into_inner(), index) {
                    (ArrayExpressionInner::Value(v), FieldElementExpression::Number(n)) => {
                        let n_as_usize = n.to_dec_string().parse::<usize>().unwrap();
                        if n_as_usize < size {
                            FieldElementExpression::try_from(v[n_as_usize].clone()).unwrap()
                        } else {
                            unreachable!(
                                "out of bounds index ({} >= {}) found during static analysis",
                                n_as_usize, size
                            );
                        }
                    }
                    (ArrayExpressionInner::Identifier(id), FieldElementExpression::Number(n)) => {
                        match self.constants.get(&id) {
                            Some(a) => match a {
                                TypedExpression::Array(a) => match a.as_inner() {
                                    ArrayExpressionInner::Value(v) => {
                                        FieldElementExpression::try_from(
                                            v[n.to_dec_string().parse::<usize>().unwrap()].clone(),
                                        )
                                        .unwrap()
                                    }
                                    _ => unreachable!(),
                                },
                                _ => unreachable!(""),
                            },
                            None => FieldElementExpression::Select(
                                box ArrayExpressionInner::Identifier(id).annotate(inner_type, size),
                                box FieldElementExpression::Number(n),
                            ),
                        }
                    }
                    (a, i) => {
                        FieldElementExpression::Select(box a.annotate(inner_type, size), box i)
                    }
                }
            }
            FieldElementExpression::Member(box s, m) => {
                let s = self.fold_struct_expression(s);

                let members = match s.get_type() {
                    Type::Struct(members) => members,
                    _ => unreachable!("???"),
                };

                match s.into_inner() {
                    StructExpressionInner::Value(v) => {
                        match members
                            .iter()
                            .zip(v)
                            .find(|(member, _)| member.id == m)
                            .unwrap()
                            .1
                        {
                            TypedExpression::FieldElement(s) => s,
                            _ => unreachable!("????"),
                        }
                    }
                    inner => FieldElementExpression::Member(box inner.annotate(members), m),
                }
            }
            FieldElementExpression::FunctionCall(key, inputs) => {
                assert!(
                    self.verbose,
                    "function calls should only exist out of multidef in verbose mode"
                );
                fold_field_expression(self, FieldElementExpression::FunctionCall(key, inputs))
            }
            e => fold_field_expression(self, e),
        }
    }

    fn fold_array_expression_inner(
        &mut self,
        ty: &Type,
        size: usize,
        e: ArrayExpressionInner<'ast, T>,
    ) -> ArrayExpressionInner<'ast, T> {
        match e {
            ArrayExpressionInner::Identifier(id) => match self.constants.get(&id) {
                Some(e) => match e {
                    TypedExpression::Array(e) => e.as_inner().clone(),
                    _ => panic!("constant stored for an array should be an array"),
                },
                None => ArrayExpressionInner::Identifier(id),
            },
            ArrayExpressionInner::Select(box array, box index) => {
                let array = self.fold_array_expression(array);
                let index = self.fold_field_expression(index);

                let inner_type = array.inner_type().clone();
                let size = array.size();

                match (array.into_inner(), index) {
                    (ArrayExpressionInner::Value(v), FieldElementExpression::Number(n)) => {
                        let n_as_usize = n.to_dec_string().parse::<usize>().unwrap();
                        if n_as_usize < size {
                            ArrayExpression::try_from(v[n_as_usize].clone())
                                .unwrap()
                                .into_inner()
                        } else {
                            unreachable!(
                                "out of bounds index ({} >= {}) found during static analysis",
                                n_as_usize, size
                            );
                        }
                    }
                    (ArrayExpressionInner::Identifier(id), FieldElementExpression::Number(n)) => {
                        match self.constants.get(&id) {
                            Some(a) => match a {
                                TypedExpression::Array(a) => match a.as_inner() {
                                    ArrayExpressionInner::Value(v) => ArrayExpression::try_from(
                                        v[n.to_dec_string().parse::<usize>().unwrap()].clone(),
                                    )
                                    .unwrap()
                                    .into_inner(),
                                    _ => unreachable!(),
                                },
                                _ => unreachable!(""),
                            },
                            None => ArrayExpressionInner::Select(
                                box ArrayExpressionInner::Identifier(id).annotate(inner_type, size),
                                box FieldElementExpression::Number(n),
                            ),
                        }
                    }
                    (a, i) => ArrayExpressionInner::Select(box a.annotate(inner_type, size), box i),
                }
            }
            ArrayExpressionInner::IfElse(box condition, box consequence, box alternative) => {
                let consequence = self.fold_array_expression(consequence);
                let alternative = self.fold_array_expression(alternative);
                match self.fold_boolean_expression(condition) {
                    BooleanExpression::Value(true) => consequence.into_inner(),
                    BooleanExpression::Value(false) => alternative.into_inner(),
                    c => ArrayExpressionInner::IfElse(box c, box consequence, box alternative),
                }
            }
            ArrayExpressionInner::Member(box s, m) => {
                let s = self.fold_struct_expression(s);

                let members = match s.get_type() {
                    Type::Struct(members) => members,
                    _ => unreachable!("should be a struct"),
                };

                match s.into_inner() {
                    StructExpressionInner::Value(v) => {
                        match members
                            .iter()
                            .zip(v)
                            .find(|(member, _)| member.id == m)
                            .unwrap()
                            .1
                        {
                            TypedExpression::Array(a) => a.into_inner(),
                            _ => unreachable!("should be an array"),
                        }
                    }
                    inner => ArrayExpressionInner::Member(box inner.annotate(members), m),
                }
            }
            ArrayExpressionInner::FunctionCall(key, inputs) => {
                assert!(
                    self.verbose,
                    "function calls should only exist out of multidef in verbose mode"
                );
                fold_array_expression_inner(
                    self,
                    ty,
                    size,
                    ArrayExpressionInner::FunctionCall(key, inputs),
                )
            }
            e => fold_array_expression_inner(self, ty, size, e),
        }
    }

    fn fold_struct_expression_inner(
        &mut self,
        ty: &StructType,
        e: StructExpressionInner<'ast, T>,
    ) -> StructExpressionInner<'ast, T> {
        match e {
            StructExpressionInner::Identifier(id) => match self.constants.get(&id) {
                Some(e) => match e {
                    TypedExpression::Struct(e) => e.as_inner().clone(),
                    _ => panic!("constant stored for an array should be an array"),
                },
                None => StructExpressionInner::Identifier(id),
            },
            StructExpressionInner::Select(box array, box index) => {
                let array = self.fold_array_expression(array);
                let index = self.fold_field_expression(index);

                let inner_type = array.inner_type().clone();
                let size = array.size();

                match (array.into_inner(), index) {
                    (ArrayExpressionInner::Value(v), FieldElementExpression::Number(n)) => {
                        let n_as_usize = n.to_dec_string().parse::<usize>().unwrap();
                        if n_as_usize < size {
                            StructExpression::try_from(v[n_as_usize].clone())
                                .unwrap()
                                .into_inner()
                        } else {
                            unreachable!(
                                "out of bounds index ({} >= {}) found during static analysis",
                                n_as_usize, size
                            );
                        }
                    }
                    (ArrayExpressionInner::Identifier(id), FieldElementExpression::Number(n)) => {
                        match self.constants.get(&id) {
                            Some(a) => match a {
                                TypedExpression::Array(a) => match a.as_inner() {
                                    ArrayExpressionInner::Value(v) => StructExpression::try_from(
                                        v[n.to_dec_string().parse::<usize>().unwrap()].clone(),
                                    )
                                    .unwrap()
                                    .into_inner(),
                                    _ => unreachable!(),
                                },
                                _ => unreachable!(""),
                            },
                            None => StructExpressionInner::Select(
                                box ArrayExpressionInner::Identifier(id).annotate(inner_type, size),
                                box FieldElementExpression::Number(n),
                            ),
                        }
                    }
                    (a, i) => {
                        StructExpressionInner::Select(box a.annotate(inner_type, size), box i)
                    }
                }
            }
            StructExpressionInner::IfElse(box condition, box consequence, box alternative) => {
                let consequence = self.fold_struct_expression(consequence);
                let alternative = self.fold_struct_expression(alternative);
                match self.fold_boolean_expression(condition) {
                    BooleanExpression::Value(true) => consequence.into_inner(),
                    BooleanExpression::Value(false) => alternative.into_inner(),
                    c => StructExpressionInner::IfElse(box c, box consequence, box alternative),
                }
            }
            StructExpressionInner::Member(box s, m) => {
                let s = self.fold_struct_expression(s);

                let members = match s.get_type() {
                    Type::Struct(members) => members,
                    _ => unreachable!("should be a struct"),
                };

                match s.into_inner() {
                    StructExpressionInner::Value(v) => {
                        match members
                            .iter()
                            .zip(v)
                            .find(|(member, _)| member.id == m)
                            .unwrap()
                            .1
                        {
                            TypedExpression::Struct(s) => s.into_inner(),
                            _ => unreachable!("should be a struct"),
                        }
                    }
                    inner => StructExpressionInner::Member(box inner.annotate(members), m),
                }
            }
            StructExpressionInner::FunctionCall(key, inputs) => {
                assert!(
                    self.verbose,
                    "function calls should only exist out of multidef in verbose mode"
                );
                fold_struct_expression_inner(
                    self,
                    ty,
                    StructExpressionInner::FunctionCall(key, inputs),
                )
            }
            e => fold_struct_expression_inner(self, ty, e),
        }
    }

    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> BooleanExpression<'ast, T> {
        // Note: we only propagate when we see constants, as comparing of arbitrary expressions would lead to
        // a lot of false negatives due to expressions not being in a canonical form
        // For example, `2 * a` is equivalent to `a + a`, but our notion of equality would not detect that here
        // These kind of reduction rules are easier to apply later in the process, when we have canonical representations
        // of expressions, ie `a + a` would always be written `2 * a`
        match e {
            BooleanExpression::Identifier(id) => match self.constants.get(&id) {
                Some(e) => match e {
                    TypedExpression::Boolean(e) => e.clone(),
                    _ => panic!("constant stored for a boolean should be a boolean"),
                },
                None => BooleanExpression::Identifier(id),
            },
            BooleanExpression::FieldEq(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1);
                let e2 = self.fold_field_expression(e2);

                match (e1, e2) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        BooleanExpression::Value(n1 == n2)
                    }
                    (e1, e2) => BooleanExpression::FieldEq(box e1, box e2),
                }
            }
            BooleanExpression::BoolEq(box e1, box e2) => {
                let e1 = self.fold_boolean_expression(e1);
                let e2 = self.fold_boolean_expression(e2);

                match (e1, e2) {
                    (BooleanExpression::Value(n1), BooleanExpression::Value(n2)) => {
                        BooleanExpression::Value(n1 == n2)
                    }
                    (e1, e2) => BooleanExpression::BoolEq(box e1, box e2),
                }
            }
            BooleanExpression::Lt(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1);
                let e2 = self.fold_field_expression(e2);

                match (e1, e2) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        BooleanExpression::Value(n1 < n2)
                    }
                    (e1, e2) => BooleanExpression::Lt(box e1, box e2),
                }
            }
            BooleanExpression::Le(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1);
                let e2 = self.fold_field_expression(e2);

                match (e1, e2) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        BooleanExpression::Value(n1 <= n2)
                    }
                    (e1, e2) => BooleanExpression::Le(box e1, box e2),
                }
            }
            BooleanExpression::Gt(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1);
                let e2 = self.fold_field_expression(e2);

                match (e1, e2) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        BooleanExpression::Value(n1 > n2)
                    }
                    (e1, e2) => BooleanExpression::Gt(box e1, box e2),
                }
            }
            BooleanExpression::Ge(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1);
                let e2 = self.fold_field_expression(e2);

                match (e1, e2) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        BooleanExpression::Value(n1 >= n2)
                    }
                    (e1, e2) => BooleanExpression::Ge(box e1, box e2),
                }
            }
            BooleanExpression::Or(box e1, box e2) => {
                let e1 = self.fold_boolean_expression(e1);
                let e2 = self.fold_boolean_expression(e2);

                match (e1, e2) {
                    // reduction of constants
                    (BooleanExpression::Value(v1), BooleanExpression::Value(v2)) => {
                        BooleanExpression::Value(v1 || v2)
                    }
                    // x || true == true
                    (_, BooleanExpression::Value(true)) | (BooleanExpression::Value(true), _) => {
                        BooleanExpression::Value(true)
                    }
                    // x || false == x
                    (e, BooleanExpression::Value(false)) | (BooleanExpression::Value(false), e) => {
                        e
                    }
                    (e1, e2) => BooleanExpression::Or(box e1, box e2),
                }
            }
            BooleanExpression::And(box e1, box e2) => {
                let e1 = self.fold_boolean_expression(e1);
                let e2 = self.fold_boolean_expression(e2);

                match (e1, e2) {
                    // reduction of constants
                    (BooleanExpression::Value(v1), BooleanExpression::Value(v2)) => {
                        BooleanExpression::Value(v1 && v2)
                    }
                    // x && true == x
                    (e, BooleanExpression::Value(true)) | (BooleanExpression::Value(true), e) => e,
                    // x && false == false
                    (_, BooleanExpression::Value(false)) | (BooleanExpression::Value(false), _) => {
                        BooleanExpression::Value(false)
                    }
                    (e1, e2) => BooleanExpression::And(box e1, box e2),
                }
            }
            BooleanExpression::Not(box e) => {
                let e = self.fold_boolean_expression(e);
                match e {
                    BooleanExpression::Value(v) => BooleanExpression::Value(!v),
                    e => BooleanExpression::Not(box e),
                }
            }
            BooleanExpression::IfElse(box condition, box consequence, box alternative) => {
                let consequence = self.fold_boolean_expression(consequence);
                let alternative = self.fold_boolean_expression(alternative);
                match self.fold_boolean_expression(condition) {
                    BooleanExpression::Value(true) => consequence,
                    BooleanExpression::Value(false) => alternative,
                    c => BooleanExpression::IfElse(box c, box consequence, box alternative),
                }
            }
            BooleanExpression::Select(box array, box index) => {
                let array = self.fold_array_expression(array);
                let index = self.fold_field_expression(index);

                let inner_type = array.inner_type().clone();
                let size = array.size();

                match (array.into_inner(), index) {
                    (ArrayExpressionInner::Value(v), FieldElementExpression::Number(n)) => {
                        let n_as_usize = n.to_dec_string().parse::<usize>().unwrap();
                        if n_as_usize < size {
                            BooleanExpression::try_from(v[n_as_usize].clone()).unwrap()
                        } else {
                            unreachable!(
                                "out of bounds index ({} >= {}) found during static analysis",
                                n_as_usize, size
                            );
                        }
                    }
                    (ArrayExpressionInner::Identifier(id), FieldElementExpression::Number(n)) => {
                        match self.constants.get(&id) {
                            Some(a) => match a {
                                TypedExpression::Array(a) => match a.as_inner() {
                                    ArrayExpressionInner::Value(v) => BooleanExpression::try_from(
                                        v[n.to_dec_string().parse::<usize>().unwrap()].clone(),
                                    )
                                    .unwrap(),
                                    _ => unreachable!(),
                                },
                                _ => unreachable!(""),
                            },
                            None => BooleanExpression::Select(
                                box ArrayExpressionInner::Identifier(id).annotate(inner_type, size),
                                box FieldElementExpression::Number(n),
                            ),
                        }
                    }
                    (a, i) => BooleanExpression::Select(box a.annotate(inner_type, size), box i),
                }
            }
            BooleanExpression::Member(box s, m) => {
                let s = self.fold_struct_expression(s);

                let members = match s.get_type() {
                    Type::Struct(members) => members,
                    _ => unreachable!("should be a struct"),
                };

                match s.into_inner() {
                    StructExpressionInner::Value(v) => {
                        match members
                            .iter()
                            .zip(v)
                            .find(|(member, _)| member.id == m)
                            .unwrap()
                            .1
                        {
                            TypedExpression::Boolean(s) => s,
                            _ => unreachable!("should be a boolean"),
                        }
                    }
                    inner => BooleanExpression::Member(box inner.annotate(members), m),
                }
            }
            BooleanExpression::FunctionCall(key, inputs) => {
                assert!(
                    self.verbose,
                    "function calls should only exist out of multidef in verbose mode"
                );
                fold_boolean_expression(self, BooleanExpression::FunctionCall(key, inputs))
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
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(Bn128Field::from(5))
                );
            }

            #[test]
            fn sub() {
                let e = FieldElementExpression::Sub(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                );

                assert_eq!(
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(Bn128Field::from(1))
                );
            }

            #[test]
            fn mult() {
                let e = FieldElementExpression::Mult(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                );

                assert_eq!(
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(Bn128Field::from(6))
                );
            }

            #[test]
            fn div() {
                let e = FieldElementExpression::Div(
                    box FieldElementExpression::Number(Bn128Field::from(6)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                );

                assert_eq!(
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(Bn128Field::from(3))
                );
            }

            #[test]
            fn pow() {
                let e = FieldElementExpression::Pow(
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                );

                assert_eq!(
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(Bn128Field::from(8))
                );
            }

            #[test]
            fn if_else_true() {
                let e = FieldElementExpression::IfElse(
                    box BooleanExpression::Value(true),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                );

                assert_eq!(
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(Bn128Field::from(2))
                );
            }

            #[test]
            fn if_else_false() {
                let e = FieldElementExpression::IfElse(
                    box BooleanExpression::Value(false),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                );

                assert_eq!(
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(Bn128Field::from(3))
                );
            }

            #[test]
            fn select() {
                let e = FieldElementExpression::Select(
                    box ArrayExpressionInner::Value(vec![
                        FieldElementExpression::Number(Bn128Field::from(1)).into(),
                        FieldElementExpression::Number(Bn128Field::from(2)).into(),
                        FieldElementExpression::Number(Bn128Field::from(3)).into(),
                    ])
                    .annotate(Type::FieldElement, 3),
                    box FieldElementExpression::Add(
                        box FieldElementExpression::Number(Bn128Field::from(1)),
                        box FieldElementExpression::Number(Bn128Field::from(1)),
                    ),
                );

                assert_eq!(
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(Bn128Field::from(3))
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
                    Propagator::new().fold_boolean_expression(e_true),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_false),
                    BooleanExpression::Value(false)
                );
                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_default.clone()),
                    e_default
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
                    Propagator::new().fold_boolean_expression(e_true),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_false),
                    BooleanExpression::Value(false)
                );
            }

            #[test]
            fn bool_eq() {
                assert_eq!(
                    Propagator::<Bn128Field>::new().fold_boolean_expression(
                        BooleanExpression::BoolEq(
                            box BooleanExpression::Value(false),
                            box BooleanExpression::Value(false)
                        )
                    ),
                    BooleanExpression::Value(true)
                );

                assert_eq!(
                    Propagator::<Bn128Field>::new().fold_boolean_expression(
                        BooleanExpression::BoolEq(
                            box BooleanExpression::Value(true),
                            box BooleanExpression::Value(true)
                        )
                    ),
                    BooleanExpression::Value(true)
                );

                assert_eq!(
                    Propagator::<Bn128Field>::new().fold_boolean_expression(
                        BooleanExpression::BoolEq(
                            box BooleanExpression::Value(true),
                            box BooleanExpression::Value(false)
                        )
                    ),
                    BooleanExpression::Value(false)
                );

                assert_eq!(
                    Propagator::<Bn128Field>::new().fold_boolean_expression(
                        BooleanExpression::BoolEq(
                            box BooleanExpression::Value(false),
                            box BooleanExpression::Value(true)
                        )
                    ),
                    BooleanExpression::Value(false)
                );
            }

            #[test]
            fn lt() {
                let e_true = BooleanExpression::Lt(
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                    box FieldElementExpression::Number(Bn128Field::from(4)),
                );

                let e_false = BooleanExpression::Lt(
                    box FieldElementExpression::Number(Bn128Field::from(4)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                );

                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_true),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_false),
                    BooleanExpression::Value(false)
                );
            }

            #[test]
            fn le() {
                let e_true = BooleanExpression::Le(
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                );

                let e_false = BooleanExpression::Le(
                    box FieldElementExpression::Number(Bn128Field::from(4)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                );

                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_true),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_false),
                    BooleanExpression::Value(false)
                );
            }

            #[test]
            fn gt() {
                let e_true = BooleanExpression::Gt(
                    box FieldElementExpression::Number(Bn128Field::from(5)),
                    box FieldElementExpression::Number(Bn128Field::from(4)),
                );

                let e_false = BooleanExpression::Gt(
                    box FieldElementExpression::Number(Bn128Field::from(4)),
                    box FieldElementExpression::Number(Bn128Field::from(5)),
                );

                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_true),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_false),
                    BooleanExpression::Value(false)
                );
            }

            #[test]
            fn ge() {
                let e_true = BooleanExpression::Ge(
                    box FieldElementExpression::Number(Bn128Field::from(5)),
                    box FieldElementExpression::Number(Bn128Field::from(5)),
                );

                let e_false = BooleanExpression::Ge(
                    box FieldElementExpression::Number(Bn128Field::from(4)),
                    box FieldElementExpression::Number(Bn128Field::from(5)),
                );

                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_true),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_false),
                    BooleanExpression::Value(false)
                );
            }

            #[test]
            fn and() {
                let a_bool: Identifier = "a".into();

                assert_eq!(
                    Propagator::<Bn128Field>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Value(true),
                            box BooleanExpression::Identifier(a_bool.clone())
                        )
                    ),
                    BooleanExpression::Identifier(a_bool.clone())
                );
                assert_eq!(
                    Propagator::<Bn128Field>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Identifier(a_bool.clone()),
                            box BooleanExpression::Value(true),
                        )
                    ),
                    BooleanExpression::Identifier(a_bool.clone())
                );
                assert_eq!(
                    Propagator::<Bn128Field>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Value(false),
                            box BooleanExpression::Identifier(a_bool.clone())
                        )
                    ),
                    BooleanExpression::Value(false)
                );
                assert_eq!(
                    Propagator::<Bn128Field>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Identifier(a_bool.clone()),
                            box BooleanExpression::Value(false),
                        )
                    ),
                    BooleanExpression::Value(false)
                );
                assert_eq!(
                    Propagator::<Bn128Field>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Value(true),
                            box BooleanExpression::Value(false),
                        )
                    ),
                    BooleanExpression::Value(false)
                );
                assert_eq!(
                    Propagator::<Bn128Field>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Value(false),
                            box BooleanExpression::Value(true),
                        )
                    ),
                    BooleanExpression::Value(false)
                );
                assert_eq!(
                    Propagator::<Bn128Field>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Value(true),
                            box BooleanExpression::Value(true),
                        )
                    ),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::<Bn128Field>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Value(false),
                            box BooleanExpression::Value(false),
                        )
                    ),
                    BooleanExpression::Value(false)
                );
            }

            #[test]
            fn or() {
                let a_bool: Identifier = "a".into();

                assert_eq!(
                    Propagator::<Bn128Field>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Value(true),
                        box BooleanExpression::Identifier(a_bool.clone())
                    )),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::<Bn128Field>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Identifier(a_bool.clone()),
                        box BooleanExpression::Value(true),
                    )),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::<Bn128Field>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Value(false),
                        box BooleanExpression::Identifier(a_bool.clone())
                    )),
                    BooleanExpression::Identifier(a_bool.clone())
                );
                assert_eq!(
                    Propagator::<Bn128Field>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Identifier(a_bool.clone()),
                        box BooleanExpression::Value(false),
                    )),
                    BooleanExpression::Identifier(a_bool.clone())
                );
                assert_eq!(
                    Propagator::<Bn128Field>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Value(true),
                        box BooleanExpression::Value(false),
                    )),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::<Bn128Field>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Value(false),
                        box BooleanExpression::Value(true),
                    )),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::<Bn128Field>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Value(true),
                        box BooleanExpression::Value(true),
                    )),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::<Bn128Field>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Value(false),
                        box BooleanExpression::Value(false),
                    )),
                    BooleanExpression::Value(false)
                );
            }
        }
    }
}
