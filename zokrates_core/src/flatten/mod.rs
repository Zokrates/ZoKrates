//! Module containing the `Flattener` to process a program that is R1CS-able.
//!
//! @file flatten.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

use crate::flat_absy::*;
use crate::solvers::Solver;
use crate::typed_absy::types::{FunctionIdentifier, FunctionKey, MemberId, Signature, Type};
use crate::typed_absy::*;
use std::collections::HashMap;
use std::convert::TryFrom;
use zokrates_field::field::Field;

/// Flattener, computes flattened program.
#[derive(Debug)]
pub struct Flattener<'ast, T: Field> {
    /// Index of the next introduced variable while processing the program.
    next_var_idx: usize,
    /// `FlatVariable`s corresponding to each `Identifier`
    layout: HashMap<Identifier<'ast>, Vec<FlatVariable>>,
    /// Cached `FlatFunction`s to avoid re-flattening them
    flat_cache: HashMap<FunctionKey<'ast>, FlatFunction<T>>,
}

// We introduce a trait in order to make it possible to make flattening `e` generic over the type of `e`

trait Flatten<'ast, T: Field>:
    TryFrom<TypedExpression<'ast, T>, Error = ()> + IfElse<'ast, T> + Select<'ast, T> + Member<'ast, T>
{
    fn flatten(
        self,
        flattener: &mut Flattener<'ast, T>,
        symbols: &TypedFunctionSymbols<'ast, T>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
    ) -> Vec<FlatExpression<T>>;
}

impl<'ast, T: Field> Flatten<'ast, T> for FieldElementExpression<'ast, T> {
    fn flatten(
        self,
        flattener: &mut Flattener<'ast, T>,
        symbols: &TypedFunctionSymbols<'ast, T>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
    ) -> Vec<FlatExpression<T>> {
        vec![flattener.flatten_field_expression(symbols, statements_flattened, self)]
    }
}

impl<'ast, T: Field> Flatten<'ast, T> for BooleanExpression<'ast, T> {
    fn flatten(
        self,
        flattener: &mut Flattener<'ast, T>,
        symbols: &TypedFunctionSymbols<'ast, T>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
    ) -> Vec<FlatExpression<T>> {
        vec![flattener.flatten_boolean_expression(symbols, statements_flattened, self)]
    }
}

impl<'ast, T: Field> Flatten<'ast, T> for StructExpression<'ast, T> {
    fn flatten(
        self,
        flattener: &mut Flattener<'ast, T>,
        symbols: &TypedFunctionSymbols<'ast, T>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
    ) -> Vec<FlatExpression<T>> {
        flattener.flatten_struct_expression(symbols, statements_flattened, self)
    }
}

impl<'ast, T: Field> Flatten<'ast, T> for ArrayExpression<'ast, T> {
    fn flatten(
        self,
        flattener: &mut Flattener<'ast, T>,
        symbols: &TypedFunctionSymbols<'ast, T>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
    ) -> Vec<FlatExpression<T>> {
        match self.inner_type() {
            Type::FieldElement => flattener
                .flatten_array_expression::<FieldElementExpression<'ast, T>>(
                    symbols,
                    statements_flattened,
                    self,
                ),
            Type::Boolean => flattener.flatten_array_expression::<BooleanExpression<'ast, T>>(
                symbols,
                statements_flattened,
                self,
            ),
            Type::Array(..) => flattener.flatten_array_expression::<ArrayExpression<'ast, T>>(
                symbols,
                statements_flattened,
                self,
            ),
            Type::Struct(..) => flattener.flatten_array_expression::<StructExpression<'ast, T>>(
                symbols,
                statements_flattened,
                self,
            ),
        }
    }
}

impl<'ast, T: Field> Flattener<'ast, T> {
    pub fn flatten(p: TypedProgram<'ast, T>) -> FlatProg<T> {
        Flattener::new().flatten_program(p)
    }

    /// Returns a `Flattener` with fresh `layout`.

    fn new() -> Flattener<'ast, T> {
        Flattener {
            next_var_idx: 0,
            layout: HashMap::new(),
            flat_cache: HashMap::new(),
        }
    }

    /// Flatten an if/else expression
    ///
    /// # Arguments
    ///
    /// * `symbols` - Available functions in this context
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `condition` - the condition as a `BooleanExpression`.
    /// * `consequence` - the consequence of type U.
    /// * `alternative` - the alternative of type U.
    /// # Remarks
    /// * U is the type of the expression
    fn flatten_if_else_expression<U: Flatten<'ast, T>>(
        &mut self,
        symbols: &TypedFunctionSymbols<'ast, T>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        condition: BooleanExpression<'ast, T>,
        consequence: U,
        alternative: U,
    ) -> Vec<FlatExpression<T>> {
        let condition = self.flatten_boolean_expression(symbols, statements_flattened, condition);

        let consequence = consequence.flatten(self, symbols, statements_flattened);

        let alternative = alternative.flatten(self, symbols, statements_flattened);

        let size = consequence.len();

        let condition_id = self.use_sym();
        statements_flattened.push(FlatStatement::Definition(condition_id, condition));

        let consequence_ids: Vec<_> = (0..size).map(|_| self.use_sym()).collect();
        statements_flattened.extend(
            consequence
                .into_iter()
                .zip(consequence_ids.iter())
                .map(|(c, c_id)| FlatStatement::Definition(*c_id, c)),
        );

        let alternative_ids: Vec<_> = (0..size).map(|_| self.use_sym()).collect();
        statements_flattened.extend(
            alternative
                .into_iter()
                .zip(alternative_ids.iter())
                .map(|(a, a_id)| FlatStatement::Definition(*a_id, a)),
        );

        let term0_ids: Vec<_> = (0..size).map(|_| self.use_sym()).collect();
        statements_flattened.extend(consequence_ids.iter().zip(term0_ids.iter()).map(
            |(c_id, t0_id)| {
                FlatStatement::Definition(
                    *t0_id,
                    FlatExpression::Mult(
                        box condition_id.clone().into(),
                        box FlatExpression::from(*c_id),
                    ),
                )
            },
        ));

        let term1_ids: Vec<_> = (0..size).map(|_| self.use_sym()).collect();
        statements_flattened.extend(alternative_ids.iter().zip(term1_ids.iter()).map(
            |(a_id, t1_id)| {
                FlatStatement::Definition(
                    *t1_id,
                    FlatExpression::Mult(
                        box FlatExpression::Sub(
                            box FlatExpression::Number(T::one()),
                            box condition_id.into(),
                        ),
                        box FlatExpression::from(*a_id),
                    ),
                )
            },
        ));

        let res: Vec<_> = (0..size).map(|_| self.use_sym()).collect();
        statements_flattened.extend(term0_ids.iter().zip(term1_ids).zip(res.iter()).map(
            |((t0_id, t1_id), r_id)| {
                FlatStatement::Definition(
                    *r_id,
                    FlatExpression::Add(
                        box FlatExpression::from(*t0_id),
                        box FlatExpression::from(t1_id),
                    ),
                )
            },
        ));
        res.into_iter().map(|r| r.into()).collect()
    }

    fn flatten_member_expression(
        &mut self,
        symbols: &TypedFunctionSymbols<'ast, T>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        s: StructExpression<'ast, T>,
        member_id: MemberId,
    ) -> Vec<FlatExpression<T>> {
        let members = s.ty().clone();
        let expected_output_size = members
            .iter()
            .find(|member| *member.id == member_id)
            .unwrap()
            .ty
            .get_primitive_count();

        let res =
            match s.into_inner() {
                StructExpressionInner::Value(values) => {
                    // If the struct has an explicit value, we get the value at the given member
                    assert_eq!(values.len(), members.len());
                    values
                        .into_iter()
                        .zip(members.into_iter())
                        .filter(|(_, member)| *member.id == member_id)
                        .flat_map(|(v, member)| match *member.ty {
                            Type::FieldElement => FieldElementExpression::try_from(v)
                                .unwrap()
                                .flatten(self, symbols, statements_flattened),
                            Type::Boolean => BooleanExpression::try_from(v).unwrap().flatten(
                                self,
                                symbols,
                                statements_flattened,
                            ),
                            Type::Array(..) => ArrayExpression::try_from(v).unwrap().flatten(
                                self,
                                symbols,
                                statements_flattened,
                            ),
                            Type::Struct(..) => StructExpression::try_from(v).unwrap().flatten(
                                self,
                                symbols,
                                statements_flattened,
                            ),
                        })
                        .collect()
                }
                StructExpressionInner::Identifier(id) => {
                    // If the struct is an identifier, we allocated variables in the layout for that identifier. We need to access a subset of these values.
                    // the struct is encoded as a sequence, so we need to identify the offset at which this member starts
                    let offset = members
                        .iter()
                        .take_while(|member| *member.id != member_id)
                        .map(|member| member.ty.get_primitive_count())
                        .sum();

                    // we also need the size of this member
                    let size = members
                        .iter()
                        .find(|member| *member.id == member_id)
                        .unwrap()
                        .ty
                        .get_primitive_count();
                    self.layout.get(&id).unwrap()[offset..(offset + size)]
                        .into_iter()
                        .map(|i| i.clone().into())
                        .collect()
                }
                StructExpressionInner::Select(box array, box index) => {
                    let offset = members
                        .iter()
                        .take_while(|member| *member.id != member_id)
                        .map(|member| member.ty.get_primitive_count())
                        .sum();

                    // we also need the size of this member
                    let size = members
                        .iter()
                        .find(|member| *member.id == member_id)
                        .unwrap()
                        .ty
                        .get_primitive_count();

                    self.flatten_select_expression::<StructExpression<'ast, T>>(
                        symbols,
                        statements_flattened,
                        array,
                        index,
                    )[offset..offset + size]
                        .to_vec()
                }
                StructExpressionInner::FunctionCall(..) => unreachable!(),
                StructExpressionInner::IfElse(box condition, box consequence, box alternative) => {
                    // if the struct is `(if c then a else b)`, we want to access `(if c then a else b).member`
                    // we reduce to `if c then a.member else b.member`
                    let ty = *members
                        .clone()
                        .into_iter()
                        .find(|member| *member.id == member_id)
                        .unwrap()
                        .ty;

                    match ty {
                        Type::FieldElement => self.flatten_if_else_expression(
                            symbols,
                            statements_flattened,
                            condition.clone(),
                            FieldElementExpression::member(consequence.clone(), member_id.clone()),
                            FieldElementExpression::member(alternative.clone(), member_id),
                        ),
                        Type::Boolean => self.flatten_if_else_expression(
                            symbols,
                            statements_flattened,
                            condition.clone(),
                            BooleanExpression::member(consequence.clone(), member_id.clone()),
                            BooleanExpression::member(alternative.clone(), member_id),
                        ),
                        Type::Struct(..) => self.flatten_if_else_expression(
                            symbols,
                            statements_flattened,
                            condition.clone(),
                            StructExpression::member(consequence.clone(), member_id.clone()),
                            StructExpression::member(alternative.clone(), member_id),
                        ),
                        Type::Array(..) => self.flatten_if_else_expression(
                            symbols,
                            statements_flattened,
                            condition.clone(),
                            ArrayExpression::member(consequence.clone(), member_id.clone()),
                            ArrayExpression::member(alternative.clone(), member_id),
                        ),
                    }
                }
                StructExpressionInner::Member(box s0, m_id) => {
                    let e = self.flatten_member_expression(symbols, statements_flattened, s0, m_id);

                    let offset = members
                        .iter()
                        .take_while(|member| *member.id != member_id)
                        .map(|member| member.ty.get_primitive_count())
                        .sum();

                    // we also need the size of this member
                    let size = members
                        .iter()
                        .find(|member| *member.id == member_id)
                        .unwrap()
                        .ty
                        .get_primitive_count();

                    e[offset..(offset + size)].into()
                }
            };

        assert_eq!(res.len(), expected_output_size);
        res
    }

    /// Flatten an array selection expression
    ///
    /// # Arguments
    ///
    /// * `symbols` - Available functions in this context
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `expression` - `TypedExpression` that will be flattened.
    /// # Remarks
    /// * U is the type of the expression
    fn flatten_select_expression<U: Flatten<'ast, T>>(
        &mut self,
        symbols: &TypedFunctionSymbols<'ast, T>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        array: ArrayExpression<'ast, T>,
        index: FieldElementExpression<'ast, T>,
    ) -> Vec<FlatExpression<T>> {
        let size = array.size();
        let ty = array.inner_type().clone();

        let element_size = ty.get_primitive_count();

        match index {
            FieldElementExpression::Number(n) => match array.into_inner() {
                ArrayExpressionInner::Identifier(id) => {
                    assert!(n < T::from(size));
                    let n = n.to_dec_string().parse::<usize>().unwrap();
                    self.layout.get(&id).unwrap()[n * element_size..(n + 1) * element_size]
                        .into_iter()
                        .map(|i| i.clone().into())
                        .collect()
                }
                ArrayExpressionInner::Value(expressions) => {
                    assert!(n < T::from(size));
                    let n = n.to_dec_string().parse::<usize>().unwrap();
                    U::try_from(expressions[n].clone()).unwrap().flatten(
                        self,
                        symbols,
                        statements_flattened,
                    )
                }
                ArrayExpressionInner::FunctionCall(..) => unreachable!(),
                ArrayExpressionInner::IfElse(condition, consequence, alternative) => {
                    // [if cond then [a, b] else [c, d]][1] == if cond then [a, b][1] else [c, d][1]
                    U::if_else(
                        *condition,
                        U::select(*consequence, FieldElementExpression::Number(n.clone())),
                        U::select(*alternative, FieldElementExpression::Number(n)),
                    )
                    .flatten(self, symbols, statements_flattened)
                }
                ArrayExpressionInner::Member(box s, id) => {
                    assert!(n < T::from(size));
                    let n = n.to_dec_string().parse::<usize>().unwrap();
                    self.flatten_member_expression(symbols, statements_flattened, s, id)
                        [n * ty.get_primitive_count()..(n + 1) * ty.get_primitive_count()]
                        .to_vec()
                }
                ArrayExpressionInner::Select(box array, box index) => {
                    assert!(n < T::from(size));
                    let n = n.to_dec_string().parse::<usize>().unwrap();

                    let e = match array.inner_type() {
                        Type::FieldElement => self
                            .flatten_select_expression::<FieldElementExpression<'ast, T>>(
                                symbols,
                                statements_flattened,
                                array,
                                index,
                            ),
                        Type::Boolean => self
                            .flatten_select_expression::<BooleanExpression<'ast, T>>(
                                symbols,
                                statements_flattened,
                                array,
                                index,
                            ),
                        Type::Array(..) => self
                            .flatten_select_expression::<ArrayExpression<'ast, T>>(
                                symbols,
                                statements_flattened,
                                array,
                                index,
                            ),
                        Type::Struct(..) => self
                            .flatten_select_expression::<StructExpression<'ast, T>>(
                                symbols,
                                statements_flattened,
                                array,
                                index,
                            ),
                    };

                    e[n * element_size..(n + 1) * element_size]
                        .into_iter()
                        .map(|i| i.clone().into())
                        .collect()
                }
            },
            e => {
                // we have array[e] with e an arbitrary expression
                // first we check that e is in 0..array.len(), so we check that sum(if e == i then 1 else 0) == 1
                // here, depending on the size, we could use a proper range check based on bits
                let range_check = (0..size)
                    .map(|i| {
                        FieldElementExpression::IfElse(
                            box BooleanExpression::FieldEq(
                                box e.clone(),
                                box FieldElementExpression::Number(T::from(i)),
                            ),
                            box FieldElementExpression::Number(T::from(1)),
                            box FieldElementExpression::Number(T::from(0)),
                        )
                    })
                    .fold(FieldElementExpression::Number(T::from(0)), |acc, e| {
                        FieldElementExpression::Add(box acc, box e)
                    });

                let range_check_statement = TypedStatement::Condition(
                    FieldElementExpression::Number(T::from(1)).into(),
                    range_check.into(),
                );

                self.flatten_statement(symbols, statements_flattened, range_check_statement);

                // now we flatten to sum(if e == i then array[i] else false)
                (0..size)
                    .map(|i| {
                        let term = match array.clone().into_inner() {
                            // a[i] = a[i]
                            ArrayExpressionInner::Identifier(id) => U::select(
                                ArrayExpressionInner::Identifier(id).annotate(ty.clone(), size),
                                FieldElementExpression::Number(T::from(i)),
                            ),
                            // [a_0, ..., a_n][i] = a_i
                            ArrayExpressionInner::Value(expressions) => {
                                assert_eq!(size, expressions.len());
                                U::try_from(expressions[i].clone()).unwrap()
                            }
                            ArrayExpressionInner::FunctionCall(..) => unreachable!(),
                            // (if c then a else b fi)[i] = if c then a[i] else b[i]
                            ArrayExpressionInner::IfElse(condition, consequence, alternative) => {
                                U::if_else(
                                    *condition,
                                    U::select(
                                        *consequence,
                                        FieldElementExpression::Number(T::from(i)),
                                    ),
                                    U::select(
                                        *alternative,
                                        FieldElementExpression::Number(T::from(i)),
                                    ),
                                )
                            }
                            ArrayExpressionInner::Member(box s, id) => U::member(s, id),
                            ArrayExpressionInner::Select(box array, box index) => U::select(
                                ArrayExpressionInner::Select(box array, box index)
                                    .annotate(ty.clone(), size),
                                FieldElementExpression::Number(T::from(i)),
                            ),
                        };

                        (term, FieldElementExpression::Number(T::from(i)))
                    })
                    .fold(None, |acc, (term, index)| match acc {
                        None => Some(term),
                        Some(acc) => Some(U::if_else(
                            BooleanExpression::FieldEq(box e.clone(), box index),
                            term,
                            acc,
                        )),
                    })
                    .unwrap()
                    .flatten(self, symbols, statements_flattened)
            }
        }
    }

    /// Flattens a boolean expression
    ///
    /// # Arguments
    ///
    /// * `symbols` - Available functions in this context
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `expression` - `BooleanExpression` that will be flattened.
    ///
    /// # Postconditions
    ///
    /// * `flatten_boolean_expressions` always returns a linear expression,
    /// * in order to preserve composability.
    fn flatten_boolean_expression(
        &mut self,
        symbols: &TypedFunctionSymbols<'ast, T>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        expression: BooleanExpression<'ast, T>,
    ) -> FlatExpression<T> {
        // those will be booleans in the future
        match expression {
            BooleanExpression::Identifier(x) => {
                FlatExpression::Identifier(self.layout.get(&x).unwrap().clone()[0])
            }
            BooleanExpression::Lt(box lhs, box rhs) => {
                // Get the bitwidth to know the size of the binary decompsitions for this Field
                let bitwidth = T::get_required_bits();

                // We know from semantic checking that lhs and rhs have the same type
                // What the expression will flatten to depends on that type

                let lhs_flattened =
                    self.flatten_field_expression(symbols, statements_flattened, lhs);
                let rhs_flattened =
                    self.flatten_field_expression(symbols, statements_flattened, rhs);

                // lhs
                let lhs_id = self.use_sym();
                statements_flattened.push(FlatStatement::Definition(lhs_id, lhs_flattened));

                // check that lhs and rhs are within the right range, i.e., their higher two bits are zero. We use big-endian so they are at positions 0 and 1

                // lhs
                {
                    // define variables for the bits
                    let lhs_bits_be: Vec<FlatVariable> =
                        (0..bitwidth).map(|_| self.use_sym()).collect();

                    // add a directive to get the bits
                    statements_flattened.push(FlatStatement::Directive(FlatDirective::new(
                        lhs_bits_be.clone(),
                        Solver::bits(),
                        vec![lhs_id],
                    )));

                    // bitness checks
                    for i in 0..bitwidth - 2 {
                        statements_flattened.push(FlatStatement::Condition(
                            FlatExpression::Identifier(lhs_bits_be[i + 2]),
                            FlatExpression::Mult(
                                box FlatExpression::Identifier(lhs_bits_be[i + 2]),
                                box FlatExpression::Identifier(lhs_bits_be[i + 2]),
                            ),
                        ));
                    }

                    // bit decomposition check
                    let mut lhs_sum = FlatExpression::Number(T::from(0));

                    for i in 0..bitwidth - 2 {
                        lhs_sum = FlatExpression::Add(
                            box lhs_sum,
                            box FlatExpression::Mult(
                                box FlatExpression::Identifier(lhs_bits_be[i + 2]),
                                box FlatExpression::Number(T::from(2).pow(bitwidth - 2 - i - 1)),
                            ),
                        );
                    }

                    statements_flattened.push(FlatStatement::Condition(
                        FlatExpression::Identifier(lhs_id),
                        lhs_sum,
                    ));
                }

                // rhs
                let rhs_id = self.use_sym();
                statements_flattened.push(FlatStatement::Definition(rhs_id, rhs_flattened));

                // rhs
                {
                    // define variables for the bits
                    let rhs_bits_be: Vec<FlatVariable> =
                        (0..bitwidth).map(|_| self.use_sym()).collect();

                    // add a directive to get the bits
                    statements_flattened.push(FlatStatement::Directive(FlatDirective::new(
                        rhs_bits_be.clone(),
                        Solver::bits(),
                        vec![rhs_id],
                    )));

                    // bitness checks
                    for i in 0..bitwidth - 2 {
                        statements_flattened.push(FlatStatement::Condition(
                            FlatExpression::Identifier(rhs_bits_be[i + 2]),
                            FlatExpression::Mult(
                                box FlatExpression::Identifier(rhs_bits_be[i + 2]),
                                box FlatExpression::Identifier(rhs_bits_be[i + 2]),
                            ),
                        ));
                    }

                    // bit decomposition check
                    let mut rhs_sum = FlatExpression::Number(T::from(0));

                    for i in 0..bitwidth - 2 {
                        rhs_sum = FlatExpression::Add(
                            box rhs_sum,
                            box FlatExpression::Mult(
                                box FlatExpression::Identifier(rhs_bits_be[i + 2]),
                                box FlatExpression::Number(T::from(2).pow(bitwidth - 2 - i - 1)),
                            ),
                        );
                    }

                    statements_flattened.push(FlatStatement::Condition(
                        FlatExpression::Identifier(rhs_id),
                        rhs_sum,
                    ));
                }

                // sym := (lhs * 2) - (rhs * 2)
                let subtraction_result = FlatExpression::Sub(
                    box FlatExpression::Mult(
                        box FlatExpression::Number(T::from(2)),
                        box FlatExpression::Identifier(lhs_id),
                    ),
                    box FlatExpression::Mult(
                        box FlatExpression::Number(T::from(2)),
                        box FlatExpression::Identifier(rhs_id),
                    ),
                );

                // define variables for the bits
                let sub_bits_be: Vec<FlatVariable> =
                    (0..bitwidth).map(|_| self.use_sym()).collect();

                // add a directive to get the bits
                statements_flattened.push(FlatStatement::Directive(FlatDirective::new(
                    sub_bits_be.clone(),
                    Solver::bits(),
                    vec![subtraction_result.clone()],
                )));

                // bitness checks
                for i in 0..bitwidth {
                    statements_flattened.push(FlatStatement::Condition(
                        FlatExpression::Identifier(sub_bits_be[i]),
                        FlatExpression::Mult(
                            box FlatExpression::Identifier(sub_bits_be[i]),
                            box FlatExpression::Identifier(sub_bits_be[i]),
                        ),
                    ));
                }

                // sum(sym_b{i} * 2**i)
                let mut expr = FlatExpression::Number(T::from(0));

                for i in 0..bitwidth {
                    expr = FlatExpression::Add(
                        box expr,
                        box FlatExpression::Mult(
                            box FlatExpression::Identifier(sub_bits_be[i]),
                            box FlatExpression::Number(T::from(2).pow(bitwidth - i - 1)),
                        ),
                    );
                }

                statements_flattened.push(FlatStatement::Condition(subtraction_result, expr));

                FlatExpression::Identifier(sub_bits_be[bitwidth - 1])
            }
            BooleanExpression::BoolEq(box lhs, box rhs) => {
                // lhs and rhs are booleans, they flatten to 0 or 1
                let x = self.flatten_boolean_expression(symbols, statements_flattened, lhs);
                let y = self.flatten_boolean_expression(symbols, statements_flattened, rhs);
                // Wanted: Not(X - Y)**2 which is an XNOR
                // We know that X and Y are [0, 1]
                // (X - Y) can become a negative values, which is why squaring the result is needed
                // Negating this returns correct result

                // Non-binary Truth table for logic of operation
                // +---+---+-------+---------------+
                // | X | Y | X - Y | Not(X - Y)**2 |
                // +---+---+-------+---------------+
                // | 1 | 1 |     0 |             1 |
                // | 1 | 0 |     1 |             0 |
                // | 0 | 1 |    -1 |             0 |
                // | 0 | 0 |     0 |             1 |
                // +---+---+-------+---------------+

                let x_sub_y = FlatExpression::Sub(box x, box y);
                let name_x_mult_x = self.use_sym();

                statements_flattened.push(FlatStatement::Definition(
                    name_x_mult_x,
                    FlatExpression::Mult(box x_sub_y.clone(), box x_sub_y),
                ));

                FlatExpression::Sub(
                    box FlatExpression::Number(T::one()),
                    box FlatExpression::Identifier(name_x_mult_x),
                )
            }
            BooleanExpression::FieldEq(box lhs, box rhs) => {
                // We know from semantic checking that lhs and rhs have the same type
                // What the expression will flatten to depends on that type

                // Wanted: (Y = (X != 0) ? 1 : 0)
                // X = a - b
                // # Y = if X == 0 then 0 else 1 fi
                // # M = if X == 0 then 1 else 1/X fi
                // Y == X * M
                // 0 == (1-Y) * X

                let name_y = self.use_sym();
                let name_m = self.use_sym();

                let x = self.flatten_field_expression(
                    symbols,
                    statements_flattened,
                    FieldElementExpression::Sub(box lhs, box rhs),
                );

                statements_flattened.push(FlatStatement::Directive(FlatDirective::new(
                    vec![name_y, name_m],
                    Solver::ConditionEq,
                    vec![x.clone()],
                )));
                statements_flattened.push(FlatStatement::Condition(
                    FlatExpression::Identifier(name_y),
                    FlatExpression::Mult(box x.clone(), box FlatExpression::Identifier(name_m)),
                ));

                let res = FlatExpression::Sub(
                    box FlatExpression::Number(T::one()),
                    box FlatExpression::Identifier(name_y),
                );

                statements_flattened.push(FlatStatement::Condition(
                    FlatExpression::Number(T::zero()),
                    FlatExpression::Mult(box res.clone(), box x),
                ));

                res
            }
            BooleanExpression::Le(box lhs, box rhs) => {
                let lt = self.flatten_boolean_expression(
                    symbols,
                    statements_flattened,
                    BooleanExpression::Lt(box lhs.clone(), box rhs.clone()),
                );
                let eq = self.flatten_boolean_expression(
                    symbols,
                    statements_flattened,
                    BooleanExpression::FieldEq(box lhs.clone(), box rhs.clone()),
                );
                FlatExpression::Add(box eq, box lt)
            }
            BooleanExpression::Gt(lhs, rhs) => self.flatten_boolean_expression(
                symbols,
                statements_flattened,
                BooleanExpression::Lt(rhs, lhs),
            ),
            BooleanExpression::Ge(lhs, rhs) => self.flatten_boolean_expression(
                symbols,
                statements_flattened,
                BooleanExpression::Le(rhs, lhs),
            ),
            BooleanExpression::Or(box lhs, box rhs) => {
                let x = box self.flatten_boolean_expression(symbols, statements_flattened, lhs);
                let y = box self.flatten_boolean_expression(symbols, statements_flattened, rhs);
                assert!(x.is_linear() && y.is_linear());
                let name_x_and_y = self.use_sym();
                statements_flattened.push(FlatStatement::Definition(
                    name_x_and_y,
                    FlatExpression::Mult(x.clone(), y.clone()),
                ));
                FlatExpression::Sub(
                    box FlatExpression::Add(x, y),
                    box FlatExpression::Identifier(name_x_and_y),
                )
            }
            BooleanExpression::And(box lhs, box rhs) => {
                let x = self.flatten_boolean_expression(symbols, statements_flattened, lhs);
                let y = self.flatten_boolean_expression(symbols, statements_flattened, rhs);

                let name_x_and_y = self.use_sym();
                assert!(x.is_linear() && y.is_linear());
                statements_flattened.push(FlatStatement::Definition(
                    name_x_and_y,
                    FlatExpression::Mult(box x, box y),
                ));

                FlatExpression::Identifier(name_x_and_y)
            }
            BooleanExpression::Not(box exp) => {
                let x = self.flatten_boolean_expression(symbols, statements_flattened, exp);
                FlatExpression::Sub(box FlatExpression::Number(T::one()), box x)
            }
            BooleanExpression::Value(b) => FlatExpression::Number(match b {
                true => T::from(1),
                false => T::from(0),
            }),
            BooleanExpression::FunctionCall(..) => unreachable!(),
            BooleanExpression::IfElse(box condition, box consequence, box alternative) => self
                .flatten_if_else_expression(
                    symbols,
                    statements_flattened,
                    condition,
                    consequence,
                    alternative,
                )[0]
            .clone(),
            BooleanExpression::Member(box s, id) => {
                self.flatten_member_expression(symbols, statements_flattened, s, id)[0].clone()
            }
            BooleanExpression::Select(box array, box index) => self
                .flatten_select_expression::<BooleanExpression<'ast, T>>(
                    symbols,
                    statements_flattened,
                    array,
                    index,
                )[0]
            .clone(),
        }
    }

    /// Flattens a function call
    ///
    /// # Arguments
    ///
    /// * `symbols` - Available functions in this context
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `id` - `Identifier of the function.
    /// * `return_types` - Types of the return values of the function
    /// * `param_expressions` - Arguments of this call
    fn flatten_function_call(
        &mut self,
        symbols: &TypedFunctionSymbols<'ast, T>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        id: FunctionIdentifier<'ast>,
        return_types: Vec<Type>,
        param_expressions: Vec<TypedExpression<'ast, T>>,
    ) -> FlatExpressionList<T> {
        let passed_signature = Signature::new()
            .inputs(param_expressions.iter().map(|e| e.get_type()).collect())
            .outputs(return_types);

        let key = FunctionKey::with_id(id).signature(passed_signature);

        let funct = self.get_function(&key, &symbols);

        let mut replacement_map = HashMap::new();

        // Handle complex parameters and assign values:
        // Rename Parameters, assign them to values in call. Resolve complex expressions with definitions
        let params_flattened = param_expressions
            .into_iter()
            .map(|param_expr| self.flatten_expression(symbols, statements_flattened, param_expr))
            .into_iter()
            .flat_map(|x| x)
            .collect::<Vec<_>>();

        for (concrete_argument, formal_argument) in
            params_flattened.into_iter().zip(funct.arguments)
        {
            let new_var = self.use_sym();
            statements_flattened.push(FlatStatement::Definition(new_var, concrete_argument));
            replacement_map.insert(formal_argument.id, new_var);
        }

        // Ensure renaming and correct returns:
        // add all flattened statements, adapt return statements

        let (mut return_statements, statements): (Vec<_>, Vec<_>) =
            funct.statements.into_iter().partition(|s| match s {
                FlatStatement::Return(..) => true,
                _ => false,
            });

        let statements: Vec<_> = statements
            .into_iter()
            .map(|stat| match stat {
                // set return statements as expression result
                FlatStatement::Return(..) => unreachable!(),
                FlatStatement::Definition(var, rhs) => {
                    let new_var = self.use_sym();
                    replacement_map.insert(var, new_var);
                    let new_rhs = rhs.apply_substitution(&replacement_map);
                    FlatStatement::Definition(new_var, new_rhs)
                }
                FlatStatement::Condition(lhs, rhs) => {
                    let new_lhs = lhs.apply_substitution(&replacement_map);
                    let new_rhs = rhs.apply_substitution(&replacement_map);
                    FlatStatement::Condition(new_lhs, new_rhs)
                }
                FlatStatement::Directive(d) => {
                    let new_outputs = d
                        .outputs
                        .into_iter()
                        .map(|o| {
                            let new_o = self.use_sym();
                            replacement_map.insert(o, new_o);
                            new_o
                        })
                        .collect();
                    let new_inputs = d
                        .inputs
                        .into_iter()
                        .map(|i| i.apply_substitution(&replacement_map))
                        .collect();
                    FlatStatement::Directive(FlatDirective {
                        outputs: new_outputs,
                        solver: d.solver,
                        inputs: new_inputs,
                    })
                }
            })
            .collect();

        statements_flattened.extend(statements);

        match return_statements.pop().unwrap() {
            FlatStatement::Return(list) => FlatExpressionList {
                expressions: list
                    .expressions
                    .into_iter()
                    .map(|x| x.apply_substitution(&replacement_map))
                    .collect(),
            },
            _ => unreachable!(),
        }
    }

    /// Flattens an expression
    ///
    /// # Arguments
    ///
    /// * `symbols` - Available functions in this context
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `expr` - `TypedExpression` that will be flattened.
    fn flatten_expression(
        &mut self,
        symbols: &TypedFunctionSymbols<'ast, T>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        expr: TypedExpression<'ast, T>,
    ) -> Vec<FlatExpression<T>> {
        match expr {
            TypedExpression::FieldElement(e) => {
                vec![self.flatten_field_expression(symbols, statements_flattened, e)]
            }
            TypedExpression::Boolean(e) => {
                vec![self.flatten_boolean_expression(symbols, statements_flattened, e)]
            }
            TypedExpression::Array(e) => match e.inner_type().clone() {
                Type::FieldElement => self
                    .flatten_array_expression::<FieldElementExpression<'ast, T>>(
                        symbols,
                        statements_flattened,
                        e,
                    ),
                Type::Boolean => self.flatten_array_expression::<BooleanExpression<'ast, T>>(
                    symbols,
                    statements_flattened,
                    e,
                ),
                Type::Array(..) => self.flatten_array_expression::<ArrayExpression<'ast, T>>(
                    symbols,
                    statements_flattened,
                    e,
                ),
                Type::Struct(..) => self.flatten_array_expression::<StructExpression<'ast, T>>(
                    symbols,
                    statements_flattened,
                    e,
                ),
            },
            TypedExpression::Struct(e) => {
                self.flatten_struct_expression(symbols, statements_flattened, e)
            }
        }
    }

    /// Flattens a field expression
    ///
    /// # Arguments
    ///
    /// * `symbols` - Available functions in this context
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `expr` - `FieldElementExpression` that will be flattened.
    fn flatten_field_expression(
        &mut self,
        symbols: &TypedFunctionSymbols<'ast, T>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        expr: FieldElementExpression<'ast, T>,
    ) -> FlatExpression<T> {
        match expr {
            FieldElementExpression::Number(x) => FlatExpression::Number(x), // force to be a field element
            FieldElementExpression::Identifier(x) => {
                FlatExpression::Identifier(self.layout.get(&x).unwrap().clone()[0])
            }
            FieldElementExpression::Add(box left, box right) => {
                let left_flattened =
                    self.flatten_field_expression(symbols, statements_flattened, left);
                let right_flattened =
                    self.flatten_field_expression(symbols, statements_flattened, right);
                let new_left = if left_flattened.is_linear() {
                    left_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened.push(FlatStatement::Definition(id, left_flattened));
                    FlatExpression::Identifier(id)
                };
                let new_right = if right_flattened.is_linear() {
                    right_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened.push(FlatStatement::Definition(id, right_flattened));
                    FlatExpression::Identifier(id)
                };
                FlatExpression::Add(box new_left, box new_right)
            }
            FieldElementExpression::Sub(box left, box right) => {
                let left_flattened =
                    self.flatten_field_expression(symbols, statements_flattened, left);
                let right_flattened =
                    self.flatten_field_expression(symbols, statements_flattened, right);

                let new_left = if left_flattened.is_linear() {
                    left_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened.push(FlatStatement::Definition(id, left_flattened));
                    FlatExpression::Identifier(id)
                };
                let new_right = if right_flattened.is_linear() {
                    right_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened.push(FlatStatement::Definition(id, right_flattened));
                    FlatExpression::Identifier(id)
                };

                FlatExpression::Sub(box new_left, box new_right)
            }
            FieldElementExpression::Mult(box left, box right) => {
                let left_flattened =
                    self.flatten_field_expression(symbols, statements_flattened, left);
                let right_flattened =
                    self.flatten_field_expression(symbols, statements_flattened, right);
                let new_left = if left_flattened.is_linear() {
                    left_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened.push(FlatStatement::Definition(id, left_flattened));
                    FlatExpression::Identifier(id)
                };
                let new_right = if right_flattened.is_linear() {
                    right_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened.push(FlatStatement::Definition(id, right_flattened));
                    FlatExpression::Identifier(id)
                };
                FlatExpression::Mult(box new_left, box new_right)
            }
            FieldElementExpression::Div(box left, box right) => {
                let left_flattened =
                    self.flatten_field_expression(symbols, statements_flattened, left);
                let right_flattened =
                    self.flatten_field_expression(symbols, statements_flattened, right);
                let new_left: FlatExpression<T> = {
                    let id = self.use_sym();
                    statements_flattened.push(FlatStatement::Definition(id, left_flattened));
                    id.into()
                };
                let new_right: FlatExpression<T> = {
                    let id = self.use_sym();
                    statements_flattened.push(FlatStatement::Definition(id, right_flattened));
                    id.into()
                };

                let invb = self.use_sym();
                let inverse = self.use_sym();

                // # invb = 1/b
                statements_flattened.push(FlatStatement::Directive(FlatDirective::new(
                    vec![invb],
                    Solver::Div,
                    vec![FlatExpression::Number(T::one()), new_right.clone()],
                )));

                // assert(invb * b == 1)
                statements_flattened.push(FlatStatement::Condition(
                    FlatExpression::Number(T::one()),
                    FlatExpression::Mult(box invb.into(), box new_right.clone().into()),
                ));

                // # c = a/b
                statements_flattened.push(FlatStatement::Directive(FlatDirective::new(
                    vec![inverse],
                    Solver::Div,
                    vec![new_left.clone(), new_right.clone()],
                )));

                // assert(c * b == a)
                statements_flattened.push(FlatStatement::Condition(
                    new_left.into(),
                    FlatExpression::Mult(box new_right, box inverse.into()),
                ));

                inverse.into()
            }
            FieldElementExpression::Pow(box base, box exponent) => {
                match exponent {
                    FieldElementExpression::Number(ref e) => {
                        // flatten the base expression
                        let base_flattened = self.flatten_field_expression(
                            symbols,
                            statements_flattened,
                            base.clone(),
                        );

                        // we require from the base to be linear
                        // TODO change that
                        assert!(base_flattened.is_linear());

                        let e = e.to_dec_string().parse::<usize>().unwrap();

                        // convert the exponent to bytes, big endian
                        let ebytes_be = e.to_be_bytes();
                        // convert the bytes to bits, remove leading zeroes (we only need powers up to the highest non-zero bit)
                        let ebits_be: Vec<_> = ebytes_be
                            .iter()
                            .flat_map(|byte| (0..8).rev().map(move |i| byte & (1 << i) != 0)) // byte to bit, big endian
                            .skip_while(|b| !b) // skip trailing false bits
                            .collect();

                        // reverse to start with the lowest bit first
                        let ebits_le: Vec<_> = ebits_be.into_iter().rev().collect();

                        // calculate all powers e**(2**i) by squaring
                        let powers: Vec<FlatExpression<T>> = ebits_le
                            .iter()
                            .scan(None, |state, _| {
                                match state {
                                    // the first element is the base
                                    None => {
                                        *state = Some(base_flattened.clone());
                                        Some(base_flattened.clone())
                                    }
                                    // any subsequent element is the square of the previous one
                                    Some(previous) => {
                                        // introduce a new variable
                                        let id = self.use_sym();
                                        // set it to the square of the previous one, stored in state
                                        statements_flattened.push(FlatStatement::Definition(
                                            id.clone(),
                                            FlatExpression::Mult(
                                                box previous.clone(),
                                                box previous.clone(),
                                            ),
                                        ));
                                        // store it in the state for later squaring
                                        *state = Some(FlatExpression::Identifier(id.clone()));
                                        // return it for later use constructing the result
                                        Some(FlatExpression::Identifier(id.clone()))
                                    }
                                }
                            })
                            .collect();

                        // construct the result iterating through the bits, multiplying by the associated power iff the bit is true
                        ebits_le.into_iter().zip(powers).fold(
                            FlatExpression::Number(T::from(1)), // initialise the result at 1. If we have no bits to itegrate through, we're computing x**0 == 1
                            |acc, (bit, power)| match bit {
                                true => {
                                    // update the result by introducing a new variable
                                    let id = self.use_sym();
                                    statements_flattened.push(FlatStatement::Definition(
                                        id,
                                        FlatExpression::Mult(box acc.clone(), box power), // set the new result to the current result times the current power
                                    ));
                                    FlatExpression::Identifier(id)
                                }
                                false => acc, // this bit is false, keep the previous result
                            },
                        )
                    }
                    _ => panic!("Expected number as pow exponent"),
                }
            }
            FieldElementExpression::IfElse(box condition, box consequence, box alternative) => self
                .flatten_if_else_expression(
                    symbols,
                    statements_flattened,
                    condition,
                    consequence,
                    alternative,
                )[0]
            .clone(),
            FieldElementExpression::FunctionCall(key, param_expressions) => {
                let exprs_flattened = self.flatten_function_call(
                    symbols,
                    statements_flattened,
                    key.id,
                    vec![Type::FieldElement],
                    param_expressions,
                );
                assert!(exprs_flattened.expressions.len() == 1); // outside of MultipleDefinition, FunctionCalls must return a single value
                exprs_flattened.expressions[0].clone()
            }
            FieldElementExpression::Member(box s, id) => {
                self.flatten_member_expression(symbols, statements_flattened, s, id)[0].clone()
            }
            FieldElementExpression::Select(box array, box index) => self
                .flatten_select_expression::<FieldElementExpression<'ast, T>>(
                    symbols,
                    statements_flattened,
                    array,
                    index,
                )[0]
            .clone(),
        }
    }

    /// Flattens an array expression
    ///
    /// # Arguments
    ///
    /// * `symbols` - Available functions in this context
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `expr` - `StructExpression` that will be flattened.
    fn flatten_struct_expression(
        &mut self,
        symbols: &TypedFunctionSymbols<'ast, T>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        expr: StructExpression<'ast, T>,
    ) -> Vec<FlatExpression<T>> {
        let ty = expr.get_type();
        let expected_output_size = expr.get_type().get_primitive_count();
        let members = expr.ty().clone();

        let res = match expr.into_inner() {
            StructExpressionInner::Identifier(x) => self
                .layout
                .get(&x)
                .unwrap()
                .iter()
                .map(|v| FlatExpression::Identifier(v.clone()))
                .collect(),
            StructExpressionInner::Value(values) => values
                .into_iter()
                .flat_map(|v| self.flatten_expression(symbols, statements_flattened, v))
                .collect(),
            StructExpressionInner::FunctionCall(key, param_expressions) => {
                let exprs_flattened = self.flatten_function_call(
                    symbols,
                    statements_flattened,
                    key.id,
                    vec![ty],
                    param_expressions,
                );
                exprs_flattened.expressions
            }
            StructExpressionInner::IfElse(box condition, box consequence, box alternative) => {
                members
                    .into_iter()
                    .flat_map(|member| match ty {
                        Type::FieldElement => FieldElementExpression::if_else(
                            condition.clone(),
                            FieldElementExpression::member(consequence.clone(), member.id.clone()),
                            FieldElementExpression::member(alternative.clone(), member.id.clone()),
                        )
                        .flatten(self, symbols, statements_flattened),
                        Type::Boolean => BooleanExpression::if_else(
                            condition.clone(),
                            BooleanExpression::member(consequence.clone(), member.id.clone()),
                            BooleanExpression::member(alternative.clone(), member.id.clone()),
                        )
                        .flatten(self, symbols, statements_flattened),
                        Type::Struct(..) => StructExpression::if_else(
                            condition.clone(),
                            StructExpression::member(consequence.clone(), member.id.clone()),
                            StructExpression::member(alternative.clone(), member.id.clone()),
                        )
                        .flatten(self, symbols, statements_flattened),
                        Type::Array(..) => ArrayExpression::if_else(
                            condition.clone(),
                            ArrayExpression::member(consequence.clone(), member.id.clone()),
                            ArrayExpression::member(alternative.clone(), member.id.clone()),
                        )
                        .flatten(self, symbols, statements_flattened),
                    })
                    .collect()
            }
            StructExpressionInner::Member(box s, id) => {
                self.flatten_member_expression(symbols, statements_flattened, s, id)
            }
            StructExpressionInner::Select(box array, box index) => self
                .flatten_select_expression::<StructExpression<'ast, T>>(
                    symbols,
                    statements_flattened,
                    array,
                    index,
                ),
        };

        assert_eq!(res.len(), expected_output_size);
        res
    }

    /// Flattens an array expression
    ///
    /// # Arguments
    ///
    /// * `symbols` - Available functions in this context
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `expr` - `ArrayExpression` that will be flattened.
    /// # Remarks
    /// * U is the inner type of the array
    fn flatten_array_expression<U: Flatten<'ast, T>>(
        &mut self,
        symbols: &HashMap<FunctionKey<'ast>, TypedFunctionSymbol<'ast, T>>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        expr: ArrayExpression<'ast, T>,
    ) -> Vec<FlatExpression<T>> {
        let ty = expr.get_type();

        let size = expr.size();

        match expr.into_inner() {
            ArrayExpressionInner::Identifier(x) => self
                .layout
                .get(&x)
                .unwrap()
                .iter()
                .map(|v| FlatExpression::Identifier(v.clone()))
                .collect(),
            ArrayExpressionInner::Value(values) => {
                assert_eq!(size, values.len());
                values
                    .into_iter()
                    .flat_map(|v| {
                        U::try_from(v)
                            .unwrap()
                            .flatten(self, symbols, statements_flattened)
                    })
                    .collect()
            }
            ArrayExpressionInner::FunctionCall(key, param_expressions) => {
                let exprs_flattened = self.flatten_function_call(
                    symbols,
                    statements_flattened,
                    key.id,
                    vec![ty],
                    param_expressions,
                );
                assert!(exprs_flattened.expressions.len() == size); // outside of MultipleDefinition, FunctionCalls must return a single value
                exprs_flattened.expressions
            }
            ArrayExpressionInner::IfElse(ref condition, ref consequence, ref alternative) => (0
                ..size)
                .flat_map(|i| {
                    U::if_else(
                        *condition.clone(),
                        U::select(
                            *consequence.clone(),
                            FieldElementExpression::Number(T::from(i)),
                        ),
                        U::select(
                            *alternative.clone(),
                            FieldElementExpression::Number(T::from(i)),
                        ),
                    )
                    .flatten(self, symbols, statements_flattened)
                })
                .collect(),
            ArrayExpressionInner::Member(box s, id) => {
                self.flatten_member_expression(symbols, statements_flattened, s, id)
            }
            ArrayExpressionInner::Select(box array, box index) => self
                .flatten_select_expression::<ArrayExpression<'ast, T>>(
                    symbols,
                    statements_flattened,
                    array,
                    index,
                ),
        }
    }

    /// Flattens a statement
    ///
    /// # Arguments
    ///
    /// * `symbols` - Available functions in this context
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `stat` - `TypedStatement` that will be flattened.
    fn flatten_statement(
        &mut self,
        symbols: &TypedFunctionSymbols<'ast, T>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        stat: TypedStatement<'ast, T>,
    ) {
        match stat {
            TypedStatement::Return(exprs) => {
                let flat_expressions = exprs
                    .into_iter()
                    .map(|expr| self.flatten_expression(symbols, statements_flattened, expr))
                    .flat_map(|x| x)
                    .collect::<Vec<_>>();

                statements_flattened.push(FlatStatement::Return(FlatExpressionList {
                    expressions: flat_expressions,
                }));
            }
            TypedStatement::Declaration(_) => {
                // declarations have already been checked
                ()
            }
            TypedStatement::Definition(assignee, expr) => {
                // define n variables with n the number of primitive types for v_type
                // assign them to the n primitive types for expr

                let rhs = self.flatten_expression(symbols, statements_flattened, expr);

                match assignee {
                    TypedAssignee::Identifier(ref v) => {
                        let vars = self.use_variable(&v);
                        // handle return of function call
                        statements_flattened.extend(
                            vars.into_iter()
                                .zip(rhs)
                                .map(|(v, e)| FlatStatement::Definition(v, e)),
                        );
                    }
                    TypedAssignee::Select(..) => unreachable!(
                        "array element redefs should have been replaced by array redefs in unroll"
                    ),
                    TypedAssignee::Member(..) => unreachable!(
                        "struct member redefs should have been replaced by struct redef in unroll"
                    ),
                }
            }
            TypedStatement::Condition(lhs, rhs) => {
                // flatten expr1 and expr2 to n flattened expressions with n the number of primitive types for expr1
                // add n conditions to check equality of the n expressions

                let lhs = self.flatten_expression(symbols, statements_flattened, lhs);
                let rhs = self.flatten_expression(symbols, statements_flattened, rhs);

                assert_eq!(lhs.len(), rhs.len());

                for (l, r) in lhs.into_iter().zip(rhs.into_iter()) {
                    if l.is_linear() {
                        statements_flattened.push(FlatStatement::Condition(l, r));
                    } else if r.is_linear() {
                        // swap so that left side is linear
                        statements_flattened.push(FlatStatement::Condition(r, l));
                    } else {
                        unimplemented!()
                    }
                }
            }
            TypedStatement::For(..) => unreachable!("static analyser should have unrolled"),
            TypedStatement::MultipleDefinition(vars, rhs) => {
                // flatten the right side to p = sum(var_i.type.primitive_count) expressions
                // define p new variables to the right side expressions

                let var_types = vars.iter().map(|v| v.get_type()).collect();

                match rhs {
                    TypedExpressionList::FunctionCall(key, exprs, _) => {
                        let rhs_flattened = self.flatten_function_call(
                            symbols,
                            statements_flattened,
                            &key.id,
                            var_types,
                            exprs,
                        );

                        let rhs = rhs_flattened.expressions.into_iter();

                        let vars = vars.into_iter().flat_map(|v| self.use_variable(&v));

                        statements_flattened
                            .extend(vars.zip(rhs).map(|(v, r)| FlatStatement::Definition(v, r)));
                    }
                }
            }
        }
    }

    /// Flattens a function symbol
    ///
    /// # Arguments
    ///
    /// * `funct` - `TypedFunctionSymbol` that will be flattened.
    ///
    /// # Remarks
    /// * Only "flat" symbols can be flattened here. Other function calls must have been inlined previously.
    fn flatten_function_symbol(&mut self, funct: TypedFunctionSymbol<'ast, T>) -> FlatFunction<T> {
        match funct {
            TypedFunctionSymbol::Flat(flat_function) => flat_function.synthetize(),
            _ => unreachable!("only local flat symbols can be flattened"),
        }
    }

    /// Flattens a function
    ///
    /// # Arguments
    ///
    /// * `symbols` - Available functions in this context
    /// * `funct` - `TypedFunction` that will be flattened
    fn flatten_function(
        &mut self,
        symbols: &TypedFunctionSymbols<'ast, T>,
        funct: TypedFunction<'ast, T>,
    ) -> FlatFunction<T> {
        self.layout = HashMap::new();

        self.next_var_idx = 0;
        let mut statements_flattened: Vec<FlatStatement<T>> = Vec::new();

        // push parameters
        let arguments_flattened = funct
            .arguments
            .into_iter()
            .flat_map(|p| self.use_parameter(&p))
            .collect();

        // flatten statements in functions and apply substitution
        for stat in funct.statements {
            self.flatten_statement(symbols, &mut statements_flattened, stat);
        }

        FlatFunction {
            arguments: arguments_flattened,
            statements: statements_flattened,
        }
    }

    /// Flattens a program
    ///
    /// # Arguments
    ///
    /// * `prog` - `TypedProgram` that will be flattened.
    fn flatten_program(&mut self, prog: TypedProgram<'ast, T>) -> FlatProg<T> {
        let main_module = prog.modules.get(&prog.main).unwrap();

        let main = main_module
            .functions
            .iter()
            .find(|(k, _)| k.id == "main")
            .unwrap()
            .1
            .clone();

        let symbols = &main_module.functions;

        let main_flattened = match main {
            TypedFunctionSymbol::Here(f) => self.flatten_function(&symbols, f),
            _ => unreachable!("main should be a typed function locally"),
        };

        FlatProg {
            main: main_flattened,
        }
    }

    /// Checks if the given name is a not used variable and returns a fresh variable.
    /// # Arguments
    ///
    /// * `name` - a String that holds the name of the variable
    fn use_variable(&mut self, variable: &Variable<'ast>) -> Vec<FlatVariable> {
        let vars = self.issue_new_variables(variable.get_type().get_primitive_count());

        self.layout.insert(variable.id.clone(), vars.clone());
        vars
    }

    fn use_parameter(&mut self, parameter: &Parameter<'ast>) -> Vec<FlatParameter> {
        let variables = self.use_variable(&parameter.id);

        variables
            .into_iter()
            .map(|v| FlatParameter {
                id: v,
                private: parameter.private,
            })
            .collect()
    }

    fn issue_new_variable(&mut self) -> FlatVariable {
        let var = FlatVariable::new(self.next_var_idx);
        self.next_var_idx += 1;
        var
    }

    fn issue_new_variables(&mut self, count: usize) -> Vec<FlatVariable> {
        (0..count).map(|_| self.issue_new_variable()).collect()
    }

    // create an internal variable. We do not register it in the layout
    fn use_sym(&mut self) -> FlatVariable {
        self.issue_new_variable()
    }

    fn get_function<'a>(
        &mut self,
        key: &'a FunctionKey<'ast>,
        symbols: &'a TypedFunctionSymbols<'ast, T>,
    ) -> FlatFunction<T> {
        let cached = self.flat_cache.get(&key).cloned();

        cached.unwrap_or_else(|| {
            let f = symbols.get(&key).unwrap().clone();
            let res = self.flatten_function_symbol(f);
            self.flat_cache.insert(key.clone(), res.clone());
            res
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typed_absy::types::Signature;
    use crate::typed_absy::types::Type;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn powers_zero() {
        // def main():
        //     field a = 7
        //     field b = a**0
        //     return b

        // def main():
        //     _0 = 7
        //     _1 = 1         // power flattening returns 1, definition introduces _7
        //     return _1
        let function = TypedFunction {
            arguments: vec![],
            statements: vec![
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("a".into())),
                    FieldElementExpression::Number(FieldPrime::from(7)).into(),
                ),
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("b".into())),
                    FieldElementExpression::Pow(
                        box FieldElementExpression::Identifier("a".into()),
                        box FieldElementExpression::Number(FieldPrime::from(0)),
                    )
                    .into(),
                ),
                TypedStatement::Return(vec![FieldElementExpression::Identifier("b".into()).into()]),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![Type::FieldElement],
            },
        };

        let mut flattener = Flattener::new();

        let expected = FlatFunction {
            arguments: vec![],
            statements: vec![
                FlatStatement::Definition(
                    FlatVariable::new(0),
                    FlatExpression::Number(FieldPrime::from(7)),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(1),
                    FlatExpression::Number(FieldPrime::from(1)),
                ),
                FlatStatement::Return(FlatExpressionList {
                    expressions: vec![FlatExpression::Identifier(FlatVariable::new(1))],
                }),
            ],
        };

        let flattened = flattener.flatten_function(&mut HashMap::new(), function);

        assert_eq!(flattened, expected);
    }

    #[test]
    fn power_one() {
        // def main():
        //     field a = 7
        //     field b = a**1
        //     return b

        // def main():
        //     _0 = 7
        //     _1 = 1 * _0     // x**1
        //     _2 = _1         // power flattening returns _1, definition introduces _2
        //     return _2
        let function = TypedFunction {
            arguments: vec![],
            statements: vec![
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("a".into())),
                    FieldElementExpression::Number(FieldPrime::from(7)).into(),
                ),
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("b".into())),
                    FieldElementExpression::Pow(
                        box FieldElementExpression::Identifier("a".into()),
                        box FieldElementExpression::Number(FieldPrime::from(1)),
                    )
                    .into(),
                ),
                TypedStatement::Return(vec![FieldElementExpression::Identifier("b".into()).into()]),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![Type::FieldElement],
            },
        };

        let mut flattener = Flattener::new();

        let expected = FlatFunction {
            arguments: vec![],
            statements: vec![
                FlatStatement::Definition(
                    FlatVariable::new(0),
                    FlatExpression::Number(FieldPrime::from(7)),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(1),
                    FlatExpression::Mult(
                        box FlatExpression::Number(FieldPrime::from(1)),
                        box FlatExpression::Identifier(FlatVariable::new(0)),
                    ),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(2),
                    FlatExpression::Identifier(FlatVariable::new(1)),
                ),
                FlatStatement::Return(FlatExpressionList {
                    expressions: vec![FlatExpression::Identifier(FlatVariable::new(2))],
                }),
            ],
        };

        let flattened = flattener.flatten_function(&mut HashMap::new(), function);

        assert_eq!(flattened, expected);
    }

    #[test]
    fn power_13() {
        // def main():
        //     field a = 7
        //     field b = a**13
        //     return b

        // we apply double and add
        // 13 == 0b1101
        // a ** 13 == a**(2**0 + 2**2 + 2**3) == a**1 * a**4 * a**8

        // a_0 = a * a      // a**2
        // a_1 = a_0 * a_0  // a**4
        // a_2 = a_1 * a_1  // a**8

        // a_3 = a * a_1    // a * a**4 == a**5
        // a_4 = a_3 * a_2  // a**5 * a**8 == a**13

        // def main():
        //     _0 = 7
        //     _1 = (_0 * _0)  // a**2
        //     _2 = (_1 * _1)  // a**4
        //     _3 = (_2 * _2)  // a**8
        //
        //     _4 = 1 * _0     // a
        //     _5 = _4 * _2    // a**5
        //     _6 = _5 * _3    // a**13
        //     _7 = _6         // power flattening returns _6, definition introduces _7
        //     return _7

        let function = TypedFunction {
            arguments: vec![],
            statements: vec![
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("a".into())),
                    FieldElementExpression::Number(FieldPrime::from(7)).into(),
                ),
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("b".into())),
                    FieldElementExpression::Pow(
                        box FieldElementExpression::Identifier("a".into()),
                        box FieldElementExpression::Number(FieldPrime::from(13)),
                    )
                    .into(),
                ),
                TypedStatement::Return(vec![FieldElementExpression::Identifier("b".into()).into()]),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![Type::FieldElement],
            },
        };

        let mut flattener = Flattener::new();

        let expected = FlatFunction {
            arguments: vec![],
            statements: vec![
                FlatStatement::Definition(
                    FlatVariable::new(0),
                    FlatExpression::Number(FieldPrime::from(7)),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(1),
                    FlatExpression::Mult(
                        box FlatExpression::Identifier(FlatVariable::new(0)),
                        box FlatExpression::Identifier(FlatVariable::new(0)),
                    ),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(2),
                    FlatExpression::Mult(
                        box FlatExpression::Identifier(FlatVariable::new(1)),
                        box FlatExpression::Identifier(FlatVariable::new(1)),
                    ),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(3),
                    FlatExpression::Mult(
                        box FlatExpression::Identifier(FlatVariable::new(2)),
                        box FlatExpression::Identifier(FlatVariable::new(2)),
                    ),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(4),
                    FlatExpression::Mult(
                        box FlatExpression::Number(FieldPrime::from(1)),
                        box FlatExpression::Identifier(FlatVariable::new(0)),
                    ),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(5),
                    FlatExpression::Mult(
                        box FlatExpression::Identifier(FlatVariable::new(4)),
                        box FlatExpression::Identifier(FlatVariable::new(2)),
                    ),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(6),
                    FlatExpression::Mult(
                        box FlatExpression::Identifier(FlatVariable::new(5)),
                        box FlatExpression::Identifier(FlatVariable::new(3)),
                    ),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(7),
                    FlatExpression::Identifier(FlatVariable::new(6)),
                ),
                FlatStatement::Return(FlatExpressionList {
                    expressions: vec![FlatExpression::Identifier(FlatVariable::new(7))],
                }),
            ],
        };

        let flattened = flattener.flatten_function(&mut HashMap::new(), function);

        assert_eq!(flattened, expected);
    }

    #[test]
    fn if_else() {
        let expression = FieldElementExpression::IfElse(
            box BooleanExpression::FieldEq(
                box FieldElementExpression::Number(FieldPrime::from(32)),
                box FieldElementExpression::Number(FieldPrime::from(4)),
            ),
            box FieldElementExpression::Number(FieldPrime::from(12)),
            box FieldElementExpression::Number(FieldPrime::from(51)),
        );

        let mut flattener = Flattener::new();

        flattener.flatten_field_expression(&HashMap::new(), &mut vec![], expression);
    }

    #[test]
    fn geq_leq() {
        let mut flattener = Flattener::new();
        let expression_le = BooleanExpression::Le(
            box FieldElementExpression::Number(FieldPrime::from(32)),
            box FieldElementExpression::Number(FieldPrime::from(4)),
        );
        flattener.flatten_boolean_expression(&HashMap::new(), &mut vec![], expression_le);

        let mut flattener = Flattener::new();
        let expression_ge = BooleanExpression::Ge(
            box FieldElementExpression::Number(FieldPrime::from(32)),
            box FieldElementExpression::Number(FieldPrime::from(4)),
        );
        flattener.flatten_boolean_expression(&HashMap::new(), &mut vec![], expression_ge);
    }

    #[test]
    fn bool_and() {
        let mut flattener = Flattener::new();

        let expression = FieldElementExpression::IfElse(
            box BooleanExpression::And(
                box BooleanExpression::FieldEq(
                    box FieldElementExpression::Number(FieldPrime::from(4)),
                    box FieldElementExpression::Number(FieldPrime::from(4)),
                ),
                box BooleanExpression::Lt(
                    box FieldElementExpression::Number(FieldPrime::from(4)),
                    box FieldElementExpression::Number(FieldPrime::from(20)),
                ),
            ),
            box FieldElementExpression::Number(FieldPrime::from(12)),
            box FieldElementExpression::Number(FieldPrime::from(51)),
        );

        flattener.flatten_field_expression(&HashMap::new(), &mut vec![], expression);
    }

    #[test]
    fn div() {
        // a = 5 / b / b

        let mut flattener = Flattener::new();
        let mut statements_flattened = vec![];

        let definition = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_element("b".into())),
            FieldElementExpression::Number(FieldPrime::from(42)).into(),
        );

        let statement = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_element("a".into())),
            FieldElementExpression::Div(
                box FieldElementExpression::Div(
                    box FieldElementExpression::Number(FieldPrime::from(5)),
                    box FieldElementExpression::Identifier("b".into()),
                ),
                box FieldElementExpression::Identifier("b".into()),
            )
            .into(),
        );

        flattener.flatten_statement(&HashMap::new(), &mut statements_flattened, definition);

        flattener.flatten_statement(&HashMap::new(), &mut statements_flattened, statement);

        // define b
        let b = FlatVariable::new(0);
        // define new wires for members of Div
        let five = FlatVariable::new(1);
        let b0 = FlatVariable::new(2);
        // Define inverse of denominator to prevent div by 0
        let invb0 = FlatVariable::new(3);
        // Define inverse
        let sym_0 = FlatVariable::new(4);
        // Define result, which is first member to next Div
        let sym_1 = FlatVariable::new(5);
        // Define second member
        let b1 = FlatVariable::new(6);
        // Define inverse of denominator to prevent div by 0
        let invb1 = FlatVariable::new(7);
        // Define inverse
        let sym_2 = FlatVariable::new(8);
        // Define left hand side
        let a = FlatVariable::new(9);

        assert_eq!(
            statements_flattened,
            vec![
                FlatStatement::Definition(b, FlatExpression::Number(FieldPrime::from(42))),
                // inputs to first div (5/b)
                FlatStatement::Definition(five, FlatExpression::Number(FieldPrime::from(5))),
                FlatStatement::Definition(b0, b.into()),
                // check div by 0
                FlatStatement::Directive(FlatDirective::new(
                    vec![invb0],
                    Solver::Div,
                    vec![FlatExpression::Number(FieldPrime::from(1)), b0.into()]
                )),
                FlatStatement::Condition(
                    FlatExpression::Number(FieldPrime::from(1)),
                    FlatExpression::Mult(box invb0.into(), box b0.into()),
                ),
                // execute div
                FlatStatement::Directive(FlatDirective::new(
                    vec![sym_0],
                    Solver::Div,
                    vec![five, b0]
                )),
                FlatStatement::Condition(
                    five.into(),
                    FlatExpression::Mult(box b0.into(), box sym_0.into()),
                ),
                // inputs to second div (res/b)
                FlatStatement::Definition(sym_1, sym_0.into()),
                FlatStatement::Definition(b1, b.into()),
                // check div by 0
                FlatStatement::Directive(FlatDirective::new(
                    vec![invb1],
                    Solver::Div,
                    vec![FlatExpression::Number(FieldPrime::from(1)), b1.into()]
                )),
                FlatStatement::Condition(
                    FlatExpression::Number(FieldPrime::from(1)),
                    FlatExpression::Mult(box invb1.into(), box b1.into()),
                ),
                // execute div
                FlatStatement::Directive(FlatDirective::new(
                    vec![sym_2],
                    Solver::Div,
                    vec![sym_1, b1]
                )),
                FlatStatement::Condition(
                    sym_1.into(),
                    FlatExpression::Mult(box b1.into(), box sym_2.into()),
                ),
                // result
                FlatStatement::Definition(a, sym_2.into()),
            ]
        );
    }

    #[test]
    fn field_array() {
        // foo = [ , , ]

        let mut flattener = Flattener::new();
        let mut statements_flattened = vec![];
        let statement = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_array("foo".into(), 3)),
            ArrayExpressionInner::Value(vec![
                FieldElementExpression::Number(FieldPrime::from(1)).into(),
                FieldElementExpression::Number(FieldPrime::from(2)).into(),
                FieldElementExpression::Number(FieldPrime::from(3)).into(),
            ])
            .annotate(Type::FieldElement, 3)
            .into(),
        );
        let expression =
            ArrayExpressionInner::Identifier("foo".into()).annotate(Type::FieldElement, 3);

        flattener.flatten_statement(&HashMap::new(), &mut statements_flattened, statement);

        let expressions = flattener.flatten_array_expression::<FieldElementExpression<_>>(
            &HashMap::new(),
            &mut statements_flattened,
            expression,
        );

        assert_eq!(
            expressions,
            vec![
                FlatExpression::Identifier(FlatVariable::new(0)),
                FlatExpression::Identifier(FlatVariable::new(1)),
                FlatExpression::Identifier(FlatVariable::new(2)),
            ]
        );
    }

    #[test]
    fn array_definition() {
        // field[3] foo = [1, 2, 3]
        let mut flattener = Flattener::new();
        let mut statements_flattened = vec![];
        let statement = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_array("foo".into(), 3)),
            ArrayExpressionInner::Value(vec![
                FieldElementExpression::Number(FieldPrime::from(1)).into(),
                FieldElementExpression::Number(FieldPrime::from(2)).into(),
                FieldElementExpression::Number(FieldPrime::from(3)).into(),
            ])
            .annotate(Type::FieldElement, 3)
            .into(),
        );

        flattener.flatten_statement(&HashMap::new(), &mut statements_flattened, statement);

        assert_eq!(
            statements_flattened,
            vec![
                FlatStatement::Definition(
                    FlatVariable::new(0),
                    FlatExpression::Number(FieldPrime::from(1))
                ),
                FlatStatement::Definition(
                    FlatVariable::new(1),
                    FlatExpression::Number(FieldPrime::from(2))
                ),
                FlatStatement::Definition(
                    FlatVariable::new(2),
                    FlatExpression::Number(FieldPrime::from(3))
                ),
            ]
        );
    }

    #[test]
    fn array_selection() {
        // field[3] foo = [1, 2, 3]
        // foo[1]

        let mut flattener = Flattener::new();
        let mut statements_flattened = vec![];
        let statement = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_array("foo".into(), 3)),
            ArrayExpressionInner::Value(vec![
                FieldElementExpression::Number(FieldPrime::from(1)).into(),
                FieldElementExpression::Number(FieldPrime::from(2)).into(),
                FieldElementExpression::Number(FieldPrime::from(3)).into(),
            ])
            .annotate(Type::FieldElement, 3)
            .into(),
        );

        let expression = FieldElementExpression::Select(
            box ArrayExpressionInner::Identifier("foo".into()).annotate(Type::FieldElement, 3),
            box FieldElementExpression::Number(FieldPrime::from(1)),
        );

        flattener.flatten_statement(&HashMap::new(), &mut statements_flattened, statement);

        let flat_expression = flattener.flatten_field_expression(
            &HashMap::new(),
            &mut statements_flattened,
            expression,
        );

        assert_eq!(
            flat_expression,
            FlatExpression::Identifier(FlatVariable::new(1)),
        );
    }

    #[test]
    fn array_sum() {
        // field[3] foo = [1, 2, 3]
        // bar = foo[0] + foo[1] + foo[2]
        // we don't optimise detecting constants, this will be done in an optimiser pass

        let mut flattener = Flattener::new();

        let mut statements_flattened = vec![];
        let def = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_array("foo".into(), 3)),
            ArrayExpressionInner::Value(vec![
                FieldElementExpression::Number(FieldPrime::from(1)).into(),
                FieldElementExpression::Number(FieldPrime::from(2)).into(),
                FieldElementExpression::Number(FieldPrime::from(3)).into(),
            ])
            .annotate(Type::FieldElement, 3)
            .into(),
        );

        let sum = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_element("bar".into())),
            FieldElementExpression::Add(
                box FieldElementExpression::Add(
                    box FieldElementExpression::Select(
                        box ArrayExpressionInner::Identifier("foo".into())
                            .annotate(Type::FieldElement, 3),
                        box FieldElementExpression::Number(FieldPrime::from(0)),
                    ),
                    box FieldElementExpression::Select(
                        box ArrayExpressionInner::Identifier("foo".into())
                            .annotate(Type::FieldElement, 3),
                        box FieldElementExpression::Number(FieldPrime::from(1)),
                    ),
                ),
                box FieldElementExpression::Select(
                    box ArrayExpressionInner::Identifier("foo".into())
                        .annotate(Type::FieldElement, 3),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                ),
            )
            .into(),
        );

        flattener.flatten_statement(&HashMap::new(), &mut statements_flattened, def);

        flattener.flatten_statement(&HashMap::new(), &mut statements_flattened, sum);

        assert_eq!(
            statements_flattened[3],
            FlatStatement::Definition(
                FlatVariable::new(3),
                FlatExpression::Add(
                    box FlatExpression::Add(
                        box FlatExpression::Identifier(FlatVariable::new(0)),
                        box FlatExpression::Identifier(FlatVariable::new(1)),
                    ),
                    box FlatExpression::Identifier(FlatVariable::new(2)),
                )
            )
        );
    }

    #[test]
    fn array_of_array_sum() {
        // field[2][2] foo = [[1, 2], [3, 4]]
        // bar = foo[0][0] + foo[0][1] + foo[1][0] + foo[1][1]
        // we don't optimise detecting constants, this will be done in an optimiser pass

        let mut flattener = Flattener::new();

        let mut statements_flattened = vec![];
        let def = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_array("foo".into(), 4)),
            ArrayExpressionInner::Value(vec![
                ArrayExpressionInner::Value(vec![
                    FieldElementExpression::Number(FieldPrime::from(1)).into(),
                    FieldElementExpression::Number(FieldPrime::from(2)).into(),
                ])
                .annotate(Type::FieldElement, 2)
                .into(),
                ArrayExpressionInner::Value(vec![
                    FieldElementExpression::Number(FieldPrime::from(3)).into(),
                    FieldElementExpression::Number(FieldPrime::from(4)).into(),
                ])
                .annotate(Type::FieldElement, 2)
                .into(),
            ])
            .annotate(Type::array(Type::FieldElement, 2), 2)
            .into(),
        );

        let sum = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_element("bar".into())),
            FieldElementExpression::Add(
                box FieldElementExpression::Add(
                    box FieldElementExpression::Add(
                        box FieldElementExpression::Select(
                            box ArrayExpressionInner::Select(
                                box ArrayExpressionInner::Identifier("foo".into())
                                    .annotate(Type::array(Type::FieldElement, 2), 2),
                                box FieldElementExpression::Number(FieldPrime::from(0)),
                            )
                            .annotate(Type::FieldElement, 2),
                            box FieldElementExpression::Number(FieldPrime::from(0)),
                        ),
                        box FieldElementExpression::Select(
                            box ArrayExpressionInner::Select(
                                box ArrayExpressionInner::Identifier("foo".into())
                                    .annotate(Type::array(Type::FieldElement, 2), 2),
                                box FieldElementExpression::Number(FieldPrime::from(0)),
                            )
                            .annotate(Type::FieldElement, 2),
                            box FieldElementExpression::Number(FieldPrime::from(1)),
                        ),
                    ),
                    box FieldElementExpression::Select(
                        box ArrayExpressionInner::Select(
                            box ArrayExpressionInner::Identifier("foo".into())
                                .annotate(Type::array(Type::FieldElement, 2), 2),
                            box FieldElementExpression::Number(FieldPrime::from(1)),
                        )
                        .annotate(Type::FieldElement, 2),
                        box FieldElementExpression::Number(FieldPrime::from(0)),
                    ),
                ),
                box FieldElementExpression::Select(
                    box ArrayExpressionInner::Select(
                        box ArrayExpressionInner::Identifier("foo".into())
                            .annotate(Type::array(Type::FieldElement, 2), 2),
                        box FieldElementExpression::Number(FieldPrime::from(1)),
                    )
                    .annotate(Type::FieldElement, 2),
                    box FieldElementExpression::Number(FieldPrime::from(1)),
                ),
            )
            .into(),
        );

        flattener.flatten_statement(&HashMap::new(), &mut statements_flattened, def);

        flattener.flatten_statement(&HashMap::new(), &mut statements_flattened, sum);

        assert_eq!(
            statements_flattened[4],
            FlatStatement::Definition(
                FlatVariable::new(4),
                FlatExpression::Add(
                    box FlatExpression::Add(
                        box FlatExpression::Add(
                            box FlatExpression::Identifier(FlatVariable::new(0)),
                            box FlatExpression::Identifier(FlatVariable::new(1)),
                        ),
                        box FlatExpression::Identifier(FlatVariable::new(2))
                    ),
                    box FlatExpression::Identifier(FlatVariable::new(3)),
                )
            )
        );
    }

    #[test]
    fn array_if() {
        // if 1 == 1 then [1] else [3] fi
        let with_arrays = {
            let mut flattener = Flattener::new();
            let mut statements_flattened = vec![];

            let e = ArrayExpressionInner::IfElse(
                box BooleanExpression::FieldEq(
                    box FieldElementExpression::Number(FieldPrime::from(1)),
                    box FieldElementExpression::Number(FieldPrime::from(1)),
                ),
                box ArrayExpressionInner::Value(vec![FieldElementExpression::Number(
                    FieldPrime::from(1),
                )
                .into()])
                .annotate(Type::FieldElement, 1),
                box ArrayExpressionInner::Value(vec![FieldElementExpression::Number(
                    FieldPrime::from(3),
                )
                .into()])
                .annotate(Type::FieldElement, 2),
            )
            .annotate(Type::FieldElement, 1);

            (
                flattener.flatten_array_expression::<FieldElementExpression<_>>(
                    &HashMap::new(),
                    &mut statements_flattened,
                    e,
                )[0]
                .clone(),
                statements_flattened,
            )
        };

        let without_arrays = {
            let mut statements_flattened = vec![];
            let mut flattener = Flattener::new();
            // if 1 == 1 then 1 else 3 fi
            let e = FieldElementExpression::IfElse(
                box BooleanExpression::FieldEq(
                    box FieldElementExpression::Number(FieldPrime::from(1)),
                    box FieldElementExpression::Number(FieldPrime::from(1)),
                ),
                box FieldElementExpression::Number(FieldPrime::from(1)),
                box FieldElementExpression::Number(FieldPrime::from(3)),
            );

            (
                flattener.flatten_field_expression(&HashMap::new(), &mut statements_flattened, e),
                statements_flattened,
            )
        };

        assert_eq!(with_arrays, without_arrays);
    }

    #[test]
    fn next_variable() {
        let mut flattener: Flattener<FieldPrime> = Flattener::new();
        assert_eq!(
            vec![FlatVariable::new(0)],
            flattener.use_variable(&Variable::field_element("a".into()))
        );
        assert_eq!(
            flattener.layout.get(&"a".into()),
            Some(&vec![FlatVariable::new(0)])
        );
        assert_eq!(
            vec![FlatVariable::new(1)],
            flattener.use_variable(&Variable::field_element("a".into()))
        );
        assert_eq!(
            flattener.layout.get(&"a".into()),
            Some(&vec![FlatVariable::new(1)])
        );
        assert_eq!(
            vec![FlatVariable::new(2)],
            flattener.use_variable(&Variable::field_element("a".into()))
        );
        assert_eq!(
            flattener.layout.get(&"a".into()),
            Some(&vec![FlatVariable::new(2)])
        );
    }
}
