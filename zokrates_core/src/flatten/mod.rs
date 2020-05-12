//! Module containing the `Flattener` to process a program that is R1CS-able.
//!
//! @file flatten.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

use crate::flat_absy::*;
use crate::solvers::Solver;
use crate::zir::types::{FunctionIdentifier, FunctionKey, Signature, Type};
use crate::zir::*;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::convert::TryFrom;
use zokrates_field::Field;

struct FlatStatements<T: Field>(Vec<FlatStatement<T>>);

impl<T: Field> std::iter::Extend<FlatStatement<T>> for FlatStatements<T> {
    fn extend<U: IntoIterator<Item = FlatStatement<T>>>(&mut self, iter: U) {
        for elem in iter {
            self.push(elem);
        }
    }
}

impl<T: Field> FlatStatements<T> {
    fn push(&mut self, e: FlatStatement<T>) {
        match &e {
            FlatStatement::Definition(l, FlatExpression::Identifier(_)) => {
                println!("{}", e);
            }
            _ => {}
        };
        self.0.push(e)
    }

    fn new() -> Self {
        Self(vec![])
    }
}

/// Flattener, computes flattened program.
#[derive(Debug)]
pub struct Flattener<'ast, T: Field> {
    /// Index of the next introduced variable while processing the program.
    next_var_idx: usize,
    /// `FlatVariable`s corresponding to each `Identifier`
    layout: HashMap<Identifier<'ast>, FlatVariable>,
    /// Cached `FlatFunction`s to avoid re-flattening them
    flat_cache: HashMap<FunctionKey<'ast>, FlatFunction<T>>,
    /// Cached bit decompositions to avoid re-generating them
    bits_cache: HashMap<FlatExpression<T>, Vec<FlatExpression<T>>>,
    depth: usize,
}

trait FlattenOutput<T: Field>: Sized {
    fn branches(self, other: Self) -> (Self, Self);

    fn flat(&self) -> Vec<FlatExpression<T>>;
}

impl<T: Field> FlattenOutput<T> for FlatExpression<T> {
    fn branches(self, other: Self) -> (Self, Self) {
        (self, other)
    }

    fn flat(&self) -> Vec<FlatExpression<T>> {
        vec![self.clone()]
    }
}

impl<T: Field> FlattenOutput<T> for FlatUExpression<T> {
    fn branches(self, other: Self) -> (Self, Self) {
        let left_bits = self.bits.unwrap();
        let right_bits = other.bits.unwrap();
        let size = std::cmp::max(left_bits.len(), right_bits.len());

        let left_bits = (0..size - left_bits.len())
            .map(|_| FlatExpression::Number(T::from(0)))
            .chain(left_bits)
            .collect();
        let right_bits = (0..size - right_bits.len())
            .map(|_| FlatExpression::Number(T::from(0)))
            .chain(right_bits)
            .collect();

        (
            FlatUExpression {
                bits: Some(left_bits),
                ..self
            },
            FlatUExpression {
                bits: Some(right_bits),
                ..other
            },
        )
    }

    fn flat(&self) -> Vec<FlatExpression<T>> {
        self.bits
            .clone()
            .unwrap()
            .clone()
            .into_iter()
            .chain(std::iter::once(self.field.clone().unwrap()))
            .collect()
    }
}

// We introduce a trait in order to make it possible to make flattening `e` generic over the type of `e`

trait Flatten<'ast, T: Field>: TryFrom<ZirExpression<'ast, T>, Error = ()> + IfElse<'ast, T> {
    type Output: FlattenOutput<T>;

    fn flatten(
        self,
        flattener: &mut Flattener<'ast, T>,
        symbols: &ZirFunctionSymbols<'ast, T>,
        statements_flattened: &mut FlatStatements<T>,
    ) -> Self::Output;
}

impl<'ast, T: Field> Flatten<'ast, T> for FieldElementExpression<'ast, T> {
    type Output = FlatExpression<T>;

    fn flatten(
        self,
        flattener: &mut Flattener<'ast, T>,
        symbols: &ZirFunctionSymbols<'ast, T>,
        statements_flattened: &mut FlatStatements<T>,
    ) -> Self::Output {
        flattener.flatten_field_expression(symbols, statements_flattened, self)
    }
}

impl<'ast, T: Field> Flatten<'ast, T> for UExpression<'ast, T> {
    type Output = FlatUExpression<T>;

    fn flatten(
        self,
        flattener: &mut Flattener<'ast, T>,
        symbols: &ZirFunctionSymbols<'ast, T>,
        statements_flattened: &mut FlatStatements<T>,
    ) -> Self::Output {
        flattener.flatten_uint_expression(symbols, statements_flattened, self)
    }
}

impl<'ast, T: Field> Flatten<'ast, T> for BooleanExpression<'ast, T> {
    type Output = FlatExpression<T>;

    fn flatten(
        self,
        flattener: &mut Flattener<'ast, T>,
        symbols: &ZirFunctionSymbols<'ast, T>,
        statements_flattened: &mut FlatStatements<T>,
    ) -> Self::Output {
        flattener.flatten_boolean_expression(symbols, statements_flattened, self)
    }
}

#[derive(Clone, Debug)]
struct FlatUExpression<T: Field> {
    field: Option<FlatExpression<T>>,
    bits: Option<Vec<FlatExpression<T>>>,
}

impl<T: Field> FlatUExpression<T> {
    fn default() -> Self {
        FlatUExpression {
            field: None,
            bits: None,
        }
    }
}

impl<T: Field> FlatUExpression<T> {
    fn field<U: Into<Option<FlatExpression<T>>>>(mut self, e: U) -> Self {
        self.field = e.into();
        self
    }

    fn bits<U: Into<Option<Vec<FlatExpression<T>>>>>(mut self, e: U) -> Self {
        self.bits = e.into();
        self
    }

    fn with_field<U: Into<Option<FlatExpression<T>>>>(e: U) -> Self {
        Self::default().field(e)
    }

    fn with_bits<U: Into<Option<Vec<FlatExpression<T>>>>>(e: U) -> Self {
        Self::default().bits(e)
    }

    fn get_field_unchecked(self) -> FlatExpression<T> {
        match self.field {
            Some(f) => f,
            None => match self.bits {
                Some(bits) => {
                    //assert_eq!(bits.len(), 32);
                    bits.into_iter().rev().enumerate().fold(
                        FlatExpression::Number(T::from(0)),
                        |acc, (index, bit)| {
                            FlatExpression::Add(
                                box acc,
                                box FlatExpression::Mult(
                                    box FlatExpression::Number(T::from(2).pow(index)),
                                    box bit,
                                ),
                            )
                        },
                    )
                }
                None => unreachable!(),
            },
        }
    }
}

impl<'ast, T: Field> Flattener<'ast, T> {
    pub fn flatten(p: ZirProgram<'ast, T>) -> FlatProg<T> {
        Flattener::new().flatten_program(p)
    }

    /// Returns a `Flattener` with fresh `layout`.

    fn new() -> Flattener<'ast, T> {
        Flattener {
            next_var_idx: 0,
            layout: HashMap::new(),
            flat_cache: HashMap::new(),
            bits_cache: HashMap::new(),
            depth: 0,
        }
    }

    fn define(
        &mut self,
        e: FlatExpression<T>,
        statements_flattened: &mut FlatStatements<T>,
    ) -> FlatVariable {
        match e {
            FlatExpression::Identifier(id) => id.into(),
            e => {
                let res = self.use_sym();
                statements_flattened.push(FlatStatement::Definition(res, e));
                res
            }
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
        symbols: &ZirFunctionSymbols<'ast, T>,
        statements_flattened: &mut FlatStatements<T>,
        condition: BooleanExpression<'ast, T>,
        consequence: U,
        alternative: U,
    ) -> FlatUExpression<T> {
        let condition = self.flatten_boolean_expression(symbols, statements_flattened, condition);

        let consequence = consequence.flatten(self, symbols, statements_flattened);

        let alternative = alternative.flatten(self, symbols, statements_flattened);

        let condition_id = self.use_sym();
        statements_flattened.push(FlatStatement::Definition(condition_id, condition));

        let consequence = consequence.flat();
        let alternative = alternative.flat();

        let size = consequence.len();

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

        let mut res: Vec<_> = res.into_iter().map(|r| r.into()).collect();

        FlatUExpression {
            field: Some(res.pop().unwrap()),
            bits: Some(res),
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
        symbols: &ZirFunctionSymbols<'ast, T>,
        statements_flattened: &mut FlatStatements<T>,
        expression: BooleanExpression<'ast, T>,
    ) -> FlatExpression<T> {
        // those will be booleans in the future
        match expression {
            BooleanExpression::Identifier(x) => {
                FlatExpression::Identifier(self.layout.get(&x).unwrap().clone())
            }
            BooleanExpression::Lt(box lhs, box rhs) => {
                // Get the bit width to know the size of the binary decompositions for this Field
                let bit_width = T::get_required_bits();
                let safe_width = bit_width - 2; // making sure we don't overflow, assert here?

                // We know from semantic checking that lhs and rhs have the same type
                // What the expression will flatten to depends on that type

                let lhs_flattened =
                    self.flatten_field_expression(symbols, statements_flattened, lhs);
                let rhs_flattened =
                    self.flatten_field_expression(symbols, statements_flattened, rhs);

                // lhs
                let lhs_id = self.define(lhs_flattened, statements_flattened);

                // check that lhs and rhs are within the right range, i.e., their higher two bits are zero. We use big-endian so they are at positions 0 and 1

                // lhs
                {
                    // define variables for the bits
                    let lhs_bits_be: Vec<FlatVariable> =
                        (0..safe_width).map(|_| self.use_sym()).collect();

                    // add a directive to get the bits
                    statements_flattened.push(FlatStatement::Directive(FlatDirective::new(
                        lhs_bits_be.clone(),
                        Solver::bits(safe_width),
                        vec![lhs_id],
                    )));

                    // bitness checks
                    for i in 0..safe_width {
                        statements_flattened.push(FlatStatement::Condition(
                            FlatExpression::Identifier(lhs_bits_be[i]),
                            FlatExpression::Mult(
                                box FlatExpression::Identifier(lhs_bits_be[i]),
                                box FlatExpression::Identifier(lhs_bits_be[i]),
                            ),
                        ));
                    }

                    // bit decomposition check
                    let mut lhs_sum = FlatExpression::Number(T::from(0));

                    for i in 0..safe_width {
                        lhs_sum = FlatExpression::Add(
                            box lhs_sum,
                            box FlatExpression::Mult(
                                box FlatExpression::Identifier(lhs_bits_be[i]),
                                box FlatExpression::Number(T::from(2).pow(safe_width - i - 1)),
                            ),
                        );
                    }

                    statements_flattened.push(FlatStatement::Condition(
                        FlatExpression::Identifier(lhs_id),
                        lhs_sum,
                    ));
                }

                // rhs
                let rhs_id = self.define(rhs_flattened, statements_flattened);

                // rhs
                {
                    // define variables for the bits
                    let rhs_bits_be: Vec<FlatVariable> =
                        (0..safe_width).map(|_| self.use_sym()).collect();

                    // add a directive to get the bits
                    statements_flattened.push(FlatStatement::Directive(FlatDirective::new(
                        rhs_bits_be.clone(),
                        Solver::bits(safe_width),
                        vec![rhs_id],
                    )));

                    // bitness checks
                    for i in 0..safe_width {
                        statements_flattened.push(FlatStatement::Condition(
                            FlatExpression::Identifier(rhs_bits_be[i]),
                            FlatExpression::Mult(
                                box FlatExpression::Identifier(rhs_bits_be[i]),
                                box FlatExpression::Identifier(rhs_bits_be[i]),
                            ),
                        ));
                    }

                    // bit decomposition check
                    let mut rhs_sum = FlatExpression::Number(T::from(0));

                    for i in 0..safe_width {
                        rhs_sum = FlatExpression::Add(
                            box rhs_sum,
                            box FlatExpression::Mult(
                                box FlatExpression::Identifier(rhs_bits_be[i]),
                                box FlatExpression::Number(T::from(2).pow(safe_width - i - 1)),
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
                    (0..bit_width).map(|_| self.use_sym()).collect();

                // add a directive to get the bits
                statements_flattened.push(FlatStatement::Directive(FlatDirective::new(
                    sub_bits_be.clone(),
                    Solver::bits(bit_width),
                    vec![subtraction_result.clone()],
                )));

                // bitness checks
                for i in 0..bit_width {
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

                for i in 0..bit_width {
                    expr = FlatExpression::Add(
                        box expr,
                        box FlatExpression::Mult(
                            box FlatExpression::Identifier(sub_bits_be[i]),
                            box FlatExpression::Number(T::from(2).pow(bit_width - i - 1)),
                        ),
                    );
                }

                statements_flattened.push(FlatStatement::Condition(subtraction_result, expr));

                FlatExpression::Identifier(sub_bits_be[bit_width - 1])
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
                let x = self.flatten_boolean_expression(symbols, statements_flattened, lhs);
                let y = self.flatten_boolean_expression(symbols, statements_flattened, rhs);
                assert!(x.is_linear() && y.is_linear());
                let name_x_or_y = self.use_sym();
                statements_flattened.push(FlatStatement::Directive(FlatDirective {
                    solver: Solver::Or,
                    outputs: vec![name_x_or_y],
                    inputs: vec![x.clone(), y.clone()],
                }));
                statements_flattened.push(FlatStatement::Condition(
                    FlatExpression::Add(
                        box x.clone(),
                        box FlatExpression::Sub(box y.clone(), box name_x_or_y.clone().into()),
                    ),
                    FlatExpression::Mult(box x.clone(), box y.clone()),
                ));
                name_x_or_y.into()
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
            BooleanExpression::IfElse(box condition, box consequence, box alternative) => self
                .flatten_if_else_expression(
                    symbols,
                    statements_flattened,
                    condition,
                    consequence,
                    alternative,
                )
                .get_field_unchecked()
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
        symbols: &ZirFunctionSymbols<'ast, T>,
        statements_flattened: &mut FlatStatements<T>,
        id: FunctionIdentifier<'ast>,
        return_types: Vec<Type>,
        param_expressions: Vec<ZirExpression<'ast, T>>,
    ) -> Vec<FlatUExpression<T>> {
        let passed_signature = Signature::new()
            .inputs(param_expressions.iter().map(|e| e.get_type()).collect())
            .outputs(return_types);

        let key = FunctionKey::with_id(id).signature(passed_signature);

        let funct = self.get_embed(&key, &symbols);

        if funct == crate::embed::FlatEmbed::U32ToBits {
            assert_eq!(param_expressions.len(), 1);
            let mut param_expressions = param_expressions;
            let p = param_expressions.pop().unwrap();
            let p = match p {
                ZirExpression::Uint(e) => e,
                _ => unreachable!(),
            };
            let from = p.metadata.clone().unwrap().bitwidth();
            let p = self.flatten_uint_expression(symbols, statements_flattened, p);
            let bits = self
                .get_bits(p, from as usize, 32, statements_flattened)
                .into_iter()
                .map(|b| FlatUExpression::with_field(b))
                .collect();
            return bits;
        }

        if funct == crate::embed::FlatEmbed::U32FromBits {
            assert_eq!(param_expressions.len(), 32);
            let param_expressions: Vec<_> = param_expressions
                .into_iter()
                .map(|p| {
                    self.flatten_expression(symbols, statements_flattened, p)
                        .get_field_unchecked()
                })
                .collect();

            return vec![FlatUExpression::with_bits(param_expressions)];
        }

        let funct = funct.synthetize();

        let mut replacement_map = HashMap::new();

        // Handle complex parameters and assign values:
        // Rename Parameters, assign them to values in call. Resolve complex expressions with definitions
        let params_flattened = param_expressions
            .into_iter()
            .map(|param_expr| self.flatten_expression(symbols, statements_flattened, param_expr))
            .into_iter()
            .map(|x| x.get_field_unchecked())
            .collect::<Vec<_>>();

        for (concrete_argument, formal_argument) in
            params_flattened.into_iter().zip(funct.arguments)
        {
            let new_var = self.define(concrete_argument, statements_flattened);
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
                FlatStatement::Log(s) => FlatStatement::Log(s),
            })
            .collect();

        statements_flattened.extend(statements);

        match return_statements.pop().unwrap() {
            FlatStatement::Return(list) => list
                .expressions
                .into_iter()
                .map(|x| x.apply_substitution(&replacement_map))
                .map(|x| FlatUExpression::with_field(x))
                .collect(),
            _ => unreachable!(),
        }
    }

    /// Flattens an expression
    ///
    /// # Arguments
    ///
    /// * `symbols` - Available functions in this context
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `expr` - `ZirExpression` that will be flattened.
    fn flatten_expression(
        &mut self,
        symbols: &ZirFunctionSymbols<'ast, T>,
        statements_flattened: &mut FlatStatements<T>,
        expr: ZirExpression<'ast, T>,
    ) -> FlatUExpression<T> {
        match expr {
            ZirExpression::FieldElement(e) => FlatUExpression::with_field(
                self.flatten_field_expression(symbols, statements_flattened, e),
            ),
            ZirExpression::Boolean(e) => FlatUExpression::with_field(
                self.flatten_boolean_expression(symbols, statements_flattened, e),
            ),
            ZirExpression::Uint(e) => {
                self.flatten_uint_expression(symbols, statements_flattened, e)
            }
        }
    }

    /// Flattens a uint expression
    ///
    /// # Arguments
    ///
    /// * `symbols` - Available functions in in this context
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `expr` - `UExpression` that will be flattened.
    fn flatten_uint_expression(
        &mut self,
        symbols: &ZirFunctionSymbols<'ast, T>,
        statements_flattened: &mut FlatStatements<T>,
        expr: UExpression<'ast, T>,
    ) -> FlatUExpression<T> {
        self.depth += 1;

        let target_bitwidth = expr.bitwidth;

        let metadata = expr.metadata.clone().unwrap().clone();

        let actual_bitwidth = metadata.bitwidth() as usize;
        let should_reduce = metadata.should_reduce.unwrap();

        let should_reduce = should_reduce && actual_bitwidth > target_bitwidth;

        let res = match expr.into_inner() {
            UExpressionInner::Value(x) => {
                FlatUExpression::with_field(FlatExpression::Number(T::from(x as u128)))
            } // force to be a field element
            UExpressionInner::Identifier(x) => {
                let field = FlatExpression::Identifier(self.layout.get(&x).unwrap().clone());
                let bits = self.bits_cache.get(&field).map(|bits| {
                    assert_eq!(bits.len(), target_bitwidth);
                    bits.clone()
                });
                FlatUExpression::with_field(field).bits(bits)
            }
            UExpressionInner::Not(box e) => {
                let from = e.metadata.clone().unwrap().bitwidth();

                let e_flattened = self.flatten_uint_expression(symbols, statements_flattened, e);

                let e_bits = self.get_bits(
                    e_flattened,
                    from as usize,
                    target_bitwidth,
                    statements_flattened,
                );

                assert_eq!(e_bits.len(), target_bitwidth);

                let name_not = e_bits.iter().map(|_| self.use_sym()).collect::<Vec<_>>();

                statements_flattened.extend(name_not.iter().zip(e_bits.iter()).map(
                    |(name, bit)| {
                        FlatStatement::Definition(
                            *name,
                            FlatExpression::Sub(
                                box FlatExpression::Number(T::from(1)),
                                box bit.clone(),
                            ),
                        )
                    },
                ));

                FlatUExpression::with_bits(
                    name_not.into_iter().map(|v| v.into()).collect::<Vec<_>>(),
                )
            }
            UExpressionInner::Add(box left, box right) => {
                let left_flattened = self
                    .flatten_uint_expression(symbols, statements_flattened, left)
                    .get_field_unchecked();

                let right_flattened = self
                    .flatten_uint_expression(symbols, statements_flattened, right)
                    .get_field_unchecked();

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

                FlatUExpression::with_field(FlatExpression::Add(box new_left, box new_right))
            }
            UExpressionInner::Sub(box left, box right) => {
                let aux = FlatExpression::Number(
                    T::from(2).pow(right.metadata.clone().unwrap().bitwidth() as usize),
                );

                let left_flattened = self
                    .flatten_uint_expression(symbols, statements_flattened, left)
                    .get_field_unchecked();
                let right_flattened = self
                    .flatten_uint_expression(symbols, statements_flattened, right)
                    .get_field_unchecked();
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

                FlatUExpression::with_field(FlatExpression::Add(
                    box aux,
                    box FlatExpression::Sub(box new_left, box new_right),
                ))
            }
            UExpressionInner::LeftShift(box e, box by) => {
                let from = e.metadata.clone().unwrap().bitwidth();

                let e = self.flatten_uint_expression(symbols, statements_flattened, e);

                let by = match by {
                    FieldElementExpression::Number(n) => {
                        n.to_dec_string().parse::<usize>().unwrap()
                    }
                    _ => unreachable!(),
                };

                let e_bits = self.get_bits(e, from as usize, target_bitwidth, statements_flattened);

                assert_eq!(e_bits.len(), target_bitwidth);

                FlatUExpression::with_bits(
                    e_bits
                        .into_iter()
                        .skip(by)
                        .chain(
                            (0..std::cmp::min(by, target_bitwidth))
                                .map(|_| FlatExpression::Number(T::from(0))),
                        )
                        .collect::<Vec<_>>(),
                )
            }
            UExpressionInner::RightShift(box e, box by) => {
                let from = e.metadata.clone().unwrap().bitwidth();

                let e = self.flatten_uint_expression(symbols, statements_flattened, e);

                let by = match by {
                    FieldElementExpression::Number(n) => {
                        n.to_dec_string().parse::<usize>().unwrap()
                    }
                    _ => unreachable!(),
                };

                let e_bits = self.get_bits(e, from as usize, target_bitwidth, statements_flattened);

                assert_eq!(e_bits.len(), target_bitwidth);

                FlatUExpression::with_bits(
                    (0..std::cmp::min(by, target_bitwidth))
                        .map(|_| FlatExpression::Number(T::from(0)))
                        .chain(
                            e_bits
                                .into_iter()
                                .take(target_bitwidth - std::cmp::min(by, target_bitwidth)),
                        )
                        .collect::<Vec<_>>(),
                )
            }
            UExpressionInner::Mult(box left, box right) => {
                let left_flattened = self
                    .flatten_uint_expression(symbols, statements_flattened, left)
                    .get_field_unchecked();
                let right_flattened = self
                    .flatten_uint_expression(symbols, statements_flattened, right)
                    .get_field_unchecked();
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

                let res = self.use_sym();

                statements_flattened.push(FlatStatement::Definition(
                    res,
                    FlatExpression::Mult(box new_left, box new_right),
                ));

                FlatUExpression::with_field(FlatExpression::Identifier(res))
            }
            UExpressionInner::IfElse(box condition, box consequence, box alternative) => self
                .flatten_if_else_expression(
                    symbols,
                    statements_flattened,
                    condition,
                    consequence,
                    alternative,
                )
                .clone(),
            UExpressionInner::Xor(box left, box right) => {
                let left_from = left.metadata.clone().unwrap().bitwidth();
                let right_from = right.metadata.clone().unwrap().bitwidth();

                let left_flattened =
                    self.flatten_uint_expression(symbols, statements_flattened, left);
                let right_flattened =
                    self.flatten_uint_expression(symbols, statements_flattened, right);

                let left_bits = self.get_bits(
                    left_flattened,
                    left_from as usize,
                    target_bitwidth,
                    statements_flattened,
                );
                let right_bits = self.get_bits(
                    right_flattened,
                    right_from as usize,
                    target_bitwidth,
                    statements_flattened,
                );

                assert_eq!(left_bits.len(), target_bitwidth);
                assert_eq!(right_bits.len(), target_bitwidth);

                let xor: Vec<FlatExpression<T>> = left_bits
                    .into_iter()
                    .zip(right_bits.into_iter())
                    .map(|(x, y)| match (x, y) {
                        (FlatExpression::Number(n), e) | (e, FlatExpression::Number(n)) => {
                            if n == T::from(0) {
                                self.define(e, statements_flattened).into()
                            } else if n == T::from(1) {
                                FlatExpression::Sub(
                                    box FlatExpression::Number(T::from(1)),
                                    box e.clone(),
                                )
                            } else {
                                unreachable!()
                            }
                        }
                        (x, y) => {
                            let name = self.use_sym();

                            statements_flattened.extend(vec![
                                FlatStatement::Directive(FlatDirective::new(
                                    vec![name.clone()],
                                    Solver::Xor,
                                    vec![x.clone(), y.clone()],
                                )),
                                FlatStatement::Condition(
                                    FlatExpression::Add(
                                        box x.clone(),
                                        box FlatExpression::Sub(
                                            box y.clone(),
                                            box name.clone().into(),
                                        ),
                                    ),
                                    FlatExpression::Mult(
                                        box FlatExpression::Add(box x.clone(), box x.clone()),
                                        box y.clone(),
                                    ),
                                ),
                            ]);

                            name.into()
                        }
                    })
                    .collect();

                FlatUExpression::with_bits(
                    xor
                )
            }
            UExpressionInner::And(box left, box right) => {
                let left_from = left.metadata.clone().unwrap().bitwidth();
                let right_from = right.metadata.clone().unwrap().bitwidth();

                let left_flattened =
                    self.flatten_uint_expression(symbols, statements_flattened, left);

                let right_flattened =
                    self.flatten_uint_expression(symbols, statements_flattened, right);

                let left_bits = self.get_bits(
                    left_flattened,
                    left_from as usize,
                    target_bitwidth,
                    statements_flattened,
                );
                let right_bits = self.get_bits(
                    right_flattened,
                    right_from as usize,
                    target_bitwidth,
                    statements_flattened,
                );

                assert_eq!(left_bits.len(), target_bitwidth);
                assert_eq!(right_bits.len(), target_bitwidth);

                let and: Vec<_> = 
                    left_bits.into_iter().zip(right_bits.into_iter())
                        .map(|(x, y)| {
                            match (x, y) {
                                (FlatExpression::Number(n), e) | (e, FlatExpression::Number(n)) => {
                                    if n == T::from(0) {
                                        FlatExpression::Number(T::from(0))
                                    } else if n == T::from(1) {
                                        e
                                    } else {
                                        unreachable!();
                                    }
                                },
                                (x, y) => 
                                    self.define(FlatExpression::Mult(box x.clone(), box y.clone()), statements_flattened).into()
                            }
                        }).collect();

                FlatUExpression::with_bits(
                    and
                )
            }
            UExpressionInner::Or(box left, box right) => {
                let left_from = left.metadata.clone().unwrap().bitwidth();
                let right_from = right.metadata.clone().unwrap().bitwidth();

                let left_flattened =
                    self.flatten_uint_expression(symbols, statements_flattened, left);
                let right_flattened =
                    self.flatten_uint_expression(symbols, statements_flattened, right);

                let left_bits = self.get_bits(
                    left_flattened,
                    left_from as usize,
                    target_bitwidth,
                    statements_flattened,
                );
                let right_bits = self.get_bits(
                    right_flattened,
                    right_from as usize,
                    target_bitwidth,
                    statements_flattened,
                );

                assert_eq!(left_bits.len(), target_bitwidth);
                assert_eq!(right_bits.len(), target_bitwidth);

                let or: Vec<FlatExpression<T>> = 
                    left_bits.into_iter()
                        .zip(right_bits.into_iter())
                        .map(|(x, y)| match (x, y) {
                            (FlatExpression::Number(n), e) | (e, FlatExpression::Number(n)) => {
                                if n == T::from(0) {
                                    self.define(e, statements_flattened).into()
                                } else if n == T::from(1) {
                                    FlatExpression::Number(T::from(1))
                                } else {
                                    unreachable!()
                                }
                            }
                            (x, y) => {

                                let name = self.use_sym();

                                statements_flattened.extend(vec![
                                FlatStatement::Directive(FlatDirective::new(
                                    vec![name.clone()],
                                    Solver::Or,
                                    vec![x.clone(), y.clone()],
                                )),
                                FlatStatement::Condition(
                                    FlatExpression::Add(
                                        box x.clone(),
                                        box FlatExpression::Sub(
                                            box y.clone(),
                                            box name.clone().into(),
                                        ),
                                    ),
                                    FlatExpression::Mult(box x, box y),
                                ),
                            ]);
                                name.into()

                            }
                        }).collect();

                FlatUExpression::with_bits(
                    or
                )
            }
        };

        let res = match should_reduce {
            true => {
                let bits = self.get_bits(
                    res.clone(),
                    actual_bitwidth,
                    target_bitwidth,
                    statements_flattened,
                );

                let field = bits.iter().enumerate().fold(
                    FlatExpression::Number(T::from(0)),
                    |acc, (index, bit)| {
                        FlatExpression::Add(
                            box acc,
                            box FlatExpression::Mult(
                                box FlatExpression::Number(
                                    T::from(2).pow(target_bitwidth - index - 1),
                                ),
                                box bit.clone().into(),
                            ),
                        )
                    },
                );

                // truncate to the target bitwidth
                FlatUExpression::with_bits(bits).field(field)
            }
            false => res,
        };

        self.depth -= 1;

        // statements_flattened.push(FlatStatement::Log(format!(
        //     "  {} DONE",
        //     "   ".repeat(self.depth)
        // )));

        res
    }

    fn get_bits(
        &mut self,
        e: FlatUExpression<T>,
        from: usize,
        to: usize,
        statements_flattened: &mut FlatStatements<T>,
    ) -> Vec<FlatExpression<T>> {
        // constants do not require directives!
        match e.field.clone() {
            Some(FlatExpression::Number(x)) => {
                let bits: Vec<_> = Solver::bits(to)
                    .execute(&vec![x])
                    .unwrap()
                    .into_iter()
                    .map(|x| FlatExpression::Number(x))
                    .collect();

                self.bits_cache
                    .insert(e.field.clone().unwrap(), bits.clone());
                return bits;
            }
            _ => {}
        };

        e.bits
            .clone()
            .unwrap_or_else(|| match self.bits_cache.entry(e.field.clone().unwrap()) {
                Entry::Occupied(entry) => {
                    entry.get().clone().into_iter().map(|e| e.into()).collect()
                }
                Entry::Vacant(_) => {
                    let bits = (0..from).map(|_| self.use_sym()).collect::<Vec<_>>();
                    statements_flattened.push(FlatStatement::Directive(FlatDirective::new(
                        bits.clone(),
                        Solver::Bits(from),
                        vec![e.field.clone().unwrap()],
                    )));

                    // decompose to the actual bitwidth

                    // bit checks
                    statements_flattened.extend((0..from).map(|i| {
                        FlatStatement::Condition(
                            bits[i].clone().into(),
                            FlatExpression::Mult(
                                box bits[i].clone().into(),
                                box bits[i].clone().into(),
                            ),
                        )
                    }));

                    let sum = bits.iter().enumerate().fold(
                        FlatExpression::Number(T::from(0)),
                        |acc, (index, bit)| {
                            FlatExpression::Add(
                                box acc,
                                box FlatExpression::Mult(
                                    box FlatExpression::Number(T::from(2).pow(from - index - 1)),
                                    box bit.clone().into(),
                                ),
                            )
                        },
                    );

                    // sum check
                    statements_flattened.push(FlatStatement::Condition(
                        e.field.clone().unwrap(),
                        sum.clone(),
                    ));

                    let bits = bits[from - to..].to_vec();

                    assert_eq!(bits.len(), to);

                    let bits: Vec<_> = bits
                        .into_iter()
                        .map(|b| FlatExpression::Identifier(b))
                        .collect();

                    self.bits_cache.insert(e.field.unwrap(), bits.clone());
                    self.bits_cache.insert(sum, bits.clone());

                    bits.into_iter().map(|v| v.into()).collect()
                }
            })
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
        symbols: &ZirFunctionSymbols<'ast, T>,
        statements_flattened: &mut FlatStatements<T>,
        expr: FieldElementExpression<'ast, T>,
    ) -> FlatExpression<T> {
        match expr {
            FieldElementExpression::Number(x) => FlatExpression::Number(x), // force to be a field element
            FieldElementExpression::Identifier(x) => {
                FlatExpression::Identifier(self.layout.get(&x).unwrap().clone())
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
                )
                .get_field_unchecked()
                .clone(),
        }
    }

    /// Flattens a statement
    ///
    /// # Arguments
    ///
    /// * `symbols` - Available functions in this context
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `stat` - `ZirStatement` that will be flattened.
    fn flatten_statement(
        &mut self,
        symbols: &ZirFunctionSymbols<'ast, T>,
        statements_flattened: &mut FlatStatements<T>,
        stat: ZirStatement<'ast, T>,
    ) {
        match stat {
            ZirStatement::Return(exprs) => {
                let flat_expressions = exprs
                    .into_iter()
                    .map(|expr| self.flatten_expression(symbols, statements_flattened, expr))
                    .map(|x| x.get_field_unchecked())
                    .collect::<Vec<_>>();

                statements_flattened.push(FlatStatement::Return(FlatExpressionList {
                    expressions: flat_expressions,
                }));
            }
            ZirStatement::Declaration(_) => {
                // declarations have already been checked
                ()
            }
            ZirStatement::Definition(assignee, expr) => {
                // define n variables with n the number of primitive types for v_type
                // assign them to the n primitive types for expr

                let rhs = self.flatten_expression(symbols, statements_flattened, expr);

                let bits = rhs.bits.clone();

                let var = match rhs.get_field_unchecked() {
                    FlatExpression::Identifier(id) => {
                        self.use_variable_with_existing(&assignee, id);
                        id
                    },
                    e => {
                        let var = self.use_variable(&assignee);

                        // handle return of function call
                        statements_flattened
                            .push(FlatStatement::Definition(var, e));

                        var
                    }
                };

                // register bits
                match bits {
                    Some(bits) => {
                        self.bits_cache
                            .insert(FlatExpression::Identifier(var), bits);
                    }
                    None => {}
                }
            }
            ZirStatement::Condition(lhs, rhs) => {
                // flatten expr1 and expr2 to n flattened expressions with n the number of primitive types for expr1
                // add n conditions to check equality of the n expressions

                let lhs = self
                    .flatten_expression(symbols, statements_flattened, lhs)
                    .get_field_unchecked();
                let rhs = self
                    .flatten_expression(symbols, statements_flattened, rhs)
                    .get_field_unchecked();

                //assert_eq!(lhs.len(), rhs.len());

                if lhs.is_linear() {
                    statements_flattened.push(FlatStatement::Condition(lhs, rhs));
                } else if rhs.is_linear() {
                    // swap so that left side is linear
                    statements_flattened.push(FlatStatement::Condition(rhs, lhs));
                } else {
                    unreachable!()
                }
            }
            ZirStatement::MultipleDefinition(vars, rhs) => {
                // flatten the right side to p = sum(var_i.type.primitive_count) expressions
                // define p new variables to the right side expressions

                let var_types = vars.iter().map(|v| v.get_type()).collect();

                match rhs {
                    ZirExpressionList::FunctionCall(key, exprs, _) => {

                        let rhs_flattened = self.flatten_function_call(
                            symbols,
                            statements_flattened,
                            &key.id,
                            var_types,
                            exprs.clone(),
                        );

                        let rhs = rhs_flattened.into_iter();

                        let vars: Vec<_> = vars.into_iter().zip(rhs).map(|(v, r)| {
                            match r.get_field_unchecked() {
                                FlatExpression::Identifier(id) => {
                                    self.use_variable_with_existing(&v, id);
                                    id
                                },
                                e => {
                                    let id = self.use_variable(&v);
                                    statements_flattened.push(
                                        FlatStatement::Definition(id, e)
                                    );
                                    id
                                }
                            }
                        }).collect();

                        if key.id == "_U32_FROM_BITS" {
                            let bits = exprs
                                .into_iter()
                                .map(|e| {
                                    self.flatten_expression(symbols, statements_flattened, e)
                                        .get_field_unchecked()
                                })
                                .collect();
                            self.bits_cache.insert(vars[0].clone().into(), bits);
                        }
                    }
                }
            }
        }
    }

    /// Flattens a function
    ///
    /// # Arguments
    /// * `symbols` - Available functions in in this context
    /// * `funct` - `ZirFunction` that will be flattened
    fn flatten_function(
        &mut self,
        symbols: &ZirFunctionSymbols<'ast, T>,
        funct: ZirFunction<'ast, T>,
    ) -> FlatFunction<T> {
        self.layout = HashMap::new();

        self.next_var_idx = 0;
        let mut statements_flattened: FlatStatements<T> = FlatStatements::new();

        // push parameters
        let arguments_flattened = funct
            .arguments
            .into_iter()
            .map(|p| self.use_parameter(&p, &mut statements_flattened))
            .collect();

        // flatten statements in functions and apply substitution
        for stat in funct.statements {
            self.flatten_statement(symbols, &mut statements_flattened, stat);
        }

        FlatFunction {
            arguments: arguments_flattened,
            statements: statements_flattened.0,
        }
    }

    /// Flattens a program
    ///
    /// # Arguments
    ///
    /// * `prog` - `ZirProgram` that will be flattened.
    fn flatten_program(&mut self, prog: ZirProgram<'ast, T>) -> FlatProg<T> {
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
            ZirFunctionSymbol::Here(f) => self.flatten_function(&symbols, f),
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
    fn use_variable(&mut self, variable: &Variable<'ast>) -> FlatVariable {
        let var = self.issue_new_variable();

        self.layout.insert(variable.id.clone(), var.clone());
        var
    }

    fn use_variable_with_existing(&mut self, variable: &Variable<'ast>, flat_variable: FlatVariable) {
        self.layout.insert(variable.id.clone(), flat_variable);
    }

    fn use_parameter(
        &mut self,
        parameter: &Parameter<'ast>,
        statements_flattened: &mut FlatStatements<T>,
    ) -> FlatParameter {
        let variable = self.use_variable(&parameter.id);

        match parameter.id.get_type() {
            Type::Uint(bitwidth) => {
                self.get_bits(
                    FlatUExpression::with_field(FlatExpression::Identifier(variable)),
                    bitwidth,
                    bitwidth,
                    statements_flattened,
                );
            }
            _ => {}
        }

        FlatParameter {
            id: variable,
            private: parameter.private,
        }
    }

    fn issue_new_variable(&mut self) -> FlatVariable {
        let var = FlatVariable::new(self.next_var_idx);
        self.next_var_idx += 1;
        var
    }

    // create an internal variable. We do not register it in the layout
    fn use_sym(&mut self) -> FlatVariable {
        self.issue_new_variable()
    }

    fn get_embed<'a>(
        &mut self,
        key: &'a FunctionKey<'ast>,
        symbols: &'a ZirFunctionSymbols<'ast, T>,
    ) -> crate::embed::FlatEmbed {
        let f = symbols.get(&key).expect(&format!("{}", key.id)).clone();
        let res = match f {
            ZirFunctionSymbol::Flat(flat_function) => flat_function,
            _ => unreachable!("only local flat symbols can be flattened"),
        };
        res
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::zir::types::Signature;
    use crate::zir::types::Type;
    use zokrates_field::Bn128Field;

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
        let function = ZirFunction {
            arguments: vec![],
            statements: vec![
                ZirStatement::Definition(
                    Variable::field_element("a"),
                    FieldElementExpression::Number(Bn128Field::from(7)).into(),
                ),
                ZirStatement::Definition(
                    Variable::field_element("b"),
                    FieldElementExpression::Pow(
                        box FieldElementExpression::Identifier("a".into()),
                        box FieldElementExpression::Number(Bn128Field::from(0)),
                    )
                    .into(),
                ),
                ZirStatement::Return(vec![FieldElementExpression::Identifier("b".into()).into()]),
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
                    FlatExpression::Number(Bn128Field::from(7)),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(1),
                    FlatExpression::Number(Bn128Field::from(1)),
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
        let function = ZirFunction {
            arguments: vec![],
            statements: vec![
                ZirStatement::Definition(
                    Variable::field_element("a"),
                    FieldElementExpression::Number(Bn128Field::from(7)).into(),
                ),
                ZirStatement::Definition(
                    Variable::field_element("b"),
                    FieldElementExpression::Pow(
                        box FieldElementExpression::Identifier("a".into()),
                        box FieldElementExpression::Number(Bn128Field::from(1)),
                    )
                    .into(),
                ),
                ZirStatement::Return(vec![FieldElementExpression::Identifier("b".into()).into()]),
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
                    FlatExpression::Number(Bn128Field::from(7)),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(1),
                    FlatExpression::Mult(
                        box FlatExpression::Number(Bn128Field::from(1)),
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

        let function = ZirFunction {
            arguments: vec![],
            statements: vec![
                ZirStatement::Definition(
                    Variable::field_element("a"),
                    FieldElementExpression::Number(Bn128Field::from(7)).into(),
                ),
                ZirStatement::Definition(
                    Variable::field_element("b"),
                    FieldElementExpression::Pow(
                        box FieldElementExpression::Identifier("a".into()),
                        box FieldElementExpression::Number(Bn128Field::from(13)),
                    )
                    .into(),
                ),
                ZirStatement::Return(vec![FieldElementExpression::Identifier("b".into()).into()]),
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
                    FlatExpression::Number(Bn128Field::from(7)),
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
                        box FlatExpression::Number(Bn128Field::from(1)),
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
                box FieldElementExpression::Number(Bn128Field::from(32)),
                box FieldElementExpression::Number(Bn128Field::from(4)),
            ),
            box FieldElementExpression::Number(Bn128Field::from(12)),
            box FieldElementExpression::Number(Bn128Field::from(51)),
        );

        let mut flattener = Flattener::new();

        flattener.flatten_field_expression(&HashMap::new(), &mut vec![], expression);
    }

    #[test]
    fn geq_leq() {
        let mut flattener = Flattener::new();
        let expression_le = BooleanExpression::Le(
            box FieldElementExpression::Number(Bn128Field::from(32)),
            box FieldElementExpression::Number(Bn128Field::from(4)),
        );
        flattener.flatten_boolean_expression(&HashMap::new(), &mut vec![], expression_le);

        let mut flattener = Flattener::new();
        let expression_ge = BooleanExpression::Ge(
            box FieldElementExpression::Number(Bn128Field::from(32)),
            box FieldElementExpression::Number(Bn128Field::from(4)),
        );
        flattener.flatten_boolean_expression(&HashMap::new(), &mut vec![], expression_ge);
    }

    #[test]
    fn bool_and() {
        let mut flattener = Flattener::new();

        let expression = FieldElementExpression::IfElse(
            box BooleanExpression::And(
                box BooleanExpression::FieldEq(
                    box FieldElementExpression::Number(Bn128Field::from(4)),
                    box FieldElementExpression::Number(Bn128Field::from(4)),
                ),
                box BooleanExpression::Lt(
                    box FieldElementExpression::Number(Bn128Field::from(4)),
                    box FieldElementExpression::Number(Bn128Field::from(20)),
                ),
            ),
            box FieldElementExpression::Number(Bn128Field::from(12)),
            box FieldElementExpression::Number(Bn128Field::from(51)),
        );

        flattener.flatten_field_expression(&HashMap::new(), &mut vec![], expression);
    }

    #[test]
    fn div() {
        // a = 5 / b / b

        let mut flattener = Flattener::new();
        let mut statements_flattened = vec![];

        let definition = ZirStatement::Definition(
            Variable::field_element("b"),
            FieldElementExpression::Number(Bn128Field::from(42)).into(),
        );

        let statement = ZirStatement::Definition(
            Variable::field_element("a"),
            FieldElementExpression::Div(
                box FieldElementExpression::Div(
                    box FieldElementExpression::Number(Bn128Field::from(5)),
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
                FlatStatement::Definition(b, FlatExpression::Number(Bn128Field::from(42))),
                // inputs to first div (5/b)
                FlatStatement::Definition(five, FlatExpression::Number(Bn128Field::from(5))),
                FlatStatement::Definition(b0, b.into()),
                // check div by 0
                FlatStatement::Directive(FlatDirective::new(
                    vec![invb0],
                    Solver::Div,
                    vec![FlatExpression::Number(Bn128Field::from(1)), b0.into()]
                )),
                FlatStatement::Condition(
                    FlatExpression::Number(Bn128Field::from(1)),
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
                    vec![FlatExpression::Number(Bn128Field::from(1)), b1.into()]
                )),
                FlatStatement::Condition(
                    FlatExpression::Number(Bn128Field::from(1)),
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

    // #[test]
    // fn field_array() {
    //     // foo = [ , , ]

    //     let mut flattener = Flattener::new();
    //     let mut statements_flattened = vec![];
    //     let statement = ZirStatement::Definition(
    //         ZirAssignee::Identifier(Variable::field_array("foo", 3)),
    //         ArrayExpressionInner::Value(vec![
    //             FieldElementExpression::Number(Bn128Field::from(1)).into(),
    //             FieldElementExpression::Number(Bn128Field::from(2)).into(),
    //             FieldElementExpression::Number(Bn128Field::from(3)).into(),
    //         ])
    //         .annotate(Type::FieldElement, 3)
    //         .into(),
    //     );
    //     let expression =
    //         ArrayExpressionInner::Identifier("foo".into()).annotate(Type::FieldElement, 3);

    //     flattener.flatten_statement(&HashMap::new(), &mut statements_flattened, statement);

    //     let expressions = flattener.flatten_array_expression::<FieldElementExpression<_>>(
    //         &HashMap::new(),
    //         &mut statements_flattened,
    //         expression,
    //     );

    //     assert_eq!(
    //         expressions,
    //         vec![
    //             FlatExpression::Identifier(FlatVariable::new(0)),
    //             FlatExpression::Identifier(FlatVariable::new(1)),
    //             FlatExpression::Identifier(FlatVariable::new(2)),
    //         ]
    //     );
    // }

    // #[test]
    // fn array_definition() {
    //     // field[3] foo = [1, 2, 3]
    //     let mut flattener = Flattener::new();
    //     let mut statements_flattened = vec![];
    //     let statement = ZirStatement::Definition(
    //         ZirAssignee::Identifier(Variable::field_array("foo", 3)),
    //         ArrayExpressionInner::Value(vec![
    //             FieldElementExpression::Number(Bn128Field::from(1)).into(),
    //             FieldElementExpression::Number(Bn128Field::from(2)).into(),
    //             FieldElementExpression::Number(Bn128Field::from(3)).into(),
    //         ])
    //         .annotate(Type::FieldElement, 3)
    //         .into(),
    //     );

    //     flattener.flatten_statement(&HashMap::new(), &mut statements_flattened, statement);

    //     assert_eq!(
    //         statements_flattened,
    //         vec![
    //             FlatStatement::Definition(
    //                 FlatVariable::new(0),
    //                 FlatExpression::Number(Bn128Field::from(1))
    //             ),
    //             FlatStatement::Definition(
    //                 FlatVariable::new(1),
    //                 FlatExpression::Number(Bn128Field::from(2))
    //             ),
    //             FlatStatement::Definition(
    //                 FlatVariable::new(2),
    //                 FlatExpression::Number(Bn128Field::from(3))
    //             ),
    //         ]
    //     );
    // }

    // #[test]
    // fn array_selection() {
    //     // field[3] foo = [1, 2, 3]
    //     // foo[1]

    //     let mut flattener = Flattener::new();
    //     let mut statements_flattened = vec![];
    //     let statement = ZirStatement::Definition(
    //         ZirAssignee::Identifier(Variable::field_array("foo", 3)),
    //         ArrayExpressionInner::Value(vec![
    //             FieldElementExpression::Number(Bn128Field::from(1)).into(),
    //             FieldElementExpression::Number(Bn128Field::from(2)).into(),
    //             FieldElementExpression::Number(Bn128Field::from(3)).into(),
    //         ])
    //         .annotate(Type::FieldElement, 3)
    //         .into(),
    //     );

    //     let expression = FieldElementExpression::Select(
    //         box ArrayExpressionInner::Identifier("foo".into()).annotate(Type::FieldElement, 3),
    //         box FieldElementExpression::Number(Bn128Field::from(1)),
    //     );

    //     flattener.flatten_statement(&HashMap::new(), &mut statements_flattened, statement);

    //     let flat_expression = flattener.flatten_field_expression(
    //         &HashMap::new(),
    //         &mut statements_flattened,
    //         expression,
    //     );

    //     assert_eq!(
    //         flat_expression,
    //         FlatExpression::Identifier(FlatVariable::new(1)),
    //     );
    // }

    // #[test]
    // fn array_sum() {
    //     // field[3] foo = [1, 2, 3]
    //     // bar = foo[0] + foo[1] + foo[2]
    //     // we don't optimise detecting constants, this will be done in an optimiser pass

    //     let mut flattener = Flattener::new();

    //     let mut statements_flattened = vec![];
    //     let def = ZirStatement::Definition(
    //         ZirAssignee::Identifier(Variable::field_array("foo", 3)),
    //         ArrayExpressionInner::Value(vec![
    //             FieldElementExpression::Number(Bn128Field::from(1)).into(),
    //             FieldElementExpression::Number(Bn128Field::from(2)).into(),
    //             FieldElementExpression::Number(Bn128Field::from(3)).into(),
    //         ])
    //         .annotate(Type::FieldElement, 3)
    //         .into(),
    //     );

    //     let sum = ZirStatement::Definition(
    //         ZirAssignee::Identifier(Variable::field_element("bar")),
    //         FieldElementExpression::Add(
    //             box FieldElementExpression::Add(
    //                 box FieldElementExpression::Select(
    //                     box ArrayExpressionInner::Identifier("foo".into())
    //                         .annotate(Type::FieldElement, 3),
    //                     box FieldElementExpression::Number(Bn128Field::from(0)),
    //                 ),
    //                 box FieldElementExpression::Select(
    //                     box ArrayExpressionInner::Identifier("foo".into())
    //                         .annotate(Type::FieldElement, 3),
    //                     box FieldElementExpression::Number(Bn128Field::from(1)),
    //                 ),
    //             ),
    //             box FieldElementExpression::Select(
    //                 box ArrayExpressionInner::Identifier("foo".into())
    //                     .annotate(Type::FieldElement, 3),
    //                 box FieldElementExpression::Number(Bn128Field::from(2)),
    //             ),
    //         )
    //         .into(),
    //     );

    //     flattener.flatten_statement(&HashMap::new(), &mut statements_flattened, def);

    //     flattener.flatten_statement(&HashMap::new(), &mut statements_flattened, sum);

    //     assert_eq!(
    //         statements_flattened[3],
    //         FlatStatement::Definition(
    //             FlatVariable::new(3),
    //             FlatExpression::Add(
    //                 box FlatExpression::Add(
    //                     box FlatExpression::Identifier(FlatVariable::new(0)),
    //                     box FlatExpression::Identifier(FlatVariable::new(1)),
    //                 ),
    //                 box FlatExpression::Identifier(FlatVariable::new(2)),
    //             )
    //         )
    //     );
    // }

    // #[test]
    // fn array_of_array_sum() {
    //     // field[2][2] foo = [[1, 2], [3, 4]]
    //     // bar = foo[0][0] + foo[0][1] + foo[1][0] + foo[1][1]
    //     // we don't optimise detecting constants, this will be done in an optimiser pass

    //     let mut flattener = Flattener::new();

    //     let mut statements_flattened = vec![];
    //     let def = ZirStatement::Definition(
    //         ZirAssignee::Identifier(Variable::field_array("foo", 4)),
    //         ArrayExpressionInner::Value(vec![
    //             ArrayExpressionInner::Value(vec![
    //                 FieldElementExpression::Number(Bn128Field::from(1)).into(),
    //                 FieldElementExpression::Number(Bn128Field::from(2)).into(),
    //             ])
    //             .annotate(Type::FieldElement, 2)
    //             .into(),
    //             ArrayExpressionInner::Value(vec![
    //                 FieldElementExpression::Number(Bn128Field::from(3)).into(),
    //                 FieldElementExpression::Number(Bn128Field::from(4)).into(),
    //             ])
    //             .annotate(Type::FieldElement, 2)
    //             .into(),
    //         ])
    //         .annotate(Type::array(Type::FieldElement, 2), 2)
    //         .into(),
    //     );

    //     let sum = ZirStatement::Definition(
    //         ZirAssignee::Identifier(Variable::field_element("bar")),
    //         FieldElementExpression::Add(
    //             box FieldElementExpression::Add(
    //                 box FieldElementExpression::Add(
    //                     box FieldElementExpression::Select(
    //                         box ArrayExpressionInner::Select(
    //                             box ArrayExpressionInner::Identifier("foo".into())
    //                                 .annotate(Type::array(Type::FieldElement, 2), 2),
    //                             box FieldElementExpression::Number(Bn128Field::from(0)),
    //                         )
    //                         .annotate(Type::FieldElement, 2),
    //                         box FieldElementExpression::Number(Bn128Field::from(0)),
    //                     ),
    //                     box FieldElementExpression::Select(
    //                         box ArrayExpressionInner::Select(
    //                             box ArrayExpressionInner::Identifier("foo".into())
    //                                 .annotate(Type::array(Type::FieldElement, 2), 2),
    //                             box FieldElementExpression::Number(Bn128Field::from(0)),
    //                         )
    //                         .annotate(Type::FieldElement, 2),
    //                         box FieldElementExpression::Number(Bn128Field::from(1)),
    //                     ),
    //                 ),
    //                 box FieldElementExpression::Select(
    //                     box ArrayExpressionInner::Select(
    //                         box ArrayExpressionInner::Identifier("foo".into())
    //                             .annotate(Type::array(Type::FieldElement, 2), 2),
    //                         box FieldElementExpression::Number(Bn128Field::from(1)),
    //                     )
    //                     .annotate(Type::FieldElement, 2),
    //                     box FieldElementExpression::Number(Bn128Field::from(0)),
    //                 ),
    //             ),
    //             box FieldElementExpression::Select(
    //                 box ArrayExpressionInner::Select(
    //                     box ArrayExpressionInner::Identifier("foo".into())
    //                         .annotate(Type::array(Type::FieldElement, 2), 2),
    //                     box FieldElementExpression::Number(Bn128Field::from(1)),
    //                 )
    //                 .annotate(Type::FieldElement, 2),
    //                 box FieldElementExpression::Number(Bn128Field::from(1)),
    //             ),
    //         )
    //         .into(),
    //     );

    //     flattener.flatten_statement(&HashMap::new(), &mut statements_flattened, def);

    //     flattener.flatten_statement(&HashMap::new(), &mut statements_flattened, sum);

    //     assert_eq!(
    //         statements_flattened[4],
    //         FlatStatement::Definition(
    //             FlatVariable::new(4),
    //             FlatExpression::Add(
    //                 box FlatExpression::Add(
    //                     box FlatExpression::Add(
    //                         box FlatExpression::Identifier(FlatVariable::new(0)),
    //                         box FlatExpression::Identifier(FlatVariable::new(1)),
    //                     ),
    //                     box FlatExpression::Identifier(FlatVariable::new(2))
    //                 ),
    //                 box FlatExpression::Identifier(FlatVariable::new(3)),
    //             )
    //         )
    //     );
    // }

    // #[test]
    // fn array_if() {
    //     // if 1 == 1 then [1] else [3] fi
    //     let with_arrays = {
    //         let mut flattener = Flattener::new();
    //         let mut statements_flattened = vec![];

    //         let e = ArrayExpressionInner::IfElse(
    //             box BooleanExpression::FieldEq(
    //                 box FieldElementExpression::Number(Bn128Field::from(1)),
    //                 box FieldElementExpression::Number(Bn128Field::from(1)),
    //             ),
    //             box ArrayExpressionInner::Value(vec![FieldElementExpression::Number(
    //                 Bn128Field::from(1),
    //             )
    //             .into()])
    //             .annotate(Type::FieldElement, 1),
    //             box ArrayExpressionInner::Value(vec![FieldElementExpression::Number(
    //                 Bn128Field::from(3),
    //             )
    //             .into()])
    //             .annotate(Type::FieldElement, 2),
    //         )
    //         .annotate(Type::FieldElement, 1);

    //         (
    //             flattener.flatten_array_expression::<FieldElementExpression<_>>(
    //                 &HashMap::new(),
    //                 &mut statements_flattened,
    //                 e,
    //             )[0]
    //             .clone(),
    //             statements_flattened,
    //         )
    //     };

    //     let without_arrays = {
    //         let mut statements_flattened = vec![];
    //         let mut flattener = Flattener::new();
    //         // if 1 == 1 then 1 else 3 fi
    //         let e = FieldElementExpression::IfElse(
    //             box BooleanExpression::FieldEq(
    //                 box FieldElementExpression::Number(Bn128Field::from(1)),
    //                 box FieldElementExpression::Number(Bn128Field::from(1)),
    //             ),
    //             box FieldElementExpression::Number(Bn128Field::from(1)),
    //             box FieldElementExpression::Number(Bn128Field::from(3)),
    //         );

    //         (
    //             flattener.flatten_field_expression(&HashMap::new(), &mut statements_flattened, e),
    //             statements_flattened,
    //         )
    //     };

    //     assert_eq!(with_arrays, without_arrays);
    // }

    #[test]
    fn next_variable() {
        let mut flattener: Flattener<Bn128Field> = Flattener::new();
        assert_eq!(
            FlatVariable::new(0),
            flattener.use_variable(&Variable::field_element("a"))
        );
        assert_eq!(
            flattener.layout.get(&"a".into()),
            Some(&FlatVariable::new(0))
        );
        assert_eq!(
            FlatVariable::new(1),
            flattener.use_variable(&Variable::field_element("a"))
        );
        assert_eq!(
            flattener.layout.get(&"a".into()),
            Some(&FlatVariable::new(1))
        );
        assert_eq!(
            FlatVariable::new(2),
            flattener.use_variable(&Variable::field_element("a"))
        );
        assert_eq!(
            flattener.layout.get(&"a".into()),
            Some(&FlatVariable::new(2))
        );
    }
}
