#![allow(clippy::needless_collect)]

//! Module containing the `Flattener` to process a program that is R1CS-able.
//!
//! @file flatten.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

mod utils;

use self::utils::flat_expression_from_bits;
use crate::ir::Interpreter;

use crate::compile::CompileConfig;
use crate::embed::FlatEmbed;
use crate::flat_absy::*;
use crate::solvers::Solver;
use crate::zir::types::{Type, UBitwidth};
use crate::zir::*;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::convert::TryFrom;
use zokrates_field::Field;

type FlatStatements<T> = Vec<FlatStatement<T>>;

/// Flattener, computes flattened program.
#[derive(Debug)]
pub struct Flattener<'ast, T: Field> {
    config: &'ast CompileConfig,
    /// Index of the next introduced variable while processing the program.
    next_var_idx: usize,
    /// `FlatVariable`s corresponding to each `Identifier`
    layout: HashMap<Identifier<'ast>, FlatVariable>,
    /// Cached bit decompositions to avoid re-generating them
    bits_cache: HashMap<FlatExpression<T>, Vec<FlatExpression<T>>>,
}

trait FlattenOutput<T: Field>: Sized {
    fn flat(&self) -> FlatExpression<T>;
}

impl<T: Field> FlattenOutput<T> for FlatExpression<T> {
    fn flat(&self) -> FlatExpression<T> {
        self.clone()
    }
}

impl<T: Field> FlattenOutput<T> for FlatUExpression<T> {
    fn flat(&self) -> FlatExpression<T> {
        self.clone().get_field_unchecked()
    }
}

// We introduce a trait in order to make it possible to make flattening `e` generic over the type of `e`

trait Flatten<'ast, T: Field>: TryFrom<ZirExpression<'ast, T>, Error = ()> + IfElse<'ast, T> {
    type Output: FlattenOutput<T>;

    fn flatten(
        self,
        flattener: &mut Flattener<'ast, T>,
        statements_flattened: &mut FlatStatements<T>,
    ) -> Self::Output;
}

impl<'ast, T: Field> Flatten<'ast, T> for FieldElementExpression<'ast, T> {
    type Output = FlatExpression<T>;

    fn flatten(
        self,
        flattener: &mut Flattener<'ast, T>,
        statements_flattened: &mut FlatStatements<T>,
    ) -> Self::Output {
        flattener.flatten_field_expression(statements_flattened, self)
    }
}

impl<'ast, T: Field> Flatten<'ast, T> for UExpression<'ast, T> {
    type Output = FlatUExpression<T>;

    fn flatten(
        self,
        flattener: &mut Flattener<'ast, T>,
        statements_flattened: &mut FlatStatements<T>,
    ) -> Self::Output {
        flattener.flatten_uint_expression(statements_flattened, self)
    }
}

impl<'ast, T: Field> Flatten<'ast, T> for BooleanExpression<'ast, T> {
    type Output = FlatExpression<T>;

    fn flatten(
        self,
        flattener: &mut Flattener<'ast, T>,
        statements_flattened: &mut FlatStatements<T>,
    ) -> Self::Output {
        flattener.flatten_boolean_expression(statements_flattened, self)
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
                Some(bits) => flat_expression_from_bits(bits),
                None => unreachable!(),
            },
        }
    }
}

impl<'ast, T: Field> Flattener<'ast, T> {
    pub fn flatten(p: ZirProgram<'ast, T>, config: &CompileConfig) -> FlatProg<T> {
        Flattener::new(config).flatten_program(p)
    }

    /// Returns a `Flattener` with fresh `layout`.

    fn new(config: &'ast CompileConfig) -> Flattener<'ast, T> {
        Flattener {
            config,
            next_var_idx: 0,
            layout: HashMap::new(),
            bits_cache: HashMap::new(),
        }
    }

    /// Flattens a definition, trying to avoid creating redundant variables
    fn define(
        &mut self,
        e: FlatExpression<T>,
        statements_flattened: &mut FlatStatements<T>,
    ) -> FlatVariable {
        match e {
            FlatExpression::Identifier(id) => id,
            e => {
                let res = self.use_sym();
                statements_flattened.push(FlatStatement::Definition(res, e));
                res
            }
        }
    }

    // Let's assume b = [1, 1, 1, 0]
    //
    // 1. Init `sizeUnknown = true`
    //    As long as `sizeUnknown` is `true` we don't yet know if a is <= than b.
    // 2. Loop over `b`:
    //     * b[0] = 1
    //       when `b` is 1 we check wether `a` is 0 in that particular run and update
    //       `sizeUnknown` accordingly:
    //       `sizeUnknown = sizeUnknown && a[0]`
    //     * b[1] = 1
    //       `sizrUnknown = sizeUnknown && a[1]`
    //     * b[2] = 1
    //       `sizeUnknown = sizeUnknown && a[2]`
    //     * b[3] = 0
    //       we need to enforce that `a` is 0 in case `sizeUnknown`is still `true`,
    //       otherwise `a` can be {0,1}:
    //      `true == (!sizeUnknown || !a[3])`
    //      ```
    //                     **true => a -> 0
    //         sizeUnkown *
    //                     **false => a -> {0,1}
    //      ```
    fn strict_le_check(
        &mut self,
        statements_flattened: &mut FlatStatements<T>,
        b: &[bool],
        a: Vec<FlatVariable>,
    ) {
        let len = b.len();
        assert_eq!(a.len(), T::get_required_bits());
        assert_eq!(a.len(), b.len());

        let mut is_not_smaller_run = vec![];
        let mut size_unknown = vec![];

        for _ in 0..len {
            is_not_smaller_run.push(self.use_sym());
            size_unknown.push(self.use_sym());
        }

        // init size_unknown = true
        statements_flattened.push(FlatStatement::Definition(
            size_unknown[0],
            FlatExpression::Number(T::from(1)),
        ));

        for (i, b) in b.iter().enumerate() {
            if *b {
                statements_flattened.push(FlatStatement::Definition(
                    is_not_smaller_run[i],
                    a[i].clone().into(),
                ));

                // don't need to update size_unknown in the last round
                if i < len - 1 {
                    statements_flattened.push(FlatStatement::Definition(
                        size_unknown[i + 1],
                        FlatExpression::Mult(
                            box size_unknown[i].into(),
                            box is_not_smaller_run[i].into(),
                        ),
                    ));
                }
            } else {
                // don't need to update size_unknown in the last round
                if i < len - 1 {
                    statements_flattened.push(
                        // sizeUnknown is not changing in this case
                        // We sill have to assign the old value to the variable of the current run
                        // This trivial definition will later be removed by the optimiser
                        FlatStatement::Definition(size_unknown[i + 1], size_unknown[i].into()),
                    );
                }

                let or_left = FlatExpression::Sub(
                    box FlatExpression::Number(T::from(1)),
                    box size_unknown[i].clone().into(),
                );
                let or_right: FlatExpression<_> = FlatExpression::Sub(
                    box FlatExpression::Number(T::from(1)),
                    box a[i].clone().into(),
                );

                let and_name = self.use_sym();
                let and = FlatExpression::Mult(box or_left.clone(), box or_right.clone());
                statements_flattened.push(FlatStatement::Definition(and_name, and));
                let or = FlatExpression::Sub(
                    box FlatExpression::Add(box or_left, box or_right),
                    box and_name.into(),
                );

                statements_flattened.push(FlatStatement::Condition(
                    FlatExpression::Number(T::from(1)),
                    or,
                ));
            }
        }
    }

    /// Flatten an if/else expression
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `condition` - the condition as a `BooleanExpression`.
    /// * `consequence` - the consequence of type U.
    /// * `alternative` - the alternative of type U.
    /// # Remarks
    /// * U is the type of the expression
    fn flatten_if_else_expression<U: Flatten<'ast, T>>(
        &mut self,
        statements_flattened: &mut FlatStatements<T>,
        condition: BooleanExpression<'ast, T>,
        consequence: U,
        alternative: U,
    ) -> FlatUExpression<T> {
        let condition = self.flatten_boolean_expression(statements_flattened, condition);

        let consequence = consequence.flatten(self, statements_flattened);

        let alternative = alternative.flatten(self, statements_flattened);

        let condition_id = self.use_sym();
        statements_flattened.push(FlatStatement::Definition(condition_id, condition));

        let consequence = consequence.flat();
        let alternative = alternative.flat();

        let consequence_id = self.use_sym();
        statements_flattened.push(FlatStatement::Definition(consequence_id, consequence));

        let alternative_id = self.use_sym();
        statements_flattened.push(FlatStatement::Definition(alternative_id, alternative));

        let term0_id = self.use_sym();
        statements_flattened.push(FlatStatement::Definition(
            term0_id,
            FlatExpression::Mult(
                box condition_id.clone().into(),
                box FlatExpression::from(consequence_id),
            ),
        ));

        let term1_id = self.use_sym();
        statements_flattened.push(FlatStatement::Definition(
            term1_id,
            FlatExpression::Mult(
                box FlatExpression::Sub(
                    box FlatExpression::Number(T::one()),
                    box condition_id.into(),
                ),
                box FlatExpression::from(alternative_id),
            ),
        ));

        let res = self.use_sym();
        statements_flattened.push(FlatStatement::Definition(
            res,
            FlatExpression::Add(
                box FlatExpression::from(term0_id),
                box FlatExpression::from(term1_id),
            ),
        ));

        FlatUExpression {
            field: Some(FlatExpression::Identifier(res)),
            bits: None,
        }
    }

    /// Flattens a boolean expression
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `expression` - `BooleanExpression` that will be flattened.
    ///
    /// # Postconditions
    ///
    /// * `flatten_boolean_expressions` always returns a linear expression,
    /// * in order to preserve composability.
    fn flatten_boolean_expression(
        &mut self,
        statements_flattened: &mut FlatStatements<T>,
        expression: BooleanExpression<'ast, T>,
    ) -> FlatExpression<T> {
        // those will be booleans in the future
        match expression {
            BooleanExpression::Identifier(x) => {
                FlatExpression::Identifier(*self.layout.get(&x).unwrap())
            }
            BooleanExpression::FieldLt(box lhs, box rhs) => {
                // Get the bit width to know the size of the binary decompositions for this Field
                let bit_width = T::get_required_bits();
                let safe_width = bit_width - 2; // making sure we don't overflow, assert here?

                // We know from semantic checking that lhs and rhs have the same type
                // What the expression will flatten to depends on that type

                let lhs_flattened = self.flatten_field_expression(statements_flattened, lhs);
                let rhs_flattened = self.flatten_field_expression(statements_flattened, rhs);

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
                    for bit in lhs_bits_be.iter().take(safe_width) {
                        statements_flattened.push(FlatStatement::Condition(
                            FlatExpression::Identifier(*bit),
                            FlatExpression::Mult(
                                box FlatExpression::Identifier(*bit),
                                box FlatExpression::Identifier(*bit),
                            ),
                        ));
                    }

                    // bit decomposition check
                    let mut lhs_sum = FlatExpression::Number(T::from(0));

                    for (i, bit) in lhs_bits_be.iter().enumerate().take(safe_width) {
                        lhs_sum = FlatExpression::Add(
                            box lhs_sum,
                            box FlatExpression::Mult(
                                box FlatExpression::Identifier(*bit),
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
                    for bit in rhs_bits_be.iter().take(safe_width) {
                        statements_flattened.push(FlatStatement::Condition(
                            FlatExpression::Identifier(*bit),
                            FlatExpression::Mult(
                                box FlatExpression::Identifier(*bit),
                                box FlatExpression::Identifier(*bit),
                            ),
                        ));
                    }

                    // bit decomposition check
                    let mut rhs_sum = FlatExpression::Number(T::from(0));

                    for (i, bit) in rhs_bits_be.iter().enumerate().take(safe_width) {
                        rhs_sum = FlatExpression::Add(
                            box rhs_sum,
                            box FlatExpression::Mult(
                                box FlatExpression::Identifier(*bit),
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
                for bit in sub_bits_be.iter().take(bit_width) {
                    statements_flattened.push(FlatStatement::Condition(
                        FlatExpression::Identifier(*bit),
                        FlatExpression::Mult(
                            box FlatExpression::Identifier(*bit),
                            box FlatExpression::Identifier(*bit),
                        ),
                    ));
                }

                // check that the decomposition is in the field with a strict `< p` checks
                self.strict_le_check(
                    statements_flattened,
                    &T::max_value_bit_vector_be(),
                    sub_bits_be.clone(),
                );

                // sum(sym_b{i} * 2**i)
                let mut expr = FlatExpression::Number(T::from(0));

                for (i, bit) in sub_bits_be.iter().enumerate().take(bit_width) {
                    expr = FlatExpression::Add(
                        box expr,
                        box FlatExpression::Mult(
                            box FlatExpression::Identifier(*bit),
                            box FlatExpression::Number(T::from(2).pow(bit_width - i - 1)),
                        ),
                    );
                }

                statements_flattened.push(FlatStatement::Condition(subtraction_result, expr));

                FlatExpression::Identifier(sub_bits_be[bit_width - 1])
            }
            BooleanExpression::BoolEq(box lhs, box rhs) => {
                // lhs and rhs are booleans, they flatten to 0 or 1
                let x = self.flatten_boolean_expression(statements_flattened, lhs);
                let y = self.flatten_boolean_expression(statements_flattened, rhs);
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
                // Wanted: (Y = (X != 0) ? 1 : 0)
                // X = a - b
                // # Y = if X == 0 then 0 else 1 fi
                // # M = if X == 0 then 1 else 1/X fi
                // Y == X * M
                // 0 == (1-Y) * X

                let name_y = self.use_sym();
                let name_m = self.use_sym();

                let x = self.flatten_field_expression(
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
            BooleanExpression::UintEq(box lhs, box rhs) => {
                // We reduce each side into range and apply the same approach as for field elements

                // Wanted: (Y = (X != 0) ? 1 : 0)
                // X = a - b
                // # Y = if X == 0 then 0 else 1 fi
                // # M = if X == 0 then 1 else 1/X fi
                // Y == X * M
                // 0 == (1-Y) * X

                let name_y = self.use_sym();
                let name_m = self.use_sym();

                assert!(lhs.metadata.clone().unwrap().should_reduce.to_bool());
                assert!(rhs.metadata.clone().unwrap().should_reduce.to_bool());

                let lhs = self
                    .flatten_uint_expression(statements_flattened, lhs)
                    .get_field_unchecked();
                let rhs = self
                    .flatten_uint_expression(statements_flattened, rhs)
                    .get_field_unchecked();

                let x = FlatExpression::Sub(box lhs, box rhs);

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
            BooleanExpression::FieldLe(box lhs, box rhs) => {
                let lt = self.flatten_boolean_expression(
                    statements_flattened,
                    BooleanExpression::FieldLt(box lhs.clone(), box rhs.clone()),
                );
                let eq = self.flatten_boolean_expression(
                    statements_flattened,
                    BooleanExpression::FieldEq(box lhs.clone(), box rhs.clone()),
                );
                FlatExpression::Add(box eq, box lt)
            }
            BooleanExpression::FieldGt(lhs, rhs) => self.flatten_boolean_expression(
                statements_flattened,
                BooleanExpression::FieldLt(rhs, lhs),
            ),
            BooleanExpression::FieldGe(lhs, rhs) => self.flatten_boolean_expression(
                statements_flattened,
                BooleanExpression::FieldLe(rhs, lhs),
            ),
            BooleanExpression::UintLt(box lhs, box rhs) => {
                let lhs_flattened = self.flatten_uint_expression(statements_flattened, lhs);
                let rhs_flattened = self.flatten_uint_expression(statements_flattened, rhs);

                // Get the bit width to know the size of the binary decompositions for this Field
                // This is not this uint bitwidth
                let bit_width = T::get_required_bits();

                // lhs
                let lhs_id = self.define(lhs_flattened.get_field_unchecked(), statements_flattened);
                let rhs_id = self.define(rhs_flattened.get_field_unchecked(), statements_flattened);

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
                for bit in sub_bits_be.iter().take(bit_width) {
                    statements_flattened.push(FlatStatement::Condition(
                        FlatExpression::Identifier(*bit),
                        FlatExpression::Mult(
                            box FlatExpression::Identifier(*bit),
                            box FlatExpression::Identifier(*bit),
                        ),
                    ));
                }

                // check that the decomposition is in the field with a strict `< p` checks
                self.strict_le_check(
                    statements_flattened,
                    &T::max_value_bit_vector_be(),
                    sub_bits_be.clone(),
                );

                // sum(sym_b{i} * 2**i)
                let mut expr = FlatExpression::Number(T::from(0));

                for (i, bit) in sub_bits_be.iter().enumerate().take(bit_width) {
                    expr = FlatExpression::Add(
                        box expr,
                        box FlatExpression::Mult(
                            box FlatExpression::Identifier(*bit),
                            box FlatExpression::Number(T::from(2).pow(bit_width - i - 1)),
                        ),
                    );
                }

                statements_flattened.push(FlatStatement::Condition(subtraction_result, expr));

                FlatExpression::Identifier(sub_bits_be[bit_width - 1])
            }
            BooleanExpression::UintLe(box lhs, box rhs) => {
                let lt = self.flatten_boolean_expression(
                    statements_flattened,
                    BooleanExpression::UintLt(box lhs.clone(), box rhs.clone()),
                );
                let eq = self.flatten_boolean_expression(
                    statements_flattened,
                    BooleanExpression::UintEq(box lhs.clone(), box rhs.clone()),
                );
                FlatExpression::Add(box eq, box lt)
            }
            BooleanExpression::UintGt(lhs, rhs) => self.flatten_boolean_expression(
                statements_flattened,
                BooleanExpression::UintLt(rhs, lhs),
            ),
            BooleanExpression::UintGe(lhs, rhs) => self.flatten_boolean_expression(
                statements_flattened,
                BooleanExpression::UintLe(rhs, lhs),
            ),
            BooleanExpression::Or(box lhs, box rhs) => {
                let x = self.flatten_boolean_expression(statements_flattened, lhs);
                let y = self.flatten_boolean_expression(statements_flattened, rhs);
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
                let x = self.flatten_boolean_expression(statements_flattened, lhs);
                let y = self.flatten_boolean_expression(statements_flattened, rhs);

                let name_x_and_y = self.use_sym();
                assert!(x.is_linear() && y.is_linear());
                statements_flattened.push(FlatStatement::Definition(
                    name_x_and_y,
                    FlatExpression::Mult(box x, box y),
                ));

                FlatExpression::Identifier(name_x_and_y)
            }
            BooleanExpression::Not(box exp) => {
                let x = self.flatten_boolean_expression(statements_flattened, exp);
                FlatExpression::Sub(box FlatExpression::Number(T::one()), box x)
            }
            BooleanExpression::Value(b) => FlatExpression::Number(match b {
                true => T::from(1),
                false => T::from(0),
            }),
            BooleanExpression::IfElse(box condition, box consequence, box alternative) => self
                .flatten_if_else_expression(
                    statements_flattened,
                    condition,
                    consequence,
                    alternative,
                )
                .get_field_unchecked(),
        }
    }

    fn flatten_u_to_bits(
        &mut self,
        statements_flattened: &mut FlatStatements<T>,
        expression: ZirExpression<'ast, T>,
        bitwidth: UBitwidth,
    ) -> Vec<FlatUExpression<T>> {
        let expression = UExpression::try_from(expression).unwrap();
        let from = expression.metadata.clone().unwrap().bitwidth();
        let p = self.flatten_uint_expression(statements_flattened, expression);
        self.get_bits(p, from as usize, bitwidth, statements_flattened)
            .into_iter()
            .map(FlatUExpression::with_field)
            .collect()
    }

    fn flatten_bits_to_u(
        &mut self,
        statements_flattened: &mut FlatStatements<T>,
        bits: Vec<ZirExpression<'ast, T>>,
        bitwidth: UBitwidth,
    ) -> FlatUExpression<T> {
        assert_eq!(bits.len(), bitwidth.to_usize());
        let bits: Vec<_> = bits
            .into_iter()
            .map(|p| {
                self.flatten_expression(statements_flattened, p)
                    .get_field_unchecked()
            })
            .collect();

        FlatUExpression::with_bits(bits)
    }

    /// Flattens a function call
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `id` - `Identifier of the function.
    /// * `return_types` - Types of the return values of the function
    /// * `param_expressions` - Arguments of this call
    fn flatten_embed_call(
        &mut self,
        statements_flattened: &mut FlatStatements<T>,
        embed: FlatEmbed,
        generics: Vec<u32>,
        param_expressions: Vec<ZirExpression<'ast, T>>,
    ) -> Vec<FlatUExpression<T>> {
        match embed {
            crate::embed::FlatEmbed::U64ToBits => self.flatten_u_to_bits(
                statements_flattened,
                param_expressions[0].clone(),
                64.into(),
            ),
            crate::embed::FlatEmbed::U32ToBits => self.flatten_u_to_bits(
                statements_flattened,
                param_expressions[0].clone(),
                32.into(),
            ),
            crate::embed::FlatEmbed::U16ToBits => self.flatten_u_to_bits(
                statements_flattened,
                param_expressions[0].clone(),
                16.into(),
            ),
            crate::embed::FlatEmbed::U8ToBits => {
                self.flatten_u_to_bits(statements_flattened, param_expressions[0].clone(), 8.into())
            }
            crate::embed::FlatEmbed::U64FromBits => {
                vec![self.flatten_bits_to_u(statements_flattened, param_expressions, 64.into())]
            }
            crate::embed::FlatEmbed::U32FromBits => {
                vec![self.flatten_bits_to_u(statements_flattened, param_expressions, 32.into())]
            }
            crate::embed::FlatEmbed::U16FromBits => {
                vec![self.flatten_bits_to_u(statements_flattened, param_expressions, 16.into())]
            }
            crate::embed::FlatEmbed::U8FromBits => {
                vec![self.flatten_bits_to_u(statements_flattened, param_expressions, 8.into())]
            }
            funct => {
                let funct = funct.synthetize(&generics);

                let mut replacement_map = HashMap::new();

                // Handle complex parameters and assign values:
                // Rename Parameters, assign them to values in call. Resolve complex expressions with definitions
                // Clippy doesn't like the fact that we're collecting here, however not doing so leads to a borrow issue
                // of `self` in the for-loop just after. This is why the `needless_collect` lint is disabled for this file
                // (it does not work for this single line)
                let params_flattened = param_expressions
                    .into_iter()
                    .map(|param_expr| self.flatten_expression(statements_flattened, param_expr))
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

                let (mut return_statements, statements): (Vec<_>, Vec<_>) = funct
                    .statements
                    .into_iter()
                    .partition(|s| matches!(s, FlatStatement::Return(..)));

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
                    FlatStatement::Return(list) => list
                        .expressions
                        .into_iter()
                        .map(|x| x.apply_substitution(&replacement_map))
                        .map(FlatUExpression::with_field)
                        .collect(),
                    _ => unreachable!(),
                }
            }
        }
    }

    /// Flattens an expression
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `expr` - `ZirExpression` that will be flattened.
    fn flatten_expression(
        &mut self,
        statements_flattened: &mut FlatStatements<T>,
        expr: ZirExpression<'ast, T>,
    ) -> FlatUExpression<T> {
        match expr {
            ZirExpression::FieldElement(e) => {
                FlatUExpression::with_field(self.flatten_field_expression(statements_flattened, e))
            }
            ZirExpression::Boolean(e) => FlatUExpression::with_field(
                self.flatten_boolean_expression(statements_flattened, e),
            ),
            ZirExpression::Uint(e) => self.flatten_uint_expression(statements_flattened, e),
        }
    }

    fn default_xor(
        &mut self,
        statements_flattened: &mut FlatStatements<T>,
        left: UExpression<'ast, T>,
        right: UExpression<'ast, T>,
    ) -> FlatUExpression<T> {
        let left_flattened = self.flatten_uint_expression(statements_flattened, left);
        let right_flattened = self.flatten_uint_expression(statements_flattened, right);

        // `left` and `right` were reduced to the target bitwidth, hence their bits are available

        let left_bits = left_flattened.bits.unwrap();
        let right_bits = right_flattened.bits.unwrap();

        let xor: Vec<FlatExpression<T>> = left_bits
            .into_iter()
            .zip(right_bits.into_iter())
            .map(|(x, y)| match (x, y) {
                (FlatExpression::Number(n), e) | (e, FlatExpression::Number(n)) => {
                    if n == T::from(0) {
                        self.define(e, statements_flattened).into()
                    } else if n == T::from(1) {
                        self.define(
                            FlatExpression::Sub(
                                box FlatExpression::Number(T::from(1)),
                                box e.clone(),
                            ),
                            statements_flattened,
                        )
                        .into()
                    } else {
                        unreachable!()
                    }
                }
                (x, y) => {
                    let name = self.use_sym();

                    statements_flattened.extend(vec![
                        FlatStatement::Directive(FlatDirective::new(
                            vec![name],
                            Solver::Xor,
                            vec![x.clone(), y.clone()],
                        )),
                        FlatStatement::Condition(
                            FlatExpression::Add(
                                box x.clone(),
                                box FlatExpression::Sub(box y.clone(), box name.clone().into()),
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

        FlatUExpression::with_bits(xor)
    }

    fn euclidean_division(
        &mut self,
        statements_flattened: &mut FlatStatements<T>,
        target_bitwidth: UBitwidth,
        left: UExpression<'ast, T>,
        right: UExpression<'ast, T>,
    ) -> (FlatExpression<T>, FlatExpression<T>) {
        let left_flattened = self
            .flatten_uint_expression(statements_flattened, left)
            .get_field_unchecked();
        let right_flattened = self
            .flatten_uint_expression(statements_flattened, right)
            .get_field_unchecked();
        let n = if left_flattened.is_linear() {
            left_flattened
        } else {
            let id = self.use_sym();
            statements_flattened.push(FlatStatement::Definition(id, left_flattened));
            FlatExpression::Identifier(id)
        };
        let d = if right_flattened.is_linear() {
            right_flattened
        } else {
            let id = self.use_sym();
            statements_flattened.push(FlatStatement::Definition(id, right_flattened));
            FlatExpression::Identifier(id)
        };

        // first check that the d is not 0 by giving its inverse
        let invd = self.use_sym();

        // # invd = 1/d
        statements_flattened.push(FlatStatement::Directive(FlatDirective::new(
            vec![invd],
            Solver::Div,
            vec![FlatExpression::Number(T::one()), d.clone()],
        )));

        // assert(invd * d == 1)
        statements_flattened.push(FlatStatement::Condition(
            FlatExpression::Number(T::one()),
            FlatExpression::Mult(box invd.into(), box d.clone()),
        ));

        // now introduce the quotient and remainder
        let q = self.use_sym();
        let r = self.use_sym();

        statements_flattened.push(FlatStatement::Directive(FlatDirective {
            inputs: vec![n.clone(), d.clone()],
            outputs: vec![q, r],
            solver: Solver::EuclideanDiv,
        }));

        // q in range
        let _ = self.get_bits(
            FlatUExpression::with_field(FlatExpression::from(q)),
            target_bitwidth.to_usize(),
            target_bitwidth,
            statements_flattened,
        );

        // r in range
        let _ = self.get_bits(
            FlatUExpression::with_field(FlatExpression::from(r)),
            target_bitwidth.to_usize(),
            target_bitwidth,
            statements_flattened,
        );

        // r < d <=> r - d + 2**w < 2**w
        let _ = self.get_bits(
            FlatUExpression::with_field(FlatExpression::Add(
                box FlatExpression::Sub(box r.into(), box d.clone()),
                box FlatExpression::Number(T::from(2_u128.pow(target_bitwidth.to_usize() as u32))),
            )),
            target_bitwidth.to_usize(),
            target_bitwidth,
            statements_flattened,
        );

        // q*d == n - r
        statements_flattened.push(FlatStatement::Condition(
            FlatExpression::Sub(box n, box r.into()),
            FlatExpression::Mult(box q.into(), box d),
        ));

        (q.into(), r.into())
    }

    /// Flattens a uint expression
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `expr` - `UExpression` that will be flattened.
    fn flatten_uint_expression(
        &mut self,
        statements_flattened: &mut FlatStatements<T>,
        expr: UExpression<'ast, T>,
    ) -> FlatUExpression<T> {
        // the bitwidth for this type of uint (8, 16 or 32)
        let target_bitwidth = expr.bitwidth;

        let metadata = expr.metadata.clone().unwrap();

        // the bitwidth on which this value is currently represented
        let actual_bitwidth = metadata.bitwidth() as usize;

        // whether this value should be reduced, for example if it is then used in a bitwidth operation
        let should_reduce = metadata.should_reduce;

        let should_reduce = should_reduce.to_bool();

        let res = match expr.into_inner() {
            UExpressionInner::Value(x) => {
                FlatUExpression::with_field(FlatExpression::Number(T::from(x as usize)))
            } // force to be a field element
            UExpressionInner::Identifier(x) => {
                let field = FlatExpression::Identifier(*self.layout.get(&x).unwrap());
                let bits = self.bits_cache.get(&field).map(|bits| {
                    assert_eq!(bits.len(), target_bitwidth.to_usize());
                    bits.clone()
                });
                FlatUExpression::with_field(field).bits(bits)
            }
            UExpressionInner::Not(box e) => {
                let e = self.flatten_uint_expression(statements_flattened, e);

                let e_bits = e.bits.unwrap();

                assert_eq!(e_bits.len(), target_bitwidth.to_usize());

                let name_not: Vec<_> = e_bits
                    .into_iter()
                    .map(|bit| {
                        self.define(
                            FlatExpression::Sub(box FlatExpression::Number(T::from(1)), box bit),
                            statements_flattened,
                        )
                        .into()
                    })
                    .collect();

                FlatUExpression::with_bits(name_not)
            }
            UExpressionInner::Add(box left, box right) => {
                let left_flattened = self
                    .flatten_uint_expression(statements_flattened, left)
                    .get_field_unchecked();

                let right_flattened = self
                    .flatten_uint_expression(statements_flattened, right)
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
                // see uint optimizer for the reasoning here
                let aux = FlatExpression::Number(
                    T::from(2).pow(right.metadata.clone().unwrap().bitwidth() as usize),
                );

                let left_flattened = self
                    .flatten_uint_expression(statements_flattened, left)
                    .get_field_unchecked();
                let right_flattened = self
                    .flatten_uint_expression(statements_flattened, right)
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
                assert_eq!(by.bitwidth(), UBitwidth::B32);

                let by = match by.into_inner() {
                    UExpressionInner::Value(n) => n,
                    by => unimplemented!(
                        "Variable shifts are unimplemented, found {} << {}",
                        e,
                        by.annotate(UBitwidth::B32)
                    ),
                };

                let e = self.flatten_uint_expression(statements_flattened, e);

                let e_bits = e.bits.unwrap();

                assert_eq!(e_bits.len(), target_bitwidth.to_usize());

                FlatUExpression::with_bits(
                    e_bits
                        .into_iter()
                        .skip(by as usize)
                        .chain(
                            (0..std::cmp::min(by as usize, target_bitwidth.to_usize()))
                                .map(|_| FlatExpression::Number(T::from(0))),
                        )
                        .collect::<Vec<_>>(),
                )
            }
            UExpressionInner::RightShift(box e, box by) => {
                assert_eq!(by.bitwidth(), UBitwidth::B32);

                let by = match by.into_inner() {
                    UExpressionInner::Value(n) => n,
                    by => unimplemented!(
                        "Variable shifts are unimplemented, found {} >> {}",
                        e,
                        by.annotate(UBitwidth::B32)
                    ),
                };

                let e = self.flatten_uint_expression(statements_flattened, e);

                let e_bits = e.bits.unwrap();

                assert_eq!(e_bits.len(), target_bitwidth.to_usize());

                FlatUExpression::with_bits(
                    (0..std::cmp::min(by as usize, target_bitwidth.to_usize()))
                        .map(|_| FlatExpression::Number(T::from(0)))
                        .chain(e_bits.into_iter().take(
                            target_bitwidth.to_usize()
                                - std::cmp::min(by as usize, target_bitwidth.to_usize()),
                        ))
                        .collect::<Vec<_>>(),
                )
            }
            UExpressionInner::Mult(box left, box right) => {
                let left_flattened = self
                    .flatten_uint_expression(statements_flattened, left)
                    .get_field_unchecked();
                let right_flattened = self
                    .flatten_uint_expression(statements_flattened, right)
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
            UExpressionInner::Div(box left, box right) => {
                let (q, _) =
                    self.euclidean_division(statements_flattened, target_bitwidth, left, right);

                FlatUExpression::with_field(q)
            }
            UExpressionInner::Rem(box left, box right) => {
                let (_, r) =
                    self.euclidean_division(statements_flattened, target_bitwidth, left, right);

                FlatUExpression::with_field(r)
            }
            UExpressionInner::IfElse(box condition, box consequence, box alternative) => self
                .flatten_if_else_expression(
                    statements_flattened,
                    condition,
                    consequence,
                    alternative,
                ),
            UExpressionInner::Xor(box left, box right) => {
                let left_metadata = left.metadata.clone().unwrap();
                let right_metadata = right.metadata.clone().unwrap();

                match (left.into_inner(), right.into_inner()) {
                    (UExpressionInner::And(box a, box b), UExpressionInner::And(box aa, box c)) => {
                        if aa.clone().into_inner() == UExpressionInner::Not(box a.clone()) {
                            let a_flattened = self.flatten_uint_expression(statements_flattened, a);
                            let b_flattened = self.flatten_uint_expression(statements_flattened, b);
                            let c_flattened = self.flatten_uint_expression(statements_flattened, c);

                            let a_bits = a_flattened.bits.unwrap();
                            let b_bits = b_flattened.bits.unwrap();
                            let c_bits = c_flattened.bits.unwrap();

                            let res: Vec<FlatExpression<T>> = a_bits
                                .into_iter()
                                .zip(b_bits.into_iter())
                                .zip(c_bits.into_iter())
                                .map(|((a, b), c)| {
                                    // a(b - c) = ch - c

                                    let ch = self.use_sym();

                                    statements_flattened.extend(vec![
                                        FlatStatement::Directive(FlatDirective::new(
                                            vec![ch],
                                            Solver::ShaCh,
                                            vec![a.clone(), b.clone(), c.clone()],
                                        )),
                                        FlatStatement::Condition(
                                            FlatExpression::Sub(box ch.into(), box c.clone()),
                                            FlatExpression::Mult(
                                                box a,
                                                box FlatExpression::Sub(box b, box c),
                                            ),
                                        ),
                                    ]);
                                    ch.into()
                                })
                                .collect();

                            FlatUExpression::with_bits(res)
                        } else {
                            self.default_xor(
                                statements_flattened,
                                UExpressionInner::And(box a, box b)
                                    .annotate(target_bitwidth)
                                    .metadata(left_metadata),
                                UExpressionInner::And(box aa, box c)
                                    .annotate(target_bitwidth)
                                    .metadata(right_metadata),
                            )
                        }
                    }
                    (UExpressionInner::Xor(box a, box b), c) => {
                        let a_metadata = a.metadata.clone().unwrap();
                        let b_metadata = b.metadata.clone().unwrap();

                        match (a.into_inner(), b.into_inner(), c) {
                            (
                                UExpressionInner::And(box a, box b),
                                UExpressionInner::And(box aa, box c),
                                UExpressionInner::And(box bb, box cc),
                            ) => {
                                if (aa == a) && (bb == b) && (cc == c) {
                                    let a_flattened =
                                        self.flatten_uint_expression(statements_flattened, a);
                                    let b_flattened =
                                        self.flatten_uint_expression(statements_flattened, b);
                                    let c_flattened =
                                        self.flatten_uint_expression(statements_flattened, c);

                                    let a_bits = a_flattened.bits.unwrap();
                                    let b_bits = b_flattened.bits.unwrap();
                                    let c_bits = c_flattened.bits.unwrap();

                                    let res: Vec<FlatExpression<T>> = a_bits
                                        .into_iter()
                                        .zip(b_bits.into_iter())
                                        .zip(c_bits.into_iter())
                                        .map(|((a, b), c)| {
                                            // (b) * (c) = (bc)
                                            // (2bc - b - c) * (a) = bc - maj

                                            let maj = self.use_sym();
                                            let bc = self.use_sym();

                                            statements_flattened.extend(vec![
                                                FlatStatement::Directive(FlatDirective::new(
                                                    vec![maj],
                                                    Solver::ShaAndXorAndXorAnd,
                                                    vec![a.clone(), b.clone(), c.clone()],
                                                )),
                                                FlatStatement::Condition(
                                                    bc.clone().into(),
                                                    FlatExpression::Mult(
                                                        box b.clone(),
                                                        box c.clone(),
                                                    ),
                                                ),
                                                FlatStatement::Condition(
                                                    FlatExpression::Sub(
                                                        box bc.clone().into(),
                                                        box maj.into(),
                                                    ),
                                                    FlatExpression::Mult(
                                                        box FlatExpression::Sub(
                                                            box FlatExpression::Add(
                                                                box bc.clone().into(),
                                                                box bc.clone().into(),
                                                            ),
                                                            box FlatExpression::Add(box b, box c),
                                                        ),
                                                        box a,
                                                    ),
                                                ),
                                            ]);
                                            maj.into()
                                        })
                                        .collect();

                                    FlatUExpression::with_bits(res)
                                } else {
                                    self.default_xor(
                                        statements_flattened,
                                        UExpressionInner::Xor(
                                            box UExpressionInner::And(box a, box b)
                                                .annotate(target_bitwidth)
                                                .metadata(a_metadata),
                                            box UExpressionInner::And(box aa, box c)
                                                .annotate(target_bitwidth)
                                                .metadata(b_metadata),
                                        )
                                        .annotate(target_bitwidth)
                                        .metadata(left_metadata),
                                        UExpressionInner::And(box bb, box cc)
                                            .annotate(target_bitwidth)
                                            .metadata(right_metadata),
                                    )
                                }
                            }
                            (a, b, c) => self.default_xor(
                                statements_flattened,
                                UExpressionInner::Xor(
                                    box a.annotate(target_bitwidth).metadata(a_metadata),
                                    box b.annotate(target_bitwidth).metadata(b_metadata),
                                )
                                .annotate(target_bitwidth)
                                .metadata(left_metadata),
                                c.annotate(target_bitwidth).metadata(right_metadata),
                            ),
                        }
                    }
                    (left_i, right_i) => self.default_xor(
                        statements_flattened,
                        left_i.annotate(target_bitwidth).metadata(left_metadata),
                        right_i.annotate(target_bitwidth).metadata(right_metadata),
                    ),
                }
            }
            UExpressionInner::And(box left, box right) => {
                let left_flattened = self.flatten_uint_expression(statements_flattened, left);

                let right_flattened = self.flatten_uint_expression(statements_flattened, right);

                let left_bits = left_flattened.bits.unwrap();
                let right_bits = right_flattened.bits.unwrap();

                assert_eq!(left_bits.len(), target_bitwidth.to_usize());
                assert_eq!(right_bits.len(), target_bitwidth.to_usize());

                let and: Vec<_> = left_bits
                    .into_iter()
                    .zip(right_bits.into_iter())
                    .map(|(x, y)| match (x, y) {
                        (FlatExpression::Number(n), e) | (e, FlatExpression::Number(n)) => {
                            if n == T::from(0) {
                                FlatExpression::Number(T::from(0))
                            } else if n == T::from(1) {
                                e
                            } else {
                                unreachable!();
                            }
                        }
                        (x, y) => self
                            .define(
                                FlatExpression::Mult(box x.clone(), box y.clone()),
                                statements_flattened,
                            )
                            .into(),
                    })
                    .collect();

                FlatUExpression::with_bits(and)
            }
            UExpressionInner::Or(box left, box right) => {
                let left_flattened = self.flatten_uint_expression(statements_flattened, left);
                let right_flattened = self.flatten_uint_expression(statements_flattened, right);

                let left_bits = left_flattened.bits.unwrap();
                let right_bits = right_flattened.bits.unwrap();

                assert_eq!(left_bits.len(), target_bitwidth.to_usize());
                assert_eq!(right_bits.len(), target_bitwidth.to_usize());

                assert_eq!(left_bits.len(), target_bitwidth.to_usize());
                assert_eq!(right_bits.len(), target_bitwidth.to_usize());

                let or: Vec<FlatExpression<T>> = left_bits
                    .into_iter()
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
                                    vec![name],
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
                    })
                    .collect();

                FlatUExpression::with_bits(or)
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

                let field = if actual_bitwidth > target_bitwidth.to_usize() {
                    bits.iter().enumerate().fold(
                        FlatExpression::Number(T::from(0)),
                        |acc, (index, bit)| {
                            FlatExpression::Add(
                                box acc,
                                box FlatExpression::Mult(
                                    box FlatExpression::Number(
                                        T::from(2).pow(target_bitwidth.to_usize() - index - 1),
                                    ),
                                    box bit.clone(),
                                ),
                            )
                        },
                    )
                } else {
                    res.get_field_unchecked()
                };

                FlatUExpression::with_bits(bits).field(field)
            }
            false => res,
        };

        res
    }

    fn get_bits(
        &mut self,
        e: FlatUExpression<T>,
        from: usize,
        to: UBitwidth,
        statements_flattened: &mut FlatStatements<T>,
    ) -> Vec<FlatExpression<T>> {
        let to = to.to_usize();

        assert!(from < T::get_required_bits());
        assert!(to < T::get_required_bits());

        // constants do not require directives
        if let Some(FlatExpression::Number(ref x)) = e.field {
            let bits: Vec<_> = Interpreter::default()
                .execute_solver(&Solver::bits(to), &[x.clone()])
                .unwrap()
                .into_iter()
                .map(FlatExpression::Number)
                .collect();

            assert_eq!(bits.len(), to);

            self.bits_cache
                .insert(e.field.clone().unwrap(), bits.clone());
            return bits;
        };

        e.bits.clone().unwrap_or_else(|| {
            // we are not reducing a constant, therefore the result should always have a smaller bitwidth:
            // `to` is the target bitwidth, and `from` cannot be smaller than that unless we're looking at a
            // constant

            let from = std::cmp::max(from, to);
            match self.bits_cache.entry(e.field.clone().unwrap()) {
                Entry::Occupied(entry) => {
                    let res: Vec<_> = entry.get().clone();
                    // if we already know a decomposition, it has to be of the size of the target bitwidth
                    assert_eq!(res.len(), to);
                    res
                }
                Entry::Vacant(_) => {
                    let bits = (0..from).map(|_| self.use_sym()).collect::<Vec<_>>();
                    statements_flattened.push(FlatStatement::Directive(FlatDirective::new(
                        bits.clone(),
                        Solver::Bits(from),
                        vec![e.field.clone().unwrap()],
                    )));

                    let bits: Vec<_> = bits.into_iter().map(FlatExpression::Identifier).collect();

                    // decompose to the actual bitwidth

                    // bit checks
                    statements_flattened.extend(bits.iter().take(from).map(|bit| {
                        FlatStatement::Condition(
                            bit.clone(),
                            FlatExpression::Mult(box bit.clone(), box bit.clone()),
                        )
                    }));

                    let sum = flat_expression_from_bits(bits.clone());

                    // sum check
                    statements_flattened.push(FlatStatement::Condition(
                        e.field.clone().unwrap(),
                        sum.clone(),
                    ));

                    // truncate to the `to` lowest bits
                    let bits = bits[from - to..].to_vec();

                    assert_eq!(bits.len(), to);

                    self.bits_cache.insert(e.field.unwrap(), bits.clone());
                    self.bits_cache.insert(sum, bits.clone());

                    bits
                }
            }
        })
    }

    /// Flattens a field expression
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `expr` - `FieldElementExpression` that will be flattened.
    fn flatten_field_expression(
        &mut self,
        statements_flattened: &mut FlatStatements<T>,
        expr: FieldElementExpression<'ast, T>,
    ) -> FlatExpression<T> {
        match expr {
            FieldElementExpression::Number(x) => FlatExpression::Number(x), // force to be a field element
            FieldElementExpression::Identifier(x) => {
                FlatExpression::Identifier(*self.layout.get(&x).unwrap_or_else(|| panic!("{}", x)))
            }
            FieldElementExpression::Add(box left, box right) => {
                let left_flattened = self.flatten_field_expression(statements_flattened, left);
                let right_flattened = self.flatten_field_expression(statements_flattened, right);
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
                let left_flattened = self.flatten_field_expression(statements_flattened, left);
                let right_flattened = self.flatten_field_expression(statements_flattened, right);

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
                let left_flattened = self.flatten_field_expression(statements_flattened, left);
                let right_flattened = self.flatten_field_expression(statements_flattened, right);
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
                let left_flattened = self.flatten_field_expression(statements_flattened, left);
                let right_flattened = self.flatten_field_expression(statements_flattened, right);
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
                    FlatExpression::Mult(box invb.into(), box new_right.clone()),
                ));

                // # c = a/b
                statements_flattened.push(FlatStatement::Directive(FlatDirective::new(
                    vec![inverse],
                    Solver::Div,
                    vec![new_left.clone(), new_right.clone()],
                )));

                // assert(c * b == a)
                statements_flattened.push(FlatStatement::Condition(
                    new_left,
                    FlatExpression::Mult(box new_right, box inverse.into()),
                ));

                inverse.into()
            }
            FieldElementExpression::Pow(box base, box exponent) => {
                match exponent.into_inner() {
                    UExpressionInner::Value(ref e) => {
                        // flatten the base expression
                        let base_flattened =
                            self.flatten_field_expression(statements_flattened, base.clone());

                        // we require from the base to be linear
                        // TODO change that
                        assert!(base_flattened.is_linear());

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
                                            id,
                                            FlatExpression::Mult(
                                                box previous.clone(),
                                                box previous.clone(),
                                            ),
                                        ));
                                        // store it in the state for later squaring
                                        *state = Some(FlatExpression::Identifier(id));
                                        // return it for later use constructing the result
                                        Some(FlatExpression::Identifier(id))
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
                    statements_flattened,
                    condition,
                    consequence,
                    alternative,
                )
                .get_field_unchecked(),
        }
    }

    /// Flattens a statement
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `stat` - `ZirStatement` that will be flattened.
    fn flatten_statement(
        &mut self,
        statements_flattened: &mut FlatStatements<T>,
        stat: ZirStatement<'ast, T>,
    ) {
        match stat {
            ZirStatement::Return(exprs) => {
                let flat_expressions = exprs
                    .into_iter()
                    .map(|expr| self.flatten_expression(statements_flattened, expr))
                    .map(|x| x.get_field_unchecked())
                    .collect::<Vec<_>>();

                statements_flattened.push(FlatStatement::Return(FlatExpressionList {
                    expressions: flat_expressions,
                }));
            }
            ZirStatement::Declaration(_) => {
                // declarations have already been checked
            }
            ZirStatement::Definition(assignee, expr) => {
                // define n variables with n the number of primitive types for v_type
                // assign them to the n primitive types for expr

                let rhs = self.flatten_expression(statements_flattened, expr);

                let bits = rhs.bits.clone();

                let var = match rhs.get_field_unchecked() {
                    FlatExpression::Identifier(id) => {
                        self.use_variable_with_existing(&assignee, id);
                        id
                    }
                    e => {
                        let var = self.use_variable(&assignee);

                        // handle return of function call
                        statements_flattened.push(FlatStatement::Definition(var, e));

                        var
                    }
                };

                // register bits
                if let Some(bits) = bits {
                    self.bits_cache
                        .insert(FlatExpression::Identifier(var), bits);
                }
            }
            ZirStatement::Assertion(e) => {
                match e {
                    BooleanExpression::And(..) => {
                        for boolean in e.into_conjunction_iterator() {
                            self.flatten_statement(
                                statements_flattened,
                                ZirStatement::Assertion(boolean),
                            )
                        }
                    }
                    BooleanExpression::FieldEq(box lhs, box rhs) => {
                        let lhs = self.flatten_field_expression(statements_flattened, lhs);
                        let rhs = self.flatten_field_expression(statements_flattened, rhs);

                        self.flatten_equality(statements_flattened, lhs, rhs)
                    }
                    BooleanExpression::UintEq(box lhs, box rhs) => {
                        let lhs = self
                            .flatten_uint_expression(statements_flattened, lhs)
                            .get_field_unchecked();
                        let rhs = self
                            .flatten_uint_expression(statements_flattened, rhs)
                            .get_field_unchecked();

                        self.flatten_equality(statements_flattened, lhs, rhs)
                    }
                    BooleanExpression::BoolEq(box lhs, box rhs) => {
                        let lhs = self.flatten_boolean_expression(statements_flattened, lhs);
                        let rhs = self.flatten_boolean_expression(statements_flattened, rhs);

                        self.flatten_equality(statements_flattened, lhs, rhs)
                    }
                    _ => {
                        // naive approach: flatten the boolean to a single field element and constrain it to 1
                        let e = self.flatten_boolean_expression(statements_flattened, e);

                        if e.is_linear() {
                            statements_flattened.push(FlatStatement::Condition(
                                e,
                                FlatExpression::Number(T::from(1)),
                            ));
                        } else {
                            // swap so that left side is linear
                            statements_flattened.push(FlatStatement::Condition(
                                FlatExpression::Number(T::from(1)),
                                e,
                            ));
                        }
                    }
                }
            }
            ZirStatement::MultipleDefinition(vars, rhs) => {
                // flatten the right side to p = sum(var_i.type.primitive_count) expressions
                // define p new variables to the right side expressions

                match rhs {
                    ZirExpressionList::EmbedCall(embed, generics, exprs) => {
                        let rhs_flattened = self.flatten_embed_call(
                            statements_flattened,
                            embed,
                            generics,
                            exprs.clone(),
                        );

                        let rhs = rhs_flattened.into_iter();

                        assert_eq!(vars.len(), rhs.len());

                        let vars: Vec<_> = vars
                            .into_iter()
                            .zip(rhs)
                            .map(|(v, r)| match r.get_field_unchecked() {
                                FlatExpression::Identifier(id) => {
                                    self.use_variable_with_existing(&v, id);
                                    id
                                }
                                e => {
                                    let id = self.use_variable(&v);
                                    statements_flattened.push(FlatStatement::Definition(id, e));
                                    id
                                }
                            })
                            .collect();

                        match embed {
                            FlatEmbed::U64FromBits
                            | FlatEmbed::U32FromBits
                            | FlatEmbed::U16FromBits
                            | FlatEmbed::U8FromBits => {
                                let bits = exprs
                                    .into_iter()
                                    .map(|e| {
                                        self.flatten_expression(statements_flattened, e)
                                            .get_field_unchecked()
                                    })
                                    .collect();
                                self.bits_cache.insert(vars[0].clone().into(), bits);
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
    }

    /// Flattens a function
    ///
    /// # Arguments
    /// * `funct` - `ZirFunction` that will be flattened
    fn flatten_function(&mut self, funct: ZirFunction<'ast, T>) -> FlatFunction<T> {
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
            self.flatten_statement(&mut statements_flattened, stat);
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
    /// * `prog` - `ZirProgram` that will be flattened.
    fn flatten_program(&mut self, prog: ZirProgram<'ast, T>) -> FlatProg<T> {
        FlatProg {
            main: self.flatten_function(prog.main),
        }
    }

    /// Flattens an equality expression
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - `FlatStatements<T>` Vector where new flattened statements can be added.
    /// * `lhs` - `FlatExpression<T>` Left-hand side of the equality expression.
    /// * `rhs` - `FlatExpression<T>` Right-hand side of the equality expression.
    fn flatten_equality(
        &mut self,
        statements_flattened: &mut FlatStatements<T>,
        lhs: FlatExpression<T>,
        rhs: FlatExpression<T>,
    ) {
        let (lhs, rhs) = match (lhs, rhs) {
            (FlatExpression::Mult(box x, box y), z) | (z, FlatExpression::Mult(box x, box y)) => (
                self.identify_expression(z, statements_flattened),
                FlatExpression::Mult(
                    box self.identify_expression(x, statements_flattened),
                    box self.identify_expression(y, statements_flattened),
                ),
            ),
            (x, z) => (
                self.identify_expression(z, statements_flattened),
                FlatExpression::Mult(
                    box self.identify_expression(x, statements_flattened),
                    box FlatExpression::Number(T::from(1)),
                ),
            ),
        };
        statements_flattened.push(FlatStatement::Condition(lhs, rhs));
    }

    /// Identifies a non-linear expression by assigning it to a new identifier.
    ///
    /// # Arguments
    ///
    /// * `e` - `FlatExpression<T>` Expression to be assigned to an identifier.
    /// * `statements_flattened` - `FlatStatements<T>` Vector where new flattened statements can be added.
    fn identify_expression(
        &mut self,
        e: FlatExpression<T>,
        statements_flattened: &mut FlatStatements<T>,
    ) -> FlatExpression<T> {
        match e.is_linear() {
            true => e,
            false => {
                let sym = self.use_sym();
                statements_flattened.push(FlatStatement::Definition(sym, e));
                FlatExpression::Identifier(sym)
            }
        }
    }

    /// Returns a fresh FlatVariable for a given Variable
    /// # Arguments
    ///
    /// * `variable` - a variable in the program being flattened
    fn use_variable(&mut self, variable: &Variable<'ast>) -> FlatVariable {
        let var = self.issue_new_variable();

        self.layout.insert(variable.id.clone(), var);
        var
    }

    /// Reuse an existing variable for a new name
    /// # Arguments
    ///
    /// * `variable` - a variable in the program being flattened
    /// * `flat_variable` - an existing flat variable
    fn use_variable_with_existing(
        &mut self,
        variable: &Variable<'ast>,
        flat_variable: FlatVariable,
    ) {
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
                // to constrain unsigned integer inputs to be in range, we get their bit decomposition.
                // it will be cached
                self.get_bits(
                    FlatUExpression::with_field(FlatExpression::Identifier(variable)),
                    bitwidth.to_usize(),
                    bitwidth,
                    statements_flattened,
                );
            }
            Type::Boolean => {
                statements_flattened.push(FlatStatement::Condition(
                    variable.into(),
                    FlatExpression::Mult(box variable.into(), box variable.into()),
                ));
            }
            Type::FieldElement => {
                if self.config.allow_unconstrained_variables && parameter.private {
                    // we insert dummy condition statement for private field elements
                    // to avoid unconstrained variables
                    // translates to y == x * x
                    statements_flattened.push(FlatStatement::Condition(
                        self.use_sym().into(),
                        FlatExpression::Mult(box variable.into(), box variable.into()),
                    ));
                }
            }
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::zir::types::Signature;
    use crate::zir::types::Type;
    use zokrates_field::Bn128Field;

    #[test]
    fn assertion_bool_eq() {
        // def main():
        //     bool x = true
        //     bool y = true
        //     assert(x == y)

        // def main():
        //     _0 = 1
        //     _1 = 1
        //     _1 == (_0 * 1)
        let function = ZirFunction::<Bn128Field> {
            arguments: vec![],
            statements: vec![
                ZirStatement::Definition(
                    Variable::boolean("x".into()),
                    BooleanExpression::Value(true).into(),
                ),
                ZirStatement::Definition(
                    Variable::boolean("y".into()),
                    BooleanExpression::Value(true).into(),
                ),
                ZirStatement::Assertion(BooleanExpression::BoolEq(
                    box BooleanExpression::Identifier("x".into()),
                    box BooleanExpression::Identifier("y".into()),
                )),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![],
            },
        };

        let config = CompileConfig::default();
        let mut flattener = Flattener::new(&config);

        let flat = flattener.flatten_function(function);
        let expected = FlatFunction {
            arguments: vec![],
            statements: vec![
                FlatStatement::Definition(
                    FlatVariable::new(0),
                    FlatExpression::Number(Bn128Field::from(1)),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(1),
                    FlatExpression::Number(Bn128Field::from(1)),
                ),
                FlatStatement::Condition(
                    FlatExpression::Identifier(FlatVariable::new(1)),
                    FlatExpression::Mult(
                        box FlatExpression::Identifier(FlatVariable::new(0)),
                        box FlatExpression::Number(Bn128Field::from(1)),
                    ),
                ),
            ],
        };

        assert_eq!(flat, expected);
    }

    #[test]
    fn assertion_field_eq() {
        // def main():
        //     field x = 1
        //     field y = 2
        //     assert(x + 1 == y)

        // def main():
        //     _0 = 42
        //     _1 = 42
        //     _1 == ((_0 + 1) * 1)
        let function = ZirFunction {
            arguments: vec![],
            statements: vec![
                ZirStatement::Definition(
                    Variable::field_element("x"),
                    FieldElementExpression::Number(Bn128Field::from(1)).into(),
                ),
                ZirStatement::Definition(
                    Variable::field_element("y"),
                    FieldElementExpression::Number(Bn128Field::from(2)).into(),
                ),
                ZirStatement::Assertion(BooleanExpression::FieldEq(
                    box FieldElementExpression::Add(
                        box FieldElementExpression::Identifier("x".into()),
                        box FieldElementExpression::Number(Bn128Field::from(1)).into(),
                    ),
                    box FieldElementExpression::Identifier("y".into()),
                )),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![],
            },
        };

        let config = CompileConfig::default();
        let mut flattener = Flattener::new(&config);

        let flat = flattener.flatten_function(function);
        let expected = FlatFunction {
            arguments: vec![],
            statements: vec![
                FlatStatement::Definition(
                    FlatVariable::new(0),
                    FlatExpression::Number(Bn128Field::from(1)),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(1),
                    FlatExpression::Number(Bn128Field::from(2)),
                ),
                FlatStatement::Condition(
                    FlatExpression::Identifier(FlatVariable::new(1)),
                    FlatExpression::Mult(
                        box FlatExpression::Add(
                            box FlatExpression::Identifier(FlatVariable::new(0)),
                            box FlatExpression::Number(Bn128Field::from(1)),
                        ),
                        box FlatExpression::Number(Bn128Field::from(1)),
                    ),
                ),
            ],
        };

        assert_eq!(flat, expected);
    }

    #[test]
    fn assertion_uint_eq() {
        // def main():
        //     u32 x = 42
        //     assert(x == 42)

        // def main():
        //     _0 = 42
        //     42 == (_0 * 1)
        let metadata = UMetadata {
            max: 0xffffffff_u32.into(),
            should_reduce: ShouldReduce::True,
        };
        let function = ZirFunction::<Bn128Field> {
            arguments: vec![],
            statements: vec![
                ZirStatement::Definition(
                    Variable::uint("x".into(), 32),
                    ZirExpression::Uint(
                        UExpressionInner::Value(42)
                            .annotate(32)
                            .metadata(metadata.clone()),
                    ),
                ),
                ZirStatement::Assertion(BooleanExpression::UintEq(
                    box UExpressionInner::Identifier("x".into())
                        .annotate(32)
                        .metadata(metadata.clone()),
                    box UExpressionInner::Value(42).annotate(32).metadata(metadata),
                )),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![],
            },
        };

        let config = CompileConfig::default();
        let mut flattener = Flattener::new(&config);

        let flat = flattener.flatten_function(function);
        let expected = FlatFunction {
            arguments: vec![],
            statements: vec![
                FlatStatement::Definition(
                    FlatVariable::new(0),
                    FlatExpression::Number(Bn128Field::from(42)),
                ),
                FlatStatement::Condition(
                    FlatExpression::Number(Bn128Field::from(42)),
                    FlatExpression::Mult(
                        box FlatExpression::Identifier(FlatVariable::new(0)),
                        box FlatExpression::Number(Bn128Field::from(1)),
                    ),
                ),
            ],
        };

        assert_eq!(flat, expected);
    }

    #[test]
    fn assertion_ident_eq_ident() {
        // def main():
        //     field x = 2
        //     field y = 2
        //     assert(x == y)

        // def main():
        //     _0 = 2
        //     _1 = 2
        //     _1 == (_0 * 1)
        let function = ZirFunction {
            arguments: vec![],
            statements: vec![
                ZirStatement::Definition(
                    Variable::field_element("x"),
                    FieldElementExpression::Number(Bn128Field::from(2)).into(),
                ),
                ZirStatement::Definition(
                    Variable::field_element("y"),
                    FieldElementExpression::Number(Bn128Field::from(2)).into(),
                ),
                ZirStatement::Assertion(BooleanExpression::FieldEq(
                    box FieldElementExpression::Identifier("x".into()),
                    box FieldElementExpression::Identifier("y".into()),
                )),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![],
            },
        };

        let config = CompileConfig::default();
        let mut flattener = Flattener::new(&config);

        let flat = flattener.flatten_function(function);
        let expected = FlatFunction {
            arguments: vec![],
            statements: vec![
                FlatStatement::Definition(
                    FlatVariable::new(0),
                    FlatExpression::Number(Bn128Field::from(2)),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(1),
                    FlatExpression::Number(Bn128Field::from(2)),
                ),
                FlatStatement::Condition(
                    FlatExpression::Identifier(FlatVariable::new(1)),
                    FlatExpression::Mult(
                        box FlatExpression::Identifier(FlatVariable::new(0)),
                        box FlatExpression::Number(Bn128Field::from(1)),
                    ),
                ),
            ],
        };

        assert_eq!(flat, expected);
    }

    #[test]
    fn assertion_mult_eq_ident() {
        // def main():
        //     field x = 2
        //     field y = 2
        //     field z = 4
        //     assert(x * y == z)

        // def main():
        //     _0 = 2
        //     _1 = 2
        //     _2 = 4
        //     _2 == (_0 * _1)
        let function = ZirFunction {
            arguments: vec![],
            statements: vec![
                ZirStatement::Definition(
                    Variable::field_element("x"),
                    FieldElementExpression::Number(Bn128Field::from(2)).into(),
                ),
                ZirStatement::Definition(
                    Variable::field_element("y"),
                    FieldElementExpression::Number(Bn128Field::from(2)).into(),
                ),
                ZirStatement::Definition(
                    Variable::field_element("z"),
                    FieldElementExpression::Number(Bn128Field::from(4)).into(),
                ),
                ZirStatement::Assertion(BooleanExpression::FieldEq(
                    box FieldElementExpression::Mult(
                        box FieldElementExpression::Identifier("x".into()),
                        box FieldElementExpression::Identifier("y".into()),
                    ),
                    box FieldElementExpression::Identifier("z".into()),
                )),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![],
            },
        };

        let config = CompileConfig::default();
        let mut flattener = Flattener::new(&config);

        let flat = flattener.flatten_function(function);
        let expected = FlatFunction {
            arguments: vec![],
            statements: vec![
                FlatStatement::Definition(
                    FlatVariable::new(0),
                    FlatExpression::Number(Bn128Field::from(2)),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(1),
                    FlatExpression::Number(Bn128Field::from(2)),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(2),
                    FlatExpression::Number(Bn128Field::from(4)),
                ),
                FlatStatement::Condition(
                    FlatExpression::Identifier(FlatVariable::new(2)),
                    FlatExpression::Mult(
                        box FlatExpression::Identifier(FlatVariable::new(0)),
                        box FlatExpression::Identifier(FlatVariable::new(1)),
                    ),
                ),
            ],
        };

        assert_eq!(flat, expected);
    }

    #[test]
    fn assertion_ident_eq_mult() {
        // def main():
        //     field x = 2
        //     field y = 2
        //     field z = 4
        //     assert(z == x * y)

        // def main():
        //     _0 = 2
        //     _1 = 2
        //     _2 = 4
        //     _2 == (_0 * _1)
        let function = ZirFunction {
            arguments: vec![],
            statements: vec![
                ZirStatement::Definition(
                    Variable::field_element("x"),
                    FieldElementExpression::Number(Bn128Field::from(2)).into(),
                ),
                ZirStatement::Definition(
                    Variable::field_element("y"),
                    FieldElementExpression::Number(Bn128Field::from(2)).into(),
                ),
                ZirStatement::Definition(
                    Variable::field_element("z"),
                    FieldElementExpression::Number(Bn128Field::from(4)).into(),
                ),
                ZirStatement::Assertion(BooleanExpression::FieldEq(
                    box FieldElementExpression::Identifier("z".into()),
                    box FieldElementExpression::Mult(
                        box FieldElementExpression::Identifier("x".into()),
                        box FieldElementExpression::Identifier("y".into()),
                    ),
                )),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![],
            },
        };

        let config = CompileConfig::default();
        let mut flattener = Flattener::new(&config);

        let flat = flattener.flatten_function(function);
        let expected = FlatFunction {
            arguments: vec![],
            statements: vec![
                FlatStatement::Definition(
                    FlatVariable::new(0),
                    FlatExpression::Number(Bn128Field::from(2)),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(1),
                    FlatExpression::Number(Bn128Field::from(2)),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(2),
                    FlatExpression::Number(Bn128Field::from(4)),
                ),
                FlatStatement::Condition(
                    FlatExpression::Identifier(FlatVariable::new(2)),
                    FlatExpression::Mult(
                        box FlatExpression::Identifier(FlatVariable::new(0)),
                        box FlatExpression::Identifier(FlatVariable::new(1)),
                    ),
                ),
            ],
        };

        assert_eq!(flat, expected);
    }

    #[test]
    fn assertion_mult_eq_mult() {
        // def main():
        //     field x = 4
        //     field y = 4
        //     field z = 8
        //     field t = 2
        //     assert(x * y == z * t)

        // def main():
        //     _0 = 4
        //     _1 = 4
        //     _2 = 8
        //     _3 = 2
        //     _4 = (_2 * _3)
        //     _4 == (_0 * _1)
        let function = ZirFunction {
            arguments: vec![],
            statements: vec![
                ZirStatement::Definition(
                    Variable::field_element("x"),
                    FieldElementExpression::Number(Bn128Field::from(4)).into(),
                ),
                ZirStatement::Definition(
                    Variable::field_element("y"),
                    FieldElementExpression::Number(Bn128Field::from(4)).into(),
                ),
                ZirStatement::Definition(
                    Variable::field_element("z"),
                    FieldElementExpression::Number(Bn128Field::from(8)).into(),
                ),
                ZirStatement::Definition(
                    Variable::field_element("t"),
                    FieldElementExpression::Number(Bn128Field::from(2)).into(),
                ),
                ZirStatement::Assertion(BooleanExpression::FieldEq(
                    box FieldElementExpression::Mult(
                        box FieldElementExpression::Identifier("x".into()),
                        box FieldElementExpression::Identifier("y".into()),
                    ),
                    box FieldElementExpression::Mult(
                        box FieldElementExpression::Identifier("z".into()),
                        box FieldElementExpression::Identifier("t".into()),
                    ),
                )),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![],
            },
        };

        let config = CompileConfig::default();
        let mut flattener = Flattener::new(&config);

        let flat = flattener.flatten_function(function);
        let expected = FlatFunction {
            arguments: vec![],
            statements: vec![
                FlatStatement::Definition(
                    FlatVariable::new(0),
                    FlatExpression::Number(Bn128Field::from(4)),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(1),
                    FlatExpression::Number(Bn128Field::from(4)),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(2),
                    FlatExpression::Number(Bn128Field::from(8)),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(3),
                    FlatExpression::Number(Bn128Field::from(2)),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(4),
                    FlatExpression::Mult(
                        box FlatExpression::Identifier(FlatVariable::new(2)),
                        box FlatExpression::Identifier(FlatVariable::new(3)),
                    ),
                ),
                FlatStatement::Condition(
                    FlatExpression::Identifier(FlatVariable::new(4)),
                    FlatExpression::Mult(
                        box FlatExpression::Identifier(FlatVariable::new(0)),
                        box FlatExpression::Identifier(FlatVariable::new(1)),
                    ),
                ),
            ],
        };

        assert_eq!(flat, expected);
    }

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
                        box 0u32.into(),
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

        let config = CompileConfig::default();
        let mut flattener = Flattener::new(&config);

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

        let flattened = flattener.flatten_function(function);

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
                        box 1u32.into(),
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

        let config = CompileConfig::default();
        let mut flattener = Flattener::new(&config);

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
                FlatStatement::Return(FlatExpressionList {
                    expressions: vec![FlatExpression::Identifier(FlatVariable::new(1))],
                }),
            ],
        };

        let flattened = flattener.flatten_function(function);

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
        //     return _6

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
                        box 13u32.into(),
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

        let config = CompileConfig::default();
        let mut flattener = Flattener::new(&config);

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
                FlatStatement::Return(FlatExpressionList {
                    expressions: vec![FlatExpression::Identifier(FlatVariable::new(6))],
                }),
            ],
        };

        let flattened = flattener.flatten_function(function);

        assert_eq!(flattened, expected);
    }

    #[test]
    fn if_else() {
        let config = CompileConfig::default();
        let expression = FieldElementExpression::IfElse(
            box BooleanExpression::FieldEq(
                box FieldElementExpression::Number(Bn128Field::from(32)),
                box FieldElementExpression::Number(Bn128Field::from(4)),
            ),
            box FieldElementExpression::Number(Bn128Field::from(12)),
            box FieldElementExpression::Number(Bn128Field::from(51)),
        );

        let mut flattener = Flattener::new(&config);

        flattener.flatten_field_expression(&mut FlatStatements::new(), expression);
    }

    #[test]
    fn geq_leq() {
        let config = CompileConfig::default();
        let mut flattener = Flattener::new(&config);
        let expression_le = BooleanExpression::FieldLe(
            box FieldElementExpression::Number(Bn128Field::from(32)),
            box FieldElementExpression::Number(Bn128Field::from(4)),
        );
        flattener.flatten_boolean_expression(&mut FlatStatements::new(), expression_le);

        let mut flattener = Flattener::new(&config);
        let expression_ge = BooleanExpression::FieldGe(
            box FieldElementExpression::Number(Bn128Field::from(32)),
            box FieldElementExpression::Number(Bn128Field::from(4)),
        );
        flattener.flatten_boolean_expression(&mut FlatStatements::new(), expression_ge);
    }

    #[test]
    fn bool_and() {
        let config = CompileConfig::default();
        let mut flattener = Flattener::new(&config);

        let expression = FieldElementExpression::IfElse(
            box BooleanExpression::And(
                box BooleanExpression::FieldEq(
                    box FieldElementExpression::Number(Bn128Field::from(4)),
                    box FieldElementExpression::Number(Bn128Field::from(4)),
                ),
                box BooleanExpression::FieldLt(
                    box FieldElementExpression::Number(Bn128Field::from(4)),
                    box FieldElementExpression::Number(Bn128Field::from(20)),
                ),
            ),
            box FieldElementExpression::Number(Bn128Field::from(12)),
            box FieldElementExpression::Number(Bn128Field::from(51)),
        );

        flattener.flatten_field_expression(&mut FlatStatements::new(), expression);
    }

    #[test]
    fn div() {
        // a = 5 / b / b
        let config = CompileConfig::default();
        let mut flattener = Flattener::new(&config);
        let mut statements_flattened = FlatStatements::new();

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

        flattener.flatten_statement(&mut statements_flattened, definition);

        flattener.flatten_statement(&mut statements_flattened, statement);

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
            ]
        );
    }
}
