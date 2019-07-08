//! Module containing the `Flattener` to process a program that it is R1CS-able.
//!
//! @file flatten.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

use crate::flat_absy::*;
use crate::helpers::{DirectiveStatement, Helper, RustHelper};
use crate::typed_absy::*;
use crate::types::conversions::cast;
use crate::types::Signature;
use crate::types::Type;
use std::collections::HashMap;
use zokrates_field::Field;

/// Flattener, computes flattened program.
#[derive(Debug)]
pub struct Flattener<'ast> {
    /// Index of the next introduced variable while processing the program.
    next_var_idx: usize,
    ///
    layout: HashMap<Identifier<'ast>, Vec<FlatVariable>>,
}
impl<'ast> Flattener<'ast> {
    pub fn flatten<T: Field>(p: TypedProg<T>) -> FlatProg<T> {
        Flattener::new().flatten_program(p)
    }

    /// Returns a `Flattener` with fresh a fresh [substitution] and [variables].
    ///
    /// # Arguments
    ///
    /// * `bits` - Number of bits needed to represent the maximum value.

    fn new() -> Flattener<'ast> {
        Flattener {
            next_var_idx: 0,
            layout: HashMap::new(),
        }
    }

    /// Loads the code library
    fn load_corelib<T: Field>(&mut self, functions_flattened: &mut Vec<FlatFunction<T>>) -> () {
        // Load type casting functions
        functions_flattened.push(cast(&Type::Boolean, &Type::FieldElement));

        // Load IfElse helper
        let ie = TypedFunction {
            id: "_if_else_field",
            arguments: vec![
                Parameter {
                    id: Variable {
                        id: "condition".into(),
                        _type: Type::Boolean,
                    },
                    private: true,
                },
                Parameter {
                    id: Variable {
                        id: "consequence".into(),
                        _type: Type::FieldElement,
                    },
                    private: true,
                },
                Parameter {
                    id: Variable {
                        id: "alternative".into(),
                        _type: Type::FieldElement,
                    },
                    private: true,
                },
            ],
            statements: vec![
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("condition_as_field".into())),
                    FieldElementExpression::FunctionCall(
                        "_bool_to_field".to_string(),
                        vec![BooleanExpression::Identifier("condition".into()).into()],
                    )
                    .into(),
                ),
                TypedStatement::Return(vec![FieldElementExpression::Add(
                    box FieldElementExpression::Mult(
                        box FieldElementExpression::Identifier("condition_as_field".into()),
                        box FieldElementExpression::Identifier("consequence".into()),
                    ),
                    box FieldElementExpression::Mult(
                        box FieldElementExpression::Sub(
                            box FieldElementExpression::Number(T::one()),
                            box FieldElementExpression::Identifier("condition_as_field".into()),
                        ),
                        box FieldElementExpression::Identifier("alternative".into()),
                    ),
                )
                .into()]),
            ],
            signature: Signature::new()
                .inputs(vec![Type::Boolean, Type::FieldElement, Type::FieldElement])
                .outputs(vec![Type::FieldElement]),
        };

        let ief = self.flatten_function(functions_flattened, ie);
        functions_flattened.push(ief);
    }

    /// Flattens a boolean expression
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `condition` - `Condition` that will be flattened.
    ///
    /// # Postconditions
    ///
    /// * `flatten_boolean_expressions` always returns a linear expression,
    /// * in order to preserve composability.
    fn flatten_boolean_expression<T: Field>(
        &mut self,
        functions_flattened: &Vec<FlatFunction<T>>,
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
                    self.flatten_field_expression(functions_flattened, statements_flattened, lhs);
                let rhs_flattened =
                    self.flatten_field_expression(functions_flattened, statements_flattened, rhs);

                // lhs
                let lhs_id = self.use_sym();
                statements_flattened.push(FlatStatement::Definition(lhs_id, lhs_flattened));

                // check that lhs and rhs are within the right range, ie, their last two bits are zero

                // lhs
                {
                    // define variables for the bits
                    let lhs_bits: Vec<FlatVariable> =
                        (0..bitwidth).map(|_| self.use_sym()).collect();

                    // add a directive to get the bits
                    statements_flattened.push(FlatStatement::Directive(DirectiveStatement::new(
                        lhs_bits.clone(),
                        Helper::bits(),
                        vec![lhs_id],
                    )));

                    // bitness checks
                    for i in 0..bitwidth - 2 {
                        statements_flattened.push(FlatStatement::Condition(
                            FlatExpression::Identifier(lhs_bits[i + 2]),
                            FlatExpression::Mult(
                                box FlatExpression::Identifier(lhs_bits[i + 2]),
                                box FlatExpression::Identifier(lhs_bits[i + 2]),
                            ),
                        ));
                    }

                    // bit decomposition check
                    let mut lhs_sum = FlatExpression::Number(T::from(0));

                    for i in 0..bitwidth - 2 {
                        lhs_sum = FlatExpression::Add(
                            box lhs_sum,
                            box FlatExpression::Mult(
                                box FlatExpression::Identifier(lhs_bits[i + 2]),
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
                    let rhs_bits: Vec<FlatVariable> =
                        (0..bitwidth).map(|_| self.use_sym()).collect();

                    // add a directive to get the bits
                    statements_flattened.push(FlatStatement::Directive(DirectiveStatement::new(
                        rhs_bits.clone(),
                        Helper::bits(),
                        vec![rhs_id],
                    )));

                    // bitness checks
                    for i in 0..bitwidth - 2 {
                        statements_flattened.push(FlatStatement::Condition(
                            FlatExpression::Identifier(rhs_bits[i + 2]),
                            FlatExpression::Mult(
                                box FlatExpression::Identifier(rhs_bits[i + 2]),
                                box FlatExpression::Identifier(rhs_bits[i + 2]),
                            ),
                        ));
                    }

                    // bit decomposition check
                    let mut rhs_sum = FlatExpression::Number(T::from(0));

                    for i in 0..bitwidth - 2 {
                        rhs_sum = FlatExpression::Add(
                            box rhs_sum,
                            box FlatExpression::Mult(
                                box FlatExpression::Identifier(rhs_bits[i + 2]),
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
                let sub_bits: Vec<FlatVariable> = (0..bitwidth).map(|_| self.use_sym()).collect();

                // add a directive to get the bits
                statements_flattened.push(FlatStatement::Directive(DirectiveStatement::new(
                    sub_bits.clone(),
                    Helper::bits(),
                    vec![subtraction_result.clone()],
                )));

                // bitness checks
                for i in 0..bitwidth {
                    statements_flattened.push(FlatStatement::Condition(
                        FlatExpression::Identifier(sub_bits[i]),
                        FlatExpression::Mult(
                            box FlatExpression::Identifier(sub_bits[i]),
                            box FlatExpression::Identifier(sub_bits[i]),
                        ),
                    ));
                }

                // sum(sym_b{i} * 2**i)
                let mut expr = FlatExpression::Number(T::from(0));

                for i in 0..bitwidth {
                    expr = FlatExpression::Add(
                        box expr,
                        box FlatExpression::Mult(
                            box FlatExpression::Identifier(sub_bits[i]),
                            box FlatExpression::Number(T::from(2).pow(bitwidth - i - 1)),
                        ),
                    );
                }

                statements_flattened.push(FlatStatement::Condition(subtraction_result, expr));

                FlatExpression::Identifier(sub_bits[0])
            }
            BooleanExpression::Eq(box lhs, box rhs) => {
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
                    functions_flattened,
                    statements_flattened,
                    FieldElementExpression::Sub(box lhs, box rhs),
                );

                statements_flattened.push(FlatStatement::Directive(DirectiveStatement::new(
                    vec![name_y, name_m],
                    Helper::Rust(RustHelper::ConditionEq),
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
                    functions_flattened,
                    statements_flattened,
                    BooleanExpression::Lt(box lhs.clone(), box rhs.clone()),
                );
                let eq = self.flatten_boolean_expression(
                    functions_flattened,
                    statements_flattened,
                    BooleanExpression::Eq(box lhs.clone(), box rhs.clone()),
                );
                FlatExpression::Add(box eq, box lt)
            }
            BooleanExpression::Gt(lhs, rhs) => self.flatten_boolean_expression(
                functions_flattened,
                statements_flattened,
                BooleanExpression::Lt(rhs, lhs),
            ),
            BooleanExpression::Ge(lhs, rhs) => self.flatten_boolean_expression(
                functions_flattened,
                statements_flattened,
                BooleanExpression::Le(rhs, lhs),
            ),
            BooleanExpression::Or(box lhs, box rhs) => {
                let x = box self.flatten_boolean_expression(
                    functions_flattened,
                    statements_flattened,
                    lhs,
                );
                let y = box self.flatten_boolean_expression(
                    functions_flattened,
                    statements_flattened,
                    rhs,
                );
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
                let x =
                    self.flatten_boolean_expression(functions_flattened, statements_flattened, lhs);
                let y =
                    self.flatten_boolean_expression(functions_flattened, statements_flattened, rhs);

                let name_x_and_y = self.use_sym();
                assert!(x.is_linear() && y.is_linear());
                statements_flattened.push(FlatStatement::Definition(
                    name_x_and_y,
                    FlatExpression::Mult(box x, box y),
                ));

                FlatExpression::Identifier(name_x_and_y)
            }
            BooleanExpression::Not(box exp) => {
                let x =
                    self.flatten_boolean_expression(functions_flattened, statements_flattened, exp);
                FlatExpression::Sub(box FlatExpression::Number(T::one()), box x)
            }
            BooleanExpression::Value(b) => FlatExpression::Number(match b {
                true => T::from(1),
                false => T::from(0),
            }),
        }
    }

    fn flatten_function_call<T: Field>(
        &mut self,
        functions_flattened: &Vec<FlatFunction<T>>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        id: &String,
        return_types: Vec<Type>,
        param_expressions: &Vec<TypedExpression<'ast, T>>,
    ) -> FlatExpressionList<T> {
        let passed_signature = Signature::new()
            .inputs(param_expressions.iter().map(|e| e.get_type()).collect())
            .outputs(return_types);

        let funct = self
            .get_function(passed_signature, &functions_flattened, id)
            .clone();

        let mut replacement_map = HashMap::new();

        // Handle complex parameters and assign values:
        // Rename Parameters, assign them to values in call. Resolve complex expressions with definitions
        let params_flattened = param_expressions
            .into_iter()
            .map(|param_expr| {
                self.flatten_expression(
                    functions_flattened,
                    statements_flattened,
                    param_expr.clone(),
                )
            })
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

        // Ensure Renaming and correct returns:
        // add all flattened statements, adapt return statement

        let (return_statements, statements): (Vec<_>, Vec<_>) =
            funct.statements.into_iter().partition(|s| match s {
                FlatStatement::Return(..) => true,
                _ => false,
            });

        let statements: Vec<_> = statements
            .into_iter()
            .map(|stat| match stat {
                // set return statements right sidreturne as expression result
                FlatStatement::Return(..) => unreachable!(),
                FlatStatement::Definition(var, rhs) => {
                    let new_var = self.issue_new_variables(1)[0];
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
                            let new_o = self.issue_new_variables(1)[0];
                            replacement_map.insert(o, new_o);
                            new_o
                        })
                        .collect();
                    let new_inputs = d
                        .inputs
                        .into_iter()
                        .map(|i| i.apply_substitution(&replacement_map))
                        .collect();
                    FlatStatement::Directive(DirectiveStatement {
                        outputs: new_outputs,
                        helper: d.helper,
                        inputs: new_inputs,
                    })
                }
            })
            .collect();

        statements_flattened.extend(statements);

        match return_statements[0].clone() {
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

    fn flatten_expression<T: Field>(
        &mut self,
        functions_flattened: &Vec<FlatFunction<T>>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        expr: TypedExpression<'ast, T>,
    ) -> Vec<FlatExpression<T>> {
        match expr {
            TypedExpression::FieldElement(e) => {
                vec![self.flatten_field_expression(functions_flattened, statements_flattened, e)]
            }
            TypedExpression::Boolean(e) => {
                vec![self.flatten_boolean_expression(functions_flattened, statements_flattened, e)]
            }
            TypedExpression::FieldElementArray(e) => {
                self.flatten_field_array_expression(functions_flattened, statements_flattened, e)
            }
        }
    }

    fn flatten_field_expression<T: Field>(
        &mut self,
        functions_flattened: &Vec<FlatFunction<T>>,
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
                    self.flatten_field_expression(functions_flattened, statements_flattened, left);
                let right_flattened =
                    self.flatten_field_expression(functions_flattened, statements_flattened, right);
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
                    self.flatten_field_expression(functions_flattened, statements_flattened, left);
                let right_flattened =
                    self.flatten_field_expression(functions_flattened, statements_flattened, right);

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
                    self.flatten_field_expression(functions_flattened, statements_flattened, left);
                let right_flattened =
                    self.flatten_field_expression(functions_flattened, statements_flattened, right);
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
                    self.flatten_field_expression(functions_flattened, statements_flattened, left);
                let right_flattened =
                    self.flatten_field_expression(functions_flattened, statements_flattened, right);
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
                statements_flattened.push(FlatStatement::Directive(DirectiveStatement::new(
                    vec![invb],
                    Helper::Rust(RustHelper::Div),
                    vec![FlatExpression::Number(T::one()), new_right.clone()],
                )));

                // assert(invb * b == 1)
                statements_flattened.push(FlatStatement::Condition(
                    FlatExpression::Number(T::one()),
                    FlatExpression::Mult(box invb.into(), box new_right.clone().into()),
                ));

                // # c = a/b
                statements_flattened.push(FlatStatement::Directive(DirectiveStatement::new(
                    vec![inverse],
                    Helper::Rust(RustHelper::Div),
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
                            functions_flattened,
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
                            .into_iter()
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
                            FlatExpression::Number(T::from(1)), // initialise the result at 1. If we have no bits to iterate through, we're computing x**0 == 1
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
            FieldElementExpression::IfElse(box condition, box consequent, box alternative) => self
                .flatten_function_call(
                    functions_flattened,
                    statements_flattened,
                    &"_if_else_field".to_string(),
                    vec![Type::FieldElement],
                    &vec![condition.into(), consequent.into(), alternative.into()],
                )
                .expressions[0]
                .clone(),
            FieldElementExpression::FunctionCall(ref id, ref param_expressions) => {
                let exprs_flattened = self.flatten_function_call(
                    functions_flattened,
                    statements_flattened,
                    id,
                    vec![Type::FieldElement],
                    param_expressions,
                );
                assert!(exprs_flattened.expressions.len() == 1); // outside of MultipleDefinition, FunctionCalls must return a single value
                exprs_flattened.expressions[0].clone()
            }
            FieldElementExpression::Select(box array, box index) => {
                match index {
                    FieldElementExpression::Number(n) => match array {
                        FieldElementArrayExpression::Identifier(size, id) => {
                            assert!(n < T::from(size));
                            FlatExpression::Identifier(
                                self.layout.get(&id).unwrap().clone()
                                    [n.to_dec_string().parse::<usize>().unwrap()],
                            )
                        }
                        FieldElementArrayExpression::Value(size, expressions) => {
                            assert!(n < T::from(size));
                            self.flatten_field_expression(
                                functions_flattened,
                                statements_flattened,
                                expressions[n.to_dec_string().parse::<usize>().unwrap()].clone(),
                            )
                        }
                        FieldElementArrayExpression::FunctionCall(..) => {
                            unimplemented!("please use intermediate variables for now")
                        }
                        FieldElementArrayExpression::IfElse(
                            condition,
                            consequence,
                            alternative,
                        ) => {
                            // [if cond then [a, b] else [c, d]][1] == if cond then [a, b][1] else [c, d][1]
                            self.flatten_field_expression(
                                functions_flattened,
                                statements_flattened,
                                FieldElementExpression::IfElse(
                                    condition,
                                    box FieldElementExpression::Select(
                                        consequence,
                                        box FieldElementExpression::Number(n.clone()),
                                    ),
                                    box FieldElementExpression::Select(
                                        alternative,
                                        box FieldElementExpression::Number(n),
                                    ),
                                ),
                            )
                        }
                    },
                    e => {
                        let size = array.size();
                        // we have array[e] with e an arbitrary expression
                        // first we check that e is in 0..array.len(), so we check that sum(if e == i then 1 else 0) == 1
                        // here depending on the size, we could use a proper range check based on bits
                        let range_check = (0..size)
                            .map(|i| {
                                FieldElementExpression::IfElse(
                                    box BooleanExpression::Eq(
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

                        self.flatten_statement(
                            functions_flattened,
                            statements_flattened,
                            range_check_statement,
                        );

                        // now we flatten to sum(if e == i then array[i] else 0)
                        let lookup = (0..size)
                            .map(|i| {
                                FieldElementExpression::IfElse(
                                    box BooleanExpression::Eq(
                                        box e.clone(),
                                        box FieldElementExpression::Number(T::from(i)),
                                    ),
                                    box match array.clone() {
                                        FieldElementArrayExpression::Identifier(size, id) => {
                                            FieldElementExpression::Select(
                                                box FieldElementArrayExpression::Identifier(
                                                    size, id,
                                                ),
                                                box FieldElementExpression::Number(T::from(i)),
                                            )
                                        }
                                        FieldElementArrayExpression::Value(size, expressions) => {
                                            assert_eq!(size, expressions.len());
                                            expressions[i].clone()
                                        }
                                        FieldElementArrayExpression::FunctionCall(..) => {
                                            unimplemented!(
                                                "please use intermediate variables for now"
                                            )
                                        }
                                        FieldElementArrayExpression::IfElse(
                                            condition,
                                            consequence,
                                            alternative,
                                        ) => FieldElementExpression::IfElse(
                                            condition,
                                            box FieldElementExpression::Select(
                                                consequence,
                                                box FieldElementExpression::Number(T::from(i)),
                                            ),
                                            box FieldElementExpression::Select(
                                                alternative,
                                                box FieldElementExpression::Number(T::from(i)),
                                            ),
                                        ),
                                    },
                                    box FieldElementExpression::Number(T::from(0)),
                                )
                            })
                            .fold(FieldElementExpression::Number(T::from(0)), |acc, e| {
                                FieldElementExpression::Add(box acc, box e)
                            });

                        self.flatten_field_expression(
                            functions_flattened,
                            statements_flattened,
                            lookup,
                        )
                    }
                }
            }
        }
    }

    fn flatten_field_array_expression<T: Field>(
        &mut self,
        functions_flattened: &Vec<FlatFunction<T>>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        expr: FieldElementArrayExpression<'ast, T>,
    ) -> Vec<FlatExpression<T>> {
        match expr {
            FieldElementArrayExpression::Identifier(_, x) => self
                .layout
                .get(&x)
                .unwrap()
                .iter()
                .map(|v| FlatExpression::Identifier(v.clone()))
                .collect(),
            FieldElementArrayExpression::Value(size, values) => {
                assert_eq!(size, values.len());
                values
                    .into_iter()
                    .map(|v| {
                        self.flatten_field_expression(functions_flattened, statements_flattened, v)
                    })
                    .collect()
            }
            FieldElementArrayExpression::FunctionCall(size, ref id, ref param_expressions) => {
                let exprs_flattened = self.flatten_function_call(
                    functions_flattened,
                    statements_flattened,
                    id,
                    vec![Type::FieldElementArray(size)],
                    param_expressions,
                );
                assert!(exprs_flattened.expressions.len() == size); // outside of MultipleDefinition, FunctionCalls must return a single value
                exprs_flattened.expressions
            }
            FieldElementArrayExpression::IfElse(
                ref condition,
                ref consequence,
                ref alternative,
            ) => {
                let size = match consequence.get_type() {
                    Type::FieldElementArray(n) => n,
                    _ => unreachable!(),
                };
                (0..size)
                    .map(|i| {
                        self.flatten_field_expression(
                            functions_flattened,
                            statements_flattened,
                            FieldElementExpression::IfElse(
                                condition.clone(),
                                box FieldElementExpression::Select(
                                    consequence.clone(),
                                    box FieldElementExpression::Number(T::from(i)),
                                ),
                                box FieldElementExpression::Select(
                                    alternative.clone(),
                                    box FieldElementExpression::Number(T::from(i)),
                                ),
                            ),
                        )
                    })
                    .collect()
            }
        }
    }

    fn flatten_statement<T: Field>(
        &mut self,
        functions_flattened: &Vec<FlatFunction<T>>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        stat: TypedStatement<'ast, T>,
    ) {
        match stat {
            TypedStatement::Return(exprs) => {
                let flat_expressions = exprs
                    .into_iter()
                    .map(|expr| {
                        self.flatten_expression(functions_flattened, statements_flattened, expr)
                    })
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

                let rhs = self.flatten_expression(
                    functions_flattened,
                    statements_flattened,
                    expr.clone(),
                );

                match expr.get_type() {
                    Type::FieldElement | Type::Boolean => {
                        match assignee {
                            TypedAssignee::Identifier(ref v) => {
                                let var = self.use_variable(&v)[0];
                                // handle return of function call
                                statements_flattened
                                    .push(FlatStatement::Definition(var, rhs[0].clone()));
                            }
                            TypedAssignee::ArrayElement(box array, box index) => {
                                let expr = match expr {
                                    TypedExpression::FieldElement(e) => e,
                                    _ => panic!("not a field element as rhs of array element update, should have been caught at semantic")
                                };
                                match index {
                                    FieldElementExpression::Number(n) => match array {
                                        TypedAssignee::Identifier(id) => {
                                            let var = self.issue_new_variables(1);
                                            let variables = self.layout.get_mut(&id.id).unwrap();
                                            variables
                                                [n.to_dec_string().parse::<usize>().unwrap()] =
                                                var[0];
                                            statements_flattened.push(FlatStatement::Definition(
                                                var[0],
                                                rhs[0].clone(),
                                            ));
                                        }
                                        _ => panic!("no multidimension array for now"),
                                    },
                                    e => {
                                        // we have array[e] with e an arbitrary expression
                                        // first we check that e is in 0..array.len(), so we check that sum(if e == i then 1 else 0) == 1
                                        // here depending on the size, we could use a proper range check based on bits
                                        let size = match array.get_type() {
                                            Type::FieldElementArray(n) => n,
                                            _ => panic!("checker should generate array element based on non array")
                                        };
                                        let range_check = (0..size)
                                            .map(|i| {
                                                FieldElementExpression::IfElse(
                                                    box BooleanExpression::Eq(
                                                        box e.clone(),
                                                        box FieldElementExpression::Number(
                                                            T::from(i),
                                                        ),
                                                    ),
                                                    box FieldElementExpression::Number(T::from(1)),
                                                    box FieldElementExpression::Number(T::from(0)),
                                                )
                                            })
                                            .fold(
                                                FieldElementExpression::Number(T::from(0)),
                                                |acc, e| {
                                                    FieldElementExpression::Add(box acc, box e)
                                                },
                                            );

                                        let range_check_statement = TypedStatement::Condition(
                                            FieldElementExpression::Number(T::from(1)).into(),
                                            range_check.into(),
                                        );

                                        self.flatten_statement(
                                            functions_flattened,
                                            statements_flattened,
                                            range_check_statement,
                                        );

                                        // now we redefine the whole array, updating only the piece that changed
                                        // stat(array[i] = if e == i then `expr` else `array[i]`)
                                        let vars = match array {
                                            TypedAssignee::Identifier(v) => self.use_variable(&v),
                                            _ => unimplemented!(),
                                        };

                                        let statements = vars
                                            .into_iter()
                                            .enumerate()
                                            .map(|(i, v)| {
                                                let rhs = FieldElementExpression::IfElse(
                                                    box BooleanExpression::Eq(
                                                        box e.clone(),
                                                        box FieldElementExpression::Number(
                                                            T::from(i),
                                                        ),
                                                    ),
                                                    box expr.clone(),
                                                    box e.clone(),
                                                );

                                                let rhs_flattened = self.flatten_field_expression(
                                                    functions_flattened,
                                                    statements_flattened,
                                                    rhs,
                                                );

                                                FlatStatement::Definition(v, rhs_flattened)
                                            })
                                            .collect::<Vec<_>>();

                                        statements_flattened.extend(statements);
                                    }
                                }
                            }
                        }
                    }
                    Type::FieldElementArray(..) => {
                        let vars = match assignee {
                            TypedAssignee::Identifier(v) => self.use_variable(&v),
                            _ => unimplemented!(),
                        };
                        statements_flattened.extend(
                            vars.into_iter()
                                .zip(rhs.into_iter())
                                .map(|(v, r)| FlatStatement::Definition(v, r)),
                        );
                    }
                }
            }
            TypedStatement::Condition(expr1, expr2) => {
                // flatten expr1 and expr2 to n flattened expressions with n the number of primitive types for expr1
                // add n conditions to check equality of the n expressions

                match (expr1, expr2) {
                    (TypedExpression::FieldElement(e1), TypedExpression::FieldElement(e2)) => {
                        let (lhs, rhs) = (
                            self.flatten_field_expression(
                                functions_flattened,
                                statements_flattened,
                                e1,
                            ),
                            self.flatten_field_expression(
                                functions_flattened,
                                statements_flattened,
                                e2,
                            ),
                        );

                        if lhs.is_linear() {
                            statements_flattened.push(FlatStatement::Condition(lhs, rhs));
                        } else if rhs.is_linear() {
                            // swap so that left side is linear
                            statements_flattened.push(FlatStatement::Condition(rhs, lhs));
                        } else {
                            unimplemented!()
                        }
                    }
                    (TypedExpression::Boolean(e1), TypedExpression::Boolean(e2)) => {
                        let (lhs, rhs) = (
                            self.flatten_boolean_expression(
                                functions_flattened,
                                statements_flattened,
                                e1,
                            ),
                            self.flatten_boolean_expression(
                                functions_flattened,
                                statements_flattened,
                                e2,
                            ),
                        );

                        if lhs.is_linear() {
                            statements_flattened.push(FlatStatement::Condition(lhs, rhs));
                        } else if rhs.is_linear() {
                            // swap so that left side is linear
                            statements_flattened.push(FlatStatement::Condition(rhs, lhs));
                        } else {
                            unimplemented!()
                        }
                    }
                    (
                        TypedExpression::FieldElementArray(e1),
                        TypedExpression::FieldElementArray(e2),
                    ) => {
                        let (lhs, rhs) = (
                            self.flatten_field_array_expression(
                                functions_flattened,
                                statements_flattened,
                                e1,
                            ),
                            self.flatten_field_array_expression(
                                functions_flattened,
                                statements_flattened,
                                e2,
                            ),
                        );

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
                    _ => panic!(
                        "non matching types in condition should have been caught at semantic stage"
                    ),
                }
            }
            TypedStatement::For(var, start, end, statements) => {
                let mut current = start;
                while current < end {
                    statements_flattened.push(FlatStatement::Definition(
                        self.use_variable(&var)[0],
                        FlatExpression::Number(current.clone()),
                    ));
                    for s in statements.clone() {
                        self.flatten_statement(functions_flattened, statements_flattened, s);
                    }
                    current = T::one() + &current;
                }
            }
            TypedStatement::MultipleDefinition(vars, rhs) => {
                // flatten the right side to p = sum(var_i.type.primitive_count) expressions
                // define p new variables to the right side expressions

                let var_types = vars.iter().map(|v| v.get_type()).collect();

                match rhs {
                    TypedExpressionList::FunctionCall(fun_id, exprs, _) => {
                        let rhs_flattened = self.flatten_function_call(
                            functions_flattened,
                            statements_flattened,
                            &fun_id,
                            var_types,
                            &exprs,
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

    /// Returns a flattened `TypedFunction` based on the given `funct`.
    ///
    /// # Arguments
    ///
    /// * `functions_flattened` - Vector where new flattened functions can be added.
    /// * `funct` - `TypedFunction` that will be flattened.
    fn flatten_function<T: Field>(
        &mut self,
        functions_flattened: &mut Vec<FlatFunction<T>>,
        funct: TypedFunction<'ast, T>,
    ) -> FlatFunction<T> {
        self.layout = HashMap::new();

        self.next_var_idx = 0;
        let mut statements_flattened: Vec<FlatStatement<T>> = Vec::new();

        // push parameters
        let arguments_flattened = funct
            .arguments
            .into_iter()
            .flat_map(|p| self.use_parameter(&p, &mut statements_flattened))
            .collect();

        // flatten statements in functions and apply substitution
        for stat in funct.statements {
            self.flatten_statement(functions_flattened, &mut statements_flattened, stat);
        }

        FlatFunction {
            id: funct.id.to_string(),
            arguments: arguments_flattened,
            statements: statements_flattened,
            signature: funct.signature,
        }
    }

    /// Returns a flattened `Prog`ram based on the given `prog`.
    ///
    /// # Arguments
    ///
    /// * `prog` - `Prog`ram that will be flattened.
    fn flatten_program<T: Field>(&mut self, prog: TypedProg<'ast, T>) -> FlatProg<T> {
        let mut functions_flattened = Vec::new();

        self.load_corelib(&mut functions_flattened);

        for func in prog.imported_functions {
            functions_flattened.push(func);
        }

        for func in prog.functions {
            let flattened_func = self.flatten_function(&mut functions_flattened, func);
            functions_flattened.push(flattened_func);
        }

        FlatProg {
            functions: functions_flattened,
        }
    }

    /// Checks if the given name is a not used variable and returns a fresh variable.
    /// # Arguments
    ///
    /// * `name` - a String that holds the name of the variable
    fn use_variable(&mut self, variable: &Variable<'ast>) -> Vec<FlatVariable> {
        let vars = match variable.get_type() {
            Type::FieldElement => self.issue_new_variables(1),
            Type::Boolean => self.issue_new_variables(1),
            Type::FieldElementArray(size) => self.issue_new_variables(size),
        };

        self.layout.insert(variable.id.clone(), vars.clone());
        vars
    }

    fn use_parameter<T: Field>(
        &mut self,
        parameter: &Parameter<'ast>,
        statements: &mut Vec<FlatStatement<T>>,
    ) -> Vec<FlatParameter> {
        let variables = self.use_variable(&parameter.id);
        match parameter.id.get_type() {
            Type::Boolean => statements.extend(Self::boolean_constraint(&variables)),
            _ => {}
        };

        variables
            .into_iter()
            .map(|v| FlatParameter {
                id: v,
                private: parameter.private,
            })
            .collect()
    }

    fn issue_new_variables(&mut self, count: usize) -> Vec<FlatVariable> {
        (0..count)
            .map(|_| {
                let var = FlatVariable::new(self.next_var_idx);
                self.next_var_idx += 1;
                var
            })
            .collect()
    }

    fn boolean_constraint<T: Field>(variables: &Vec<FlatVariable>) -> Vec<FlatStatement<T>> {
        variables
            .iter()
            .map(|v| {
                FlatStatement::Condition(
                    FlatExpression::Identifier(*v),
                    FlatExpression::Mult(
                        box FlatExpression::Identifier(*v),
                        box FlatExpression::Identifier(*v),
                    ),
                )
            })
            .collect()
    }

    // create an internal variable. We do not register it in the layout
    fn use_sym(&mut self) -> FlatVariable {
        let var = self.issue_new_variables(1);
        var[0]
    }

    fn get_function<'a, T: Field>(
        &self,
        s: Signature,
        functions_flattened: &'a Vec<FlatFunction<T>>,
        id: &str,
    ) -> &'a FlatFunction<T> {
        functions_flattened
            .iter()
            .find(|f| f.id == id && f.signature == s)
            .unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Signature;
    use crate::types::Type;
    use zokrates_field::Bn128Field;

    mod boolean_checks {
        use super::*;

        #[test]
        fn boolean_arg() {
            // def main(bool a):
            //    return a
            //
            // -> should flatten to
            //
            // def main(_0) -> (1):
            //    _0 * _0 == _0
            //    return _0

            let function: TypedFunction<FieldPrime> = TypedFunction {
                id: "main",
                arguments: vec![Parameter::private(Variable::boolean("a".into()))],
                statements: vec![TypedStatement::Return(vec![BooleanExpression::Identifier(
                    "a".into(),
                )
                .into()])],
                signature: Signature::new()
                    .inputs(vec![Type::Boolean])
                    .outputs(vec![Type::Boolean]),
            };

            let expected = FlatFunction {
                id: String::from("main"),
                arguments: vec![FlatParameter::private(FlatVariable::new(0))],
                statements: vec![
                    FlatStatement::Condition(
                        FlatExpression::Identifier(FlatVariable::new(0)),
                        FlatExpression::Mult(
                            box FlatExpression::Identifier(FlatVariable::new(0)),
                            box FlatExpression::Identifier(FlatVariable::new(0)),
                        ),
                    ),
                    FlatStatement::Return(FlatExpressionList {
                        expressions: vec![FlatExpression::Identifier(FlatVariable::new(0))],
                    }),
                ],
                signature: Signature::new()
                    .inputs(vec![Type::Boolean])
                    .outputs(vec![Type::Boolean]),
            };

            let mut flattener = Flattener::new();

            let flat_function = flattener.flatten_function(&mut vec![], function);

            assert_eq!(flat_function, expected);
        }
    }

    #[test]
    fn multiple_definition() {
        // def foo()
        //     return 1, 2
        // def main()
        //     a, b = foo()

        let mut flattener = Flattener::new();
        let mut functions_flattened = vec![FlatFunction {
            id: "foo".to_string(),
            arguments: vec![],
            statements: vec![FlatStatement::Return(FlatExpressionList {
                expressions: vec![
                    FlatExpression::Number(FieldPrime::from(1)),
                    FlatExpression::Number(FieldPrime::from(2)),
                ],
            })],
            signature: Signature::new()
                .inputs(vec![])
                .outputs(vec![Type::FieldElement, Type::FieldElement]),
        }];
        let mut statements_flattened = vec![];
        let statement = TypedStatement::MultipleDefinition(
            vec![
                Variable::field_element("a".into()),
                Variable::field_element("b".into()),
            ],
            TypedExpressionList::FunctionCall(
                "foo".to_string(),
                vec![],
                vec![Type::FieldElement, Type::FieldElement],
            ),
        );

        flattener.flatten_statement(
            &mut functions_flattened,
            &mut statements_flattened,
            statement,
        );

        let a = FlatVariable::new(0);

        assert_eq!(
            statements_flattened[0],
            FlatStatement::Definition(a, FlatExpression::Number(FieldPrime::from(1)))
        );
    }

    #[test]
    fn multiple_definition2() {
        // def dup(x)
        //     return x, x
        // def main()
        //     a, b = dup(2)

        let a = FlatVariable::new(0);

        let mut flattener = Flattener::new();
        let mut functions_flattened = vec![FlatFunction {
            id: "dup".to_string(),
            arguments: vec![FlatParameter {
                id: a,
                private: true,
            }],
            statements: vec![FlatStatement::Return(FlatExpressionList {
                expressions: vec![FlatExpression::Identifier(a), FlatExpression::Identifier(a)],
            })],
            signature: Signature::new()
                .inputs(vec![Type::FieldElement])
                .outputs(vec![Type::FieldElement, Type::FieldElement]),
        }];
        let statement = TypedStatement::MultipleDefinition(
            vec![
                Variable::field_element("a".into()),
                Variable::field_element("b".into()),
            ],
            TypedExpressionList::FunctionCall(
                "dup".to_string(),
                vec![TypedExpression::FieldElement(
                    FieldElementExpression::Number(FieldPrime::from(2)),
                )],
                vec![Type::FieldElement, Type::FieldElement],
            ),
        );

        let fun = TypedFunction {
            id: "main",
            arguments: vec![],
            statements: vec![statement],
            signature: Signature {
                inputs: vec![],
                outputs: vec![],
            },
        };

        let f = flattener.flatten_function(&mut functions_flattened, fun);

        let a = FlatVariable::new(0);

        assert_eq!(
            f.statements[0],
            FlatStatement::Definition(a, FlatExpression::Number(FieldPrime::from(2)))
        );
    }

    #[test]
    fn simple_definition() {
        // def foo()
        //     return 1
        // def main()
        //     a = foo()

        let mut flattener = Flattener::new();
        let mut functions_flattened = vec![FlatFunction {
            id: "foo".to_string(),
            arguments: vec![],
            statements: vec![FlatStatement::Return(FlatExpressionList {
                expressions: vec![FlatExpression::Number(FieldPrime::from(1))],
            })],
            signature: Signature::new()
                .inputs(vec![])
                .outputs(vec![Type::FieldElement]),
        }];
        let mut statements_flattened = vec![];
        let statement = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_element("a".into())),
            TypedExpression::FieldElement(FieldElementExpression::FunctionCall(
                "foo".to_string(),
                vec![],
            )),
        );

        flattener.flatten_statement(
            &mut functions_flattened,
            &mut statements_flattened,
            statement,
        );

        let a = FlatVariable::new(0);

        assert_eq!(
            statements_flattened[0],
            FlatStatement::Definition(a, FlatExpression::Number(FieldPrime::from(1)))
        );
    }

    #[test]
    fn redefine_argument() {
        // def foo(a)
        //     a = a + 1
        //     return 1

        // should flatten to no redefinition
        // def foo(a)
        //     a_0 = a + 1
        //     return 1

        let mut flattener = Flattener::new();
        let mut functions_flattened = vec![];

        let funct = TypedFunction {
            id: "foo",
            signature: Signature::new()
                .inputs(vec![Type::FieldElement])
                .outputs(vec![Type::FieldElement]),
            arguments: vec![Parameter {
                id: Variable::field_element("a".into()),
                private: true,
            }],
            statements: vec![
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("a".into())),
                    FieldElementExpression::Add(
                        box FieldElementExpression::Identifier("a".into()),
                        box FieldElementExpression::Number(FieldPrime::from(1)),
                    )
                    .into(),
                ),
                TypedStatement::Return(vec![
                    FieldElementExpression::Number(FieldPrime::from(1)).into()
                ]),
            ],
        };

        let flat_funct = flattener.flatten_function(&mut functions_flattened, funct);

        let a = FlatVariable::new(0);
        let a_0 = FlatVariable::new(1);

        assert_eq!(
            flat_funct.statements[0],
            FlatStatement::Definition(
                a_0,
                FlatExpression::Add(
                    box FlatExpression::Identifier(a),
                    box FlatExpression::Number(FieldPrime::from(1))
                )
            )
        );
    }

    #[test]
    fn call_with_def() {
        // def foo():
        //     a = 3
        //     return a

        // def main():
        //     return foo()

        let foo = TypedFunction {
            id: "foo",
            arguments: vec![],
            statements: vec![
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("a".into())),
                    FieldElementExpression::Number(FieldPrime::from(3)).into(),
                ),
                TypedStatement::Return(vec![FieldElementExpression::Identifier("a".into()).into()]),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![Type::FieldElement],
            },
        };

        let main = TypedFunction {
            id: "main",
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![
                FieldElementExpression::FunctionCall(String::from("foo"), vec![]).into(),
            ])],
            signature: Signature {
                inputs: vec![],
                outputs: vec![Type::FieldElement],
            },
        };

        let mut flattener = Flattener::new();

        let foo_flattened = flattener.flatten_function(&mut vec![], foo);

        let expected = FlatFunction {
            id: String::from("main"),
            arguments: vec![],
            statements: vec![
                FlatStatement::Definition(
                    FlatVariable::new(0),
                    FlatExpression::Number(FieldPrime::from(3)),
                ),
                FlatStatement::Return(FlatExpressionList {
                    expressions: vec![FlatExpression::Identifier(FlatVariable::new(0))],
                }),
            ],
            signature: Signature::new().outputs(vec![Type::FieldElement]),
        };

        let main_flattened = flattener.flatten_function(&mut vec![foo_flattened], main);

        assert_eq!(main_flattened, expected);
    }

    #[test]
    fn power_zero() {
        // def main():
        //     field a = 7
        //     field b = a**0
        //     return b

        // def main():
        //     _0 = 7
        //     _1 = 1         // power flattening returns 1, definition introduces _7
        //     return _1
        let function = TypedFunction {
            id: "main",
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
            id: String::from("main"),
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
            signature: Signature::new().outputs(vec![Type::FieldElement]),
        };

        let flattened = flattener.flatten_function(&mut vec![], function);

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
            id: "main",
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
            id: String::from("main"),
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
            signature: Signature::new().outputs(vec![Type::FieldElement]),
        };

        let flattened = flattener.flatten_function(&mut vec![], function);

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
            id: "main",
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
            id: String::from("main"),
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
            signature: Signature::new().outputs(vec![Type::FieldElement]),
        };

        let flattened = flattener.flatten_function(&mut vec![], function);

        assert_eq!(flattened, expected);
    }

    #[test]
    fn overload() {
        // def foo()
        //      return 1
        // def foo()
        //      return 1, 2
        // def main()
        //      a = foo()
        //      b, c = foo()
        //      return 1
        //
        //      should not panic
        //

        let mut flattener = Flattener::new();
        let functions = vec![
            TypedFunction {
                id: "foo",
                arguments: vec![],
                statements: vec![TypedStatement::Return(vec![TypedExpression::FieldElement(
                    FieldElementExpression::Number(FieldPrime::from(1)),
                )])],
                signature: Signature::new()
                    .inputs(vec![])
                    .outputs(vec![Type::FieldElement]),
            },
            TypedFunction {
                id: "foo",
                arguments: vec![],
                statements: vec![TypedStatement::Return(vec![
                    TypedExpression::FieldElement(FieldElementExpression::Number(
                        FieldPrime::from(1),
                    )),
                    TypedExpression::FieldElement(FieldElementExpression::Number(
                        FieldPrime::from(2),
                    )),
                ])],
                signature: Signature::new()
                    .inputs(vec![])
                    .outputs(vec![Type::FieldElement, Type::FieldElement]),
            },
            TypedFunction {
                id: "main",
                arguments: vec![],
                statements: vec![
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_element("a".into())),
                        TypedExpression::FieldElement(FieldElementExpression::FunctionCall(
                            "foo".to_string(),
                            vec![],
                        )),
                    ),
                    TypedStatement::MultipleDefinition(
                        vec![
                            Variable::field_element("b".into()),
                            Variable::field_element("c".into()),
                        ],
                        TypedExpressionList::FunctionCall(
                            "foo".to_string(),
                            vec![],
                            vec![Type::FieldElement, Type::FieldElement],
                        ),
                    ),
                    TypedStatement::Return(vec![TypedExpression::FieldElement(
                        FieldElementExpression::Number(FieldPrime::from(1)),
                    )]),
                ],
                signature: Signature::new()
                    .inputs(vec![])
                    .outputs(vec![Type::FieldElement]),
            },
        ];

        flattener.flatten_program(TypedProg {
            functions: functions,
            imported_functions: vec![],
            imports: vec![],
        });

        // shouldn't panic
    }

    #[test]
    fn if_else() {
        let mut flattener = Flattener::new();
        let expression = FieldElementExpression::IfElse(
            box BooleanExpression::Eq(
                box FieldElementExpression::Number(FieldPrime::from(32)),
                box FieldElementExpression::Number(FieldPrime::from(4)),
            ),
            box FieldElementExpression::Number(FieldPrime::from(12)),
            box FieldElementExpression::Number(FieldPrime::from(51)),
        );

        let mut functions_flattened = vec![];
        flattener.load_corelib(&mut functions_flattened);

        flattener.flatten_field_expression(&functions_flattened, &mut vec![], expression);
    }

    #[test]
    fn geq_leq() {
        let mut flattener = Flattener::new();
        let expression_le = BooleanExpression::Le(
            box FieldElementExpression::Number(FieldPrime::from(32)),
            box FieldElementExpression::Number(FieldPrime::from(4)),
        );

        let expression_ge = BooleanExpression::Ge(
            box FieldElementExpression::Number(FieldPrime::from(32)),
            box FieldElementExpression::Number(FieldPrime::from(4)),
        );

        flattener.flatten_boolean_expression(&mut vec![], &mut vec![], expression_le);

        flattener.flatten_boolean_expression(&mut vec![], &mut vec![], expression_ge);
    }

    #[test]
    fn bool_and() {
        let expression = FieldElementExpression::IfElse(
            box BooleanExpression::And(
                box BooleanExpression::Eq(
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

        let mut flattener = Flattener::new();
        let mut functions_flattened = vec![];
        flattener.load_corelib(&mut functions_flattened);
        flattener.flatten_field_expression(&functions_flattened, &mut vec![], expression);
    }

    #[test]
    fn div() {
        // a = 5 / b / b
        let mut flattener = Flattener::new();
        let mut functions_flattened = vec![];
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

        flattener.flatten_statement(
            &mut functions_flattened,
            &mut statements_flattened,
            definition,
        );

        flattener.flatten_statement(
            &mut functions_flattened,
            &mut statements_flattened,
            statement,
        );

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
                FlatStatement::Directive(DirectiveStatement::new(
                    vec![invb0],
                    Helper::Rust(RustHelper::Div),
                    vec![FlatExpression::Number(FieldPrime::from(1)), b0.into()]
                )),
                FlatStatement::Condition(
                    FlatExpression::Number(FieldPrime::from(1)),
                    FlatExpression::Mult(box invb0.into(), box b0.into()),
                ),
                // execute div
                FlatStatement::Directive(DirectiveStatement::new(
                    vec![sym_0],
                    Helper::Rust(RustHelper::Div),
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
                FlatStatement::Directive(DirectiveStatement::new(
                    vec![invb1],
                    Helper::Rust(RustHelper::Div),
                    vec![FlatExpression::Number(FieldPrime::from(1)), b1.into()]
                )),
                FlatStatement::Condition(
                    FlatExpression::Number(FieldPrime::from(1)),
                    FlatExpression::Mult(box invb1.into(), box b1.into()),
                ),
                // execute div
                FlatStatement::Directive(DirectiveStatement::new(
                    vec![sym_2],
                    Helper::Rust(RustHelper::Div),
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
        let mut functions_flattened = vec![];
        let mut statements_flattened = vec![];
        let statement = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_array("foo".into(), 3)),
            FieldElementArrayExpression::Value(
                3,
                vec![
                    FieldElementExpression::Number(FieldPrime::from(1)),
                    FieldElementExpression::Number(FieldPrime::from(2)),
                    FieldElementExpression::Number(FieldPrime::from(3)),
                ],
            )
            .into(),
        );
        let expression = FieldElementArrayExpression::Identifier(3, "foo".into());

        flattener.flatten_statement(
            &mut functions_flattened,
            &mut statements_flattened,
            statement,
        );

        let expressions = flattener.flatten_field_array_expression(
            &mut functions_flattened,
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
        let mut functions_flattened = vec![];
        let mut statements_flattened = vec![];
        let statement = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_array("foo".into(), 3)),
            FieldElementArrayExpression::Value(
                3,
                vec![
                    FieldElementExpression::Number(FieldPrime::from(1)),
                    FieldElementExpression::Number(FieldPrime::from(2)),
                    FieldElementExpression::Number(FieldPrime::from(3)),
                ],
            )
            .into(),
        );

        flattener.flatten_statement(
            &mut functions_flattened,
            &mut statements_flattened,
            statement,
        );

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
        let mut functions_flattened = vec![];
        let mut statements_flattened = vec![];
        let statement = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_array("foo".into(), 3)),
            FieldElementArrayExpression::Value(
                3,
                vec![
                    FieldElementExpression::Number(FieldPrime::from(1)),
                    FieldElementExpression::Number(FieldPrime::from(2)),
                    FieldElementExpression::Number(FieldPrime::from(3)),
                ],
            )
            .into(),
        );

        let expression = FieldElementExpression::Select(
            box FieldElementArrayExpression::Identifier(3, "foo".into()),
            box FieldElementExpression::Number(FieldPrime::from(1)),
        );

        flattener.flatten_statement::<FieldPrime>(
            &mut functions_flattened,
            &mut statements_flattened,
            statement,
        );

        let flat_expression = flattener.flatten_field_expression::<FieldPrime>(
            &mut functions_flattened,
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
        let mut functions_flattened = vec![];
        let mut statements_flattened = vec![];
        let def = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_array("foo".into(), 3)),
            FieldElementArrayExpression::Value(
                3,
                vec![
                    FieldElementExpression::Number(FieldPrime::from(1)),
                    FieldElementExpression::Number(FieldPrime::from(2)),
                    FieldElementExpression::Number(FieldPrime::from(3)),
                ],
            )
            .into(),
        );

        let sum = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_element("bar".into())),
            FieldElementExpression::Add(
                box FieldElementExpression::Add(
                    box FieldElementExpression::Select(
                        box FieldElementArrayExpression::Identifier(3, "foo".into()),
                        box FieldElementExpression::Number(FieldPrime::from(0)),
                    ),
                    box FieldElementExpression::Select(
                        box FieldElementArrayExpression::Identifier(3, "foo".into()),
                        box FieldElementExpression::Number(FieldPrime::from(1)),
                    ),
                ),
                box FieldElementExpression::Select(
                    box FieldElementArrayExpression::Identifier(3, "foo".into()),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                ),
            )
            .into(),
        );

        flattener.flatten_statement::<FieldPrime>(
            &mut functions_flattened,
            &mut statements_flattened,
            def,
        );

        flattener.flatten_statement::<FieldPrime>(
            &mut functions_flattened,
            &mut statements_flattened,
            sum,
        );

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
    fn array_if() {
        // if 1 == 1 then [1] else [3] fi

        let with_arrays = {
            let mut flattener = Flattener::new();
            let mut functions_flattened = vec![];
            flattener.load_corelib(&mut functions_flattened);
            let mut statements_flattened = vec![];

            let e = FieldElementArrayExpression::IfElse(
                box BooleanExpression::Eq(
                    box FieldElementExpression::Number(FieldPrime::from(1)),
                    box FieldElementExpression::Number(FieldPrime::from(1)),
                ),
                box FieldElementArrayExpression::Value(
                    1,
                    vec![FieldElementExpression::Number(FieldPrime::from(1))],
                ),
                box FieldElementArrayExpression::Value(
                    1,
                    vec![FieldElementExpression::Number(FieldPrime::from(3))],
                ),
            );

            (
                flattener.flatten_field_array_expression(
                    &mut functions_flattened,
                    &mut statements_flattened,
                    e,
                )[0]
                .clone(),
                statements_flattened,
            )
        };

        let without_arrays = {
            let mut flattener = Flattener::new();
            let mut functions_flattened = vec![];
            flattener.load_corelib(&mut functions_flattened);
            let mut statements_flattened = vec![];

            // if 1 == 1 then 1 else 3 fi
            let e = FieldElementExpression::IfElse(
                box BooleanExpression::Eq(
                    box FieldElementExpression::Number(FieldPrime::from(1)),
                    box FieldElementExpression::Number(FieldPrime::from(1)),
                ),
                box FieldElementExpression::Number(FieldPrime::from(1)),
                box FieldElementExpression::Number(FieldPrime::from(3)),
            );

            (
                flattener.flatten_field_expression(
                    &mut functions_flattened,
                    &mut statements_flattened,
                    e,
                ),
                statements_flattened,
            )
        };

        assert_eq!(with_arrays, without_arrays);
    }

    #[test]
    fn next_variable() {
        let mut flattener = Flattener::new();
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
