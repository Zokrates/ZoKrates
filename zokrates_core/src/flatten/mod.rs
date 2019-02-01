//! Module containing the `Flattener` to process a program that it is R1CS-able.
//!
//! @file flatten.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

use bimap::BiMap;
use flat_absy::*;
use helpers::{DirectiveStatement, Helper, RustHelper};
use std::collections::{HashMap, HashSet};
use typed_absy::*;
use types::conversions::cast;
use types::Signature;
use types::Type;
use zokrates_field::field::Field;

/// Flattener, computes flattened program.
#[derive(Debug)]
pub struct Flattener {
    /// Number of bits needed to represent the maximum value.
    bits: usize,
    /// Vector containing all used variables while processing the program.
    variables: HashSet<FlatVariable>,
    /// Map of renamings for reassigned variables while processing the program.
    substitution: HashMap<FlatVariable, FlatVariable>,
    /// Index of the next introduced variable while processing the program.
    next_var_idx: usize,
    ///
    bijection: BiMap<String, FlatVariable>,
}
impl Flattener {
    /// Returns a `Flattener` with fresh a fresh [substitution] and [variables].
    ///
    /// # Arguments
    ///
    /// * `bits` - Number of bits needed to represent the maximum value.
    pub fn new(bits: usize) -> Flattener {
        Flattener {
            bits: bits,
            variables: HashSet::new(),
            substitution: HashMap::new(),
            next_var_idx: 0,
            bijection: BiMap::new(),
        }
    }

    /// Loads the code library
    fn load_corelib<T: Field>(&mut self, functions_flattened: &mut Vec<FlatFunction<T>>) -> () {
        // Load type casting functions
        functions_flattened.push(cast(&Type::Boolean, &Type::FieldElement));
        functions_flattened.push(cast(&Type::FieldElement, &Type::Boolean));

        // Load IfElse helper
        let ie = TypedFunction {
            id: "_if_else_field".to_string(),
            arguments: vec![
                Parameter {
                    id: Variable {
                        id: "condition".to_string(),
                        _type: Type::Boolean,
                    },
                    private: true,
                },
                Parameter {
                    id: Variable {
                        id: "consequence".to_string(),
                        _type: Type::FieldElement,
                    },
                    private: true,
                },
                Parameter {
                    id: Variable {
                        id: "alternative".to_string(),
                        _type: Type::FieldElement,
                    },
                    private: true,
                },
            ],
            statements: vec![
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("condition_as_field")),
                    FieldElementExpression::FunctionCall(
                        "_bool_to_field".to_string(),
                        vec![BooleanExpression::Identifier("condition".to_string()).into()],
                    )
                    .into(),
                ),
                TypedStatement::Return(vec![FieldElementExpression::Add(
                    box FieldElementExpression::Mult(
                        box FieldElementExpression::Identifier("condition_as_field".to_string()),
                        box FieldElementExpression::Identifier("consequence".to_string()),
                    ),
                    box FieldElementExpression::Mult(
                        box FieldElementExpression::Sub(
                            box FieldElementExpression::Number(T::one()),
                            box FieldElementExpression::Identifier(
                                "condition_as_field".to_string(),
                            ),
                        ),
                        box FieldElementExpression::Identifier("alternative".to_string()),
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
        arguments_flattened: &Vec<FlatParameter>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        expression: BooleanExpression<T>,
    ) -> FlatExpression<T> {
        // those will be booleans in the future
        match expression {
            BooleanExpression::Identifier(x) => {
                FlatExpression::Identifier(self.bijection.get_by_left(&x).unwrap().clone())
            }
            BooleanExpression::Lt(box lhs, box rhs) => {
                // We know from semantic checking that lhs and rhs have the same type
                // What the expression will flatten to depends on that type

                let lhs_flattened = self.flatten_field_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    lhs,
                );
                let rhs_flattened = self.flatten_field_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    rhs,
                );

                // lhs
                let lhs_id = self.use_sym();
                statements_flattened.push(FlatStatement::Definition(lhs_id, lhs_flattened));

                // check that lhs and rhs are within the right range, ie, their last two bits are zero

                // lhs
                {
                    // define variables for the bits
                    let lhs_bits: Vec<FlatVariable> =
                        (0..self.bits).map(|_| self.use_sym()).collect();

                    // add a directive to get the bits
                    statements_flattened.push(FlatStatement::Directive(DirectiveStatement::new(
                        lhs_bits.clone(),
                        Helper::bits(),
                        vec![lhs_id],
                    )));

                    // bitness checks
                    for i in 0..self.bits - 2 {
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

                    for i in 0..self.bits - 2 {
                        lhs_sum = FlatExpression::Add(
                            box lhs_sum,
                            box FlatExpression::Mult(
                                box FlatExpression::Identifier(lhs_bits[i + 2]),
                                box FlatExpression::Number(T::from(2).pow(self.bits - 2 - i - 1)),
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
                        (0..self.bits).map(|_| self.use_sym()).collect();

                    // add a directive to get the bits
                    statements_flattened.push(FlatStatement::Directive(DirectiveStatement::new(
                        rhs_bits.clone(),
                        Helper::bits(),
                        vec![rhs_id],
                    )));

                    // bitness checks
                    for i in 0..self.bits - 2 {
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

                    for i in 0..self.bits - 2 {
                        rhs_sum = FlatExpression::Add(
                            box rhs_sum,
                            box FlatExpression::Mult(
                                box FlatExpression::Identifier(rhs_bits[i + 2]),
                                box FlatExpression::Number(T::from(2).pow(self.bits - 2 - i - 1)),
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
                let sub_bits: Vec<FlatVariable> = (0..self.bits).map(|_| self.use_sym()).collect();

                // add a directive to get the bits
                statements_flattened.push(FlatStatement::Directive(DirectiveStatement::new(
                    sub_bits.clone(),
                    Helper::bits(),
                    vec![subtraction_result.clone()],
                )));

                // bitness checks
                for i in 0..self.bits {
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

                for i in 0..self.bits {
                    expr = FlatExpression::Add(
                        box expr,
                        box FlatExpression::Mult(
                            box FlatExpression::Identifier(sub_bits[i]),
                            box FlatExpression::Number(T::from(2).pow(self.bits - i - 1)),
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
                    arguments_flattened,
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
                    arguments_flattened,
                    statements_flattened,
                    BooleanExpression::Lt(box lhs.clone(), box rhs.clone()),
                );
                let eq = self.flatten_boolean_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    BooleanExpression::Eq(box lhs.clone(), box rhs.clone()),
                );
                FlatExpression::Add(box eq, box lt)
            }
            BooleanExpression::Gt(lhs, rhs) => self.flatten_boolean_expression(
                functions_flattened,
                arguments_flattened,
                statements_flattened,
                BooleanExpression::Lt(rhs, lhs),
            ),
            BooleanExpression::Ge(lhs, rhs) => self.flatten_boolean_expression(
                functions_flattened,
                arguments_flattened,
                statements_flattened,
                BooleanExpression::Le(rhs, lhs),
            ),
            BooleanExpression::Or(box lhs, box rhs) => {
                let x = box self.flatten_boolean_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    lhs,
                );
                let y = box self.flatten_boolean_expression(
                    functions_flattened,
                    arguments_flattened,
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
                let x = self.flatten_boolean_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    lhs,
                );
                let y = self.flatten_boolean_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    rhs,
                );

                let name_x_and_y = self.use_sym();
                assert!(x.is_linear() && y.is_linear());
                statements_flattened.push(FlatStatement::Definition(
                    name_x_and_y,
                    FlatExpression::Mult(box x, box y),
                ));

                FlatExpression::Identifier(name_x_and_y)
            }
            BooleanExpression::Not(box exp) => {
                let x = self.flatten_boolean_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    exp,
                );
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
        arguments_flattened: &Vec<FlatParameter>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        id: &String,
        return_types: Vec<Type>,
        param_expressions: &Vec<TypedExpression<T>>,
    ) -> FlatExpressionList<T> {
        let passed_signature = Signature::new()
            .inputs(
                param_expressions
                    .into_iter()
                    .map(|e| e.get_type())
                    .collect(),
            )
            .outputs(return_types);

        for funct in functions_flattened {
            if funct.id == *id && funct.signature == passed_signature {
                // funct is now the called function

                // Stores prefixed variables

                let mut replacement_map = HashMap::new();

                // Handle complex parameters and assign values:
                // Rename Parameters, assign them to values in call. Resolve complex expressions with definitions
                let params_flattened = param_expressions
                    .clone()
                    .into_iter()
                    .map(|param_expr| {
                        self.flatten_expression(
                            functions_flattened,
                            arguments_flattened,
                            statements_flattened,
                            param_expr,
                        )
                    })
                    .into_iter()
                    .flat_map(|x| x)
                    .collect::<Vec<_>>();

                let params_flattened = params_flattened
                    .into_iter()
                    .map(|e| e.apply_recursive_substitution(&self.substitution))
                    .collect::<Vec<_>>();

                for (index, r) in params_flattened.into_iter().enumerate() {
                    let new_var = self.use_sym();
                    statements_flattened.push(FlatStatement::Definition(new_var, r));
                    replacement_map.insert(funct.arguments.get(index).unwrap().id.clone(), new_var);
                }

                // Ensure Renaming and correct returns:
                // add all flattened statements, adapt return statement
                for stat in funct.statements.clone() {
                    match stat {
                        // set return statements right sidreturne as expression result
                        FlatStatement::Return(list) => {
                            return FlatExpressionList {
                                expressions: list
                                    .expressions
                                    .into_iter()
                                    .map(|x| x.apply_direct_substitution(&replacement_map))
                                    .collect(),
                            };
                        }
                        FlatStatement::Definition(var, rhs) => {
                            let new_var = self.issue_new_variable();
                            replacement_map.insert(var, new_var);
                            let new_rhs = rhs.apply_direct_substitution(&replacement_map);
                            statements_flattened.push(FlatStatement::Definition(new_var, new_rhs));
                        }
                        FlatStatement::Condition(lhs, rhs) => {
                            let new_lhs = lhs.apply_direct_substitution(&replacement_map);
                            let new_rhs = rhs.apply_direct_substitution(&replacement_map);
                            statements_flattened.push(FlatStatement::Condition(new_lhs, new_rhs));
                        }
                        FlatStatement::Directive(d) => {
                            let new_outputs = d
                                .outputs
                                .into_iter()
                                .map(|o| {
                                    let new_o = self.issue_new_variable();
                                    replacement_map.insert(o, new_o);
                                    new_o
                                })
                                .collect();
                            let new_inputs = d
                                .inputs
                                .into_iter()
                                .map(|i| i.apply_direct_substitution(&replacement_map))
                                .collect();
                            statements_flattened.push(FlatStatement::Directive(
                                DirectiveStatement {
                                    outputs: new_outputs,
                                    helper: d.helper.clone(),
                                    inputs: new_inputs,
                                },
                            ))
                        }
                    }
                }
            }
        }
        panic!(
            "TypedFunction definition for function {} with {:?} argument(s) not found. Should have been detected during semantic checking.",
            id,
            param_expressions
        );
    }

    fn flatten_expression<T: Field>(
        &mut self,
        functions_flattened: &Vec<FlatFunction<T>>,
        arguments_flattened: &Vec<FlatParameter>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        expr: TypedExpression<T>,
    ) -> Vec<FlatExpression<T>> {
        match expr {
            TypedExpression::FieldElement(e) => vec![self.flatten_field_expression(
                functions_flattened,
                arguments_flattened,
                statements_flattened,
                e,
            )],
            TypedExpression::Boolean(e) => vec![self.flatten_boolean_expression(
                functions_flattened,
                arguments_flattened,
                statements_flattened,
                e,
            )],
            TypedExpression::FieldElementArray(e) => self.flatten_field_array_expression(
                functions_flattened,
                arguments_flattened,
                statements_flattened,
                e,
            ),
        }
    }

    fn flatten_field_expression<T: Field>(
        &mut self,
        functions_flattened: &Vec<FlatFunction<T>>,
        arguments_flattened: &Vec<FlatParameter>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        expr: FieldElementExpression<T>,
    ) -> FlatExpression<T> {
        match expr {
            FieldElementExpression::Number(x) => FlatExpression::Number(x), // force to be a field element
            FieldElementExpression::Identifier(x) => {
                FlatExpression::Identifier(self.bijection.get_by_left(&x).unwrap().clone())
            }
            FieldElementExpression::Add(box left, box right) => {
                let left_flattened = self.flatten_field_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    left,
                );
                let right_flattened = self.flatten_field_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    right,
                );
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
                let left_flattened = self.flatten_field_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    left,
                );
                let right_flattened = self.flatten_field_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    right,
                );

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
                let left_flattened = self.flatten_field_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    left,
                );
                let right_flattened = self.flatten_field_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    right,
                );
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
                let left_flattened = self.flatten_field_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    left,
                );
                let right_flattened = self.flatten_field_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    right,
                );
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
                        let base_flattened = self
                            .flatten_field_expression(
                                functions_flattened,
                                arguments_flattened,
                                statements_flattened,
                                base.clone(),
                            )
                            .apply_recursive_substitution(&self.substitution);

                        // we require from the base to be linear
                        // TODO change that
                        assert!(base_flattened.is_linear());

                        match e {
                            e if *e == T::zero() => FlatExpression::Number(T::one()),
                            // flatten(base ** 1) == flatten(base)
                            e if *e == T::one() => base_flattened,
                            // flatten(base ** 2) == flatten(base) * flatten(base)
                            // in this case, no need to define an intermediate variable
                            // as if a is linear, a ** 2 quadratic
                            e if *e == T::from(2) => {
                                FlatExpression::Mult(box base_flattened.clone(), box base_flattened)
                            }
                            // flatten(base ** n) = flatten(base) * flatten(base ** (n-1))
                            e => {
                                // flatten(base ** (n-1))
                                let tmp_expression = self
                                    .flatten_field_expression(
                                        functions_flattened,
                                        arguments_flattened,
                                        statements_flattened,
                                        FieldElementExpression::Pow(
                                            box base,
                                            box FieldElementExpression::Number(
                                                e.clone() - T::one(),
                                            ),
                                        ),
                                    )
                                    .apply_recursive_substitution(&self.substitution);

                                let id = self.use_sym();

                                statements_flattened
                                    .push(FlatStatement::Definition(id, tmp_expression));

                                FlatExpression::Mult(
                                    box FlatExpression::Identifier(id),
                                    box base_flattened,
                                )
                            }
                        }
                    }
                    _ => panic!("Expected number as pow exponent"),
                }
            }
            FieldElementExpression::IfElse(box condition, box consequent, box alternative) => self
                .flatten_function_call(
                    functions_flattened,
                    arguments_flattened,
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
                    arguments_flattened,
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
                                self.get_latest_var_substitution(&format!("{}_c{}", id, n))
                                    .clone(),
                            )
                        }
                        FieldElementArrayExpression::Value(size, expressions) => {
                            assert!(n < T::from(size));
                            self.flatten_field_expression(
                                functions_flattened,
                                arguments_flattened,
                                statements_flattened,
                                expressions[n.to_dec_string().parse::<usize>().unwrap()].clone(),
                            )
                            .apply_recursive_substitution(&self.substitution)
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
                                arguments_flattened,
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
                            .apply_recursive_substitution(&self.substitution)
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
                            arguments_flattened,
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
                                        FieldElementArrayExpression::Identifier(_, id) => {
                                            FieldElementExpression::Identifier(format!(
                                                "{}_c{}",
                                                id, i
                                            ))
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
                            arguments_flattened,
                            statements_flattened,
                            lookup,
                        )
                        .apply_recursive_substitution(&self.substitution)
                    }
                }
            }
        }
    }

    fn flatten_field_array_expression<T: Field>(
        &mut self,
        functions_flattened: &Vec<FlatFunction<T>>,
        arguments_flattened: &Vec<FlatParameter>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        expr: FieldElementArrayExpression<T>,
    ) -> Vec<FlatExpression<T>> {
        match expr {
            FieldElementArrayExpression::Identifier(size, x) => (0..size)
                .map(|index| {
                    FlatExpression::Identifier(
                        self.get_latest_var_substitution(&format!("{}_c{}", x, index))
                            .clone(),
                    )
                })
                .collect(),
            FieldElementArrayExpression::Value(size, values) => {
                assert_eq!(size, values.len());
                values
                    .into_iter()
                    .map(|v| {
                        self.flatten_field_expression(
                            functions_flattened,
                            arguments_flattened,
                            statements_flattened,
                            v,
                        )
                    })
                    .collect()
            }
            FieldElementArrayExpression::FunctionCall(size, ref id, ref param_expressions) => {
                let exprs_flattened = self.flatten_function_call(
                    functions_flattened,
                    arguments_flattened,
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
                            arguments_flattened,
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

    pub fn flatten_statement<T: Field>(
        &mut self,
        functions_flattened: &Vec<FlatFunction<T>>,
        arguments_flattened: &Vec<FlatParameter>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        stat: TypedStatement<T>,
    ) {
        match stat {
            TypedStatement::Return(exprs) => {
                let flat_expressions = exprs
                    .into_iter()
                    .map(|expr| {
                        self.flatten_expression(
                            functions_flattened,
                            arguments_flattened,
                            statements_flattened,
                            expr,
                        )
                    })
                    .flat_map(|x| x)
                    .collect::<Vec<_>>();

                let flat_expressions = flat_expressions
                    .into_iter()
                    .map(|e| e.apply_recursive_substitution(&self.substitution))
                    .collect();

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
                    arguments_flattened,
                    statements_flattened,
                    expr.clone(),
                );

                let rhs = rhs
                    .into_iter()
                    .map(|e| e.apply_recursive_substitution(&self.substitution))
                    .collect::<Vec<_>>();

                match expr.get_type() {
                    Type::FieldElement | Type::Boolean => {
                        match assignee {
                            TypedAssignee::Identifier(ref v) => {
                                let debug_name = v.clone().id;
                                let var = self.use_variable(&debug_name);
                                // handle return of function call
                                let var_to_replace = self.get_latest_var_substitution(&debug_name);
                                if !(var == var_to_replace)
                                    && self.variables.contains(&var_to_replace)
                                    && !self.substitution.contains_key(&var_to_replace)
                                {
                                    self.substitution
                                        .insert(var_to_replace.clone(), var.clone());
                                }
                                statements_flattened
                                    .push(FlatStatement::Definition(var, rhs[0].clone()));
                            }
                            TypedAssignee::ArrayElement(ref array, ref index) => {
                                let expr = match expr {
                                    TypedExpression::FieldElement(e) => e,
                                    _ => panic!("not a field element as rhs of array element update, should have been caught at semantic")
                                };
                                match index {
                                    box FieldElementExpression::Number(n) => {
                                        match array {
                                            box TypedAssignee::Identifier(id) => {
                                                let debug_name = format!("{}_c{}", id.id, n);
                                                let var = self.use_variable(&debug_name);
                                                // handle return of function call
                                                let var_to_replace =
                                                    self.get_latest_var_substitution(&debug_name);
                                                if !(var == var_to_replace)
                                                    && self.variables.contains(&var_to_replace)
                                                    && !self
                                                        .substitution
                                                        .contains_key(&var_to_replace)
                                                {
                                                    self.substitution.insert(
                                                        var_to_replace.clone(),
                                                        var.clone(),
                                                    );
                                                }
                                                statements_flattened.push(
                                                    FlatStatement::Definition(var, rhs[0].clone()),
                                                );
                                            }
                                            _ => panic!("no multidimension array for now"),
                                        }
                                    }
                                    box e => {
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
                                            arguments_flattened,
                                            statements_flattened,
                                            range_check_statement,
                                        );

                                        // now we redefine the whole array, updating only the piece that changed
                                        // stat(array[i] = if e == i then `expr` else `array[i]`)
                                        for i in 0..size {
                                            let rhs = FieldElementExpression::IfElse(
                                                box BooleanExpression::Eq(
                                                    box e.clone(),
                                                    box FieldElementExpression::Number(T::from(i)),
                                                ),
                                                box expr.clone(),
                                                box e.clone(),
                                            );

                                            let rhs_flattened = self.flatten_field_expression(
                                                functions_flattened,
                                                arguments_flattened,
                                                statements_flattened,
                                                rhs,
                                            );

                                            let var =
                                                self.use_variable(&format!("{}_c{}", array, i));

                                            statements_flattened.push(FlatStatement::Definition(
                                                var,
                                                rhs_flattened,
                                            ));
                                        }
                                    }
                                }
                            }
                        }
                    }
                    Type::FieldElementArray(..) => {
                        for (index, r) in rhs.into_iter().enumerate() {
                            let debug_name = match assignee {
                                TypedAssignee::Identifier(ref v) => format!("{}_c{}", v.id, index),
                                _ => unimplemented!(),
                            };
                            let var = self.use_variable(&debug_name);
                            // handle return of function call
                            let var_to_replace = self.get_latest_var_substitution(&debug_name);
                            if !(var == var_to_replace)
                                && self.variables.contains(&var_to_replace)
                                && !self.substitution.contains_key(&var_to_replace)
                            {
                                self.substitution
                                    .insert(var_to_replace.clone(), var.clone());
                            }
                            statements_flattened.push(FlatStatement::Definition(var, r));
                        }
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
                                arguments_flattened,
                                statements_flattened,
                                e1,
                            )
                            .apply_recursive_substitution(&self.substitution),
                            self.flatten_field_expression(
                                functions_flattened,
                                arguments_flattened,
                                statements_flattened,
                                e2,
                            )
                            .apply_recursive_substitution(&self.substitution),
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
                                arguments_flattened,
                                statements_flattened,
                                e1,
                            )
                            .apply_recursive_substitution(&self.substitution),
                            self.flatten_boolean_expression(
                                functions_flattened,
                                arguments_flattened,
                                statements_flattened,
                                e2,
                            )
                            .apply_recursive_substitution(&self.substitution),
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
                                arguments_flattened,
                                statements_flattened,
                                e1,
                            ),
                            self.flatten_field_array_expression(
                                functions_flattened,
                                arguments_flattened,
                                statements_flattened,
                                e2,
                            ),
                        );

                        let (lhs, rhs) = (
                            lhs.into_iter()
                                .map(|e| e.apply_recursive_substitution(&self.substitution)),
                            rhs.into_iter()
                                .map(|e| e.apply_recursive_substitution(&self.substitution)),
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
                        self.use_variable(&var.id),
                        FlatExpression::Number(current.clone()),
                    ));
                    for s in statements.clone() {
                        self.flatten_statement(
                            functions_flattened,
                            arguments_flattened,
                            statements_flattened,
                            s,
                        );
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
                        let rhs_flattened = self
                            .flatten_function_call(
                                functions_flattened,
                                arguments_flattened,
                                statements_flattened,
                                &fun_id,
                                var_types,
                                &exprs,
                            )
                            .apply_recursive_substitution(&self.substitution);

                        let mut iterator = rhs_flattened.expressions.into_iter();

                        // take each new variable being assigned
                        for v in vars {
                            // determine how many field elements it carries
                            match v.get_type() {
                                Type::FieldElementArray(size) => {
                                    for index in 0..size {
                                        let debug_name = format!("{}_c{}", v.id, index);
                                        let var = self.use_variable(&debug_name);
                                        // handle return of function call
                                        let var_to_replace =
                                            self.get_latest_var_substitution(&debug_name);
                                        if !(var == var_to_replace)
                                            && self.variables.contains(&var_to_replace)
                                            && !self.substitution.contains_key(&var_to_replace)
                                        {
                                            self.substitution
                                                .insert(var_to_replace.clone(), var.clone());
                                        }
                                        statements_flattened.push(FlatStatement::Definition(
                                            var,
                                            iterator.next().unwrap(),
                                        ));
                                    }
                                }
                                Type::Boolean | Type::FieldElement => {
                                    let debug_name = v.id;
                                    let var = self.use_variable(&debug_name);
                                    // handle return of function call
                                    let var_to_replace =
                                        self.get_latest_var_substitution(&debug_name);
                                    if !(var == var_to_replace)
                                        && self.variables.contains(&var_to_replace)
                                        && !self.substitution.contains_key(&var_to_replace)
                                    {
                                        self.substitution
                                            .insert(var_to_replace.clone(), var.clone());
                                    }
                                    statements_flattened.push(FlatStatement::Definition(
                                        var,
                                        iterator.next().unwrap(),
                                    ));
                                }
                            }
                        }

                        // we should have exhausted the return values
                        assert_eq!(iterator.next(), None);
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
    pub fn flatten_function<T: Field>(
        &mut self,
        functions_flattened: &mut Vec<FlatFunction<T>>,
        funct: TypedFunction<T>,
    ) -> FlatFunction<T> {
        self.variables = HashSet::new();
        self.substitution = HashMap::new();

        self.bijection = BiMap::new();

        self.next_var_idx = 0;

        let mut arguments_flattened: Vec<FlatParameter> = Vec::new();
        let mut statements_flattened: Vec<FlatStatement<T>> = Vec::new();

        // push parameters
        for arg in &funct.arguments {
            let arg_type = arg.id.get_type();

            match arg_type {
                Type::FieldElement => {
                    arguments_flattened.push(FlatParameter {
                        id: self.use_variable(&arg.id.id),
                        private: arg.private,
                    });
                }
                Type::Boolean => {
                    arguments_flattened.push(FlatParameter {
                        id: self.use_variable(&arg.id.id),
                        private: arg.private,
                    });
                }
                Type::FieldElementArray(size) => {
                    for i in 0..size {
                        arguments_flattened.push(FlatParameter {
                            id: self.use_variable(&format!("{}_c{}", arg.id.id, i)),
                            private: arg.private,
                        })
                    }
                }
            }
        }

        // flatten statements in functions and apply substitution
        for stat in funct.statements {
            self.flatten_statement(
                functions_flattened,
                &arguments_flattened,
                &mut statements_flattened,
                stat,
            );
        }

        FlatFunction {
            id: funct.id.clone(),
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
    pub fn flatten_program<T: Field>(&mut self, prog: TypedProg<T>) -> FlatProg<T> {
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
    fn use_variable(&mut self, name: &String) -> FlatVariable {
        // issue the variable we'll use
        let var = self.issue_new_variable();

        self.bijection.insert(name.to_string(), var);
        var
    }

    fn issue_new_variable(&mut self) -> FlatVariable {
        let var = FlatVariable::new(self.next_var_idx);
        self.next_var_idx += 1;
        var
    }

    fn use_sym(&mut self) -> FlatVariable {
        let name = format!("sym_{}", self.next_var_idx);
        let var = self.issue_new_variable();
        self.bijection.insert(name, var);
        var
    }

    fn get_latest_var_substitution(&mut self, name: &String) -> FlatVariable {
        // start with the variable name
        let latest_var = self.bijection.get_by_left(name).unwrap().clone();
        // loop {
        //     // walk the substitutions
        //     match self.substitution.get(&latest_var) {
        //         Some(x) => latest_var = x,
        //         None => break,
        //     }
        // }
        latest_var
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use types::Signature;
    use types::Type;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn multiple_definition() {
        // def foo()
        //     return 1, 2
        // def main()
        //     a, b = foo()

        let mut flattener = Flattener::new(FieldPrime::get_required_bits());
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
        let arguments_flattened = vec![];
        let mut statements_flattened = vec![];
        let statement = TypedStatement::MultipleDefinition(
            vec![
                Variable::field_element("a".to_string()),
                Variable::field_element("b".to_string()),
            ],
            TypedExpressionList::FunctionCall(
                "foo".to_string(),
                vec![],
                vec![Type::FieldElement, Type::FieldElement],
            ),
        );

        flattener.flatten_statement(
            &mut functions_flattened,
            &arguments_flattened,
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

        let mut flattener = Flattener::new(FieldPrime::get_required_bits());
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
                Variable::field_element("a".to_string()),
                Variable::field_element("b".to_string()),
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
            id: String::from("main"),
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

        let mut flattener = Flattener::new(FieldPrime::get_required_bits());
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
        let arguments_flattened = vec![];
        let mut statements_flattened = vec![];
        let statement = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_element("a")),
            TypedExpression::FieldElement(FieldElementExpression::FunctionCall(
                "foo".to_string(),
                vec![],
            )),
        );

        flattener.flatten_statement(
            &mut functions_flattened,
            &arguments_flattened,
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

        let mut flattener = Flattener::new(FieldPrime::get_required_bits());
        let mut functions_flattened = vec![];

        let funct = TypedFunction {
            id: "foo".to_string(),
            signature: Signature::new()
                .inputs(vec![Type::FieldElement])
                .outputs(vec![Type::FieldElement]),
            arguments: vec![Parameter {
                id: Variable::field_element("a"),
                private: true,
            }],
            statements: vec![
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("a")),
                    FieldElementExpression::Add(
                        box FieldElementExpression::Identifier("a".to_string()),
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
            id: String::from("foo"),
            arguments: vec![],
            statements: vec![
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("a")),
                    FieldElementExpression::Number(FieldPrime::from(3)).into(),
                ),
                TypedStatement::Return(vec![
                    FieldElementExpression::Identifier(String::from("a")).into()
                ]),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![Type::FieldElement],
            },
        };

        let main = TypedFunction {
            id: String::from("main"),
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![
                FieldElementExpression::FunctionCall(String::from("foo"), vec![]).into(),
            ])],
            signature: Signature {
                inputs: vec![],
                outputs: vec![Type::FieldElement],
            },
        };

        let mut flattener = Flattener::new(FieldPrime::get_required_bits());

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
    fn powers() {
        // def main():
        //     field a = 7
        //     field b = a**4
        //     return b

        // def main():
        //     _0 = 7
        //     _1 = (_0 * _0)
        //     _2 = (_1 * _0)
        //     _3 = (_2 * _0)
        //     return _3

        let function = TypedFunction {
            id: String::from("main"),
            arguments: vec![],
            statements: vec![
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("a")),
                    FieldElementExpression::Number(FieldPrime::from(7)).into(),
                ),
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("b")),
                    FieldElementExpression::Pow(
                        box FieldElementExpression::Identifier(String::from("a")),
                        box FieldElementExpression::Number(FieldPrime::from(4)),
                    )
                    .into(),
                ),
                TypedStatement::Return(vec![
                    FieldElementExpression::Identifier(String::from("b")).into()
                ]),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![Type::FieldElement],
            },
        };

        let mut flattener = Flattener::new(FieldPrime::get_required_bits());

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
                        box FlatExpression::Identifier(FlatVariable::new(0)),
                    ),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(3),
                    FlatExpression::Mult(
                        box FlatExpression::Identifier(FlatVariable::new(2)),
                        box FlatExpression::Identifier(FlatVariable::new(0)),
                    ),
                ),
                FlatStatement::Return(FlatExpressionList {
                    expressions: vec![FlatExpression::Identifier(FlatVariable::new(3))],
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

        let mut flattener = Flattener::new(FieldPrime::get_required_bits());
        let functions = vec![
            TypedFunction {
                id: "foo".to_string(),
                arguments: vec![],
                statements: vec![TypedStatement::Return(vec![TypedExpression::FieldElement(
                    FieldElementExpression::Number(FieldPrime::from(1)),
                )])],
                signature: Signature::new()
                    .inputs(vec![])
                    .outputs(vec![Type::FieldElement]),
            },
            TypedFunction {
                id: "foo".to_string(),
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
                id: "main".to_string(),
                arguments: vec![],
                statements: vec![
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_element("a")),
                        TypedExpression::FieldElement(FieldElementExpression::FunctionCall(
                            "foo".to_string(),
                            vec![],
                        )),
                    ),
                    TypedStatement::MultipleDefinition(
                        vec![
                            Variable::field_element("b".to_string()),
                            Variable::field_element("c".to_string()),
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
        let mut flattener = Flattener::new(FieldPrime::get_required_bits());
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

        flattener.flatten_field_expression(&functions_flattened, &vec![], &mut vec![], expression);
    }

    #[test]
    fn geq_leq() {
        let mut flattener = Flattener::new(FieldPrime::get_required_bits());
        let expression_le = BooleanExpression::Le(
            box FieldElementExpression::Number(FieldPrime::from(32)),
            box FieldElementExpression::Number(FieldPrime::from(4)),
        );

        let expression_ge = BooleanExpression::Ge(
            box FieldElementExpression::Number(FieldPrime::from(32)),
            box FieldElementExpression::Number(FieldPrime::from(4)),
        );

        flattener.flatten_boolean_expression(&mut vec![], &vec![], &mut vec![], expression_le);

        flattener.flatten_boolean_expression(&mut vec![], &vec![], &mut vec![], expression_ge);
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

        let mut flattener = Flattener::new(FieldPrime::get_required_bits());
        let mut functions_flattened = vec![];
        flattener.load_corelib(&mut functions_flattened);
        flattener.flatten_field_expression(&functions_flattened, &vec![], &mut vec![], expression);
    }

    #[test]
    fn div() {
        // a = 5 / b / b
        let mut flattener = Flattener::new(FieldPrime::get_required_bits());
        let mut functions_flattened = vec![];
        let arguments_flattened = vec![];
        let mut statements_flattened = vec![];

        let definition = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_element("b")),
            FieldElementExpression::Number(FieldPrime::from(42)).into(),
        );

        let statement = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_element("a")),
            FieldElementExpression::Div(
                box FieldElementExpression::Div(
                    box FieldElementExpression::Number(FieldPrime::from(5)),
                    box FieldElementExpression::Identifier(String::from("b")),
                ),
                box FieldElementExpression::Identifier(String::from("b")),
            )
            .into(),
        );

        flattener.flatten_statement(
            &mut functions_flattened,
            &arguments_flattened,
            &mut statements_flattened,
            definition,
        );

        flattener.flatten_statement(
            &mut functions_flattened,
            &arguments_flattened,
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

        let mut flattener = Flattener::new(FieldPrime::get_required_bits());
        let mut functions_flattened = vec![];
        let arguments_flattened = vec![];
        let mut statements_flattened = vec![];
        let statement = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_array("foo", 3)),
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
        let expression = FieldElementArrayExpression::Identifier(3, String::from("foo"));

        flattener.flatten_statement(
            &mut functions_flattened,
            &arguments_flattened,
            &mut statements_flattened,
            statement,
        );

        let expressions = flattener.flatten_field_array_expression(
            &mut functions_flattened,
            &arguments_flattened,
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

        let mut flattener = Flattener::new(FieldPrime::get_required_bits());
        let mut functions_flattened = vec![];
        let arguments_flattened = vec![];
        let mut statements_flattened = vec![];
        let statement = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_array("foo", 3)),
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
            &arguments_flattened,
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

        let mut flattener = Flattener::new(FieldPrime::get_required_bits());
        let mut functions_flattened = vec![];
        let arguments_flattened = vec![];
        let mut statements_flattened = vec![];
        let statement = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_array("foo", 3)),
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
            box FieldElementArrayExpression::Identifier(3, String::from("foo")),
            box FieldElementExpression::Number(FieldPrime::from(1)),
        );

        flattener.flatten_statement::<FieldPrime>(
            &mut functions_flattened,
            &arguments_flattened,
            &mut statements_flattened,
            statement,
        );

        let flat_expression = flattener.flatten_field_expression::<FieldPrime>(
            &mut functions_flattened,
            &arguments_flattened,
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

        let mut flattener = Flattener::new(FieldPrime::get_required_bits());
        let mut functions_flattened = vec![];
        let arguments_flattened = vec![];
        let mut statements_flattened = vec![];
        let def = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_array("foo", 3)),
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
            TypedAssignee::Identifier(Variable::field_element("bar")),
            FieldElementExpression::Add(
                box FieldElementExpression::Add(
                    box FieldElementExpression::Select(
                        box FieldElementArrayExpression::Identifier(3, String::from("foo")),
                        box FieldElementExpression::Number(FieldPrime::from(0)),
                    ),
                    box FieldElementExpression::Select(
                        box FieldElementArrayExpression::Identifier(3, String::from("foo")),
                        box FieldElementExpression::Number(FieldPrime::from(1)),
                    ),
                ),
                box FieldElementExpression::Select(
                    box FieldElementArrayExpression::Identifier(3, String::from("foo")),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                ),
            )
            .into(),
        );

        flattener.flatten_statement::<FieldPrime>(
            &mut functions_flattened,
            &arguments_flattened,
            &mut statements_flattened,
            def,
        );

        flattener.flatten_statement::<FieldPrime>(
            &mut functions_flattened,
            &arguments_flattened,
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
            let mut flattener = Flattener::new(FieldPrime::get_required_bits());
            let mut functions_flattened = vec![];
            flattener.load_corelib(&mut functions_flattened);
            let arguments_flattened = vec![];
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
                    &arguments_flattened,
                    &mut statements_flattened,
                    e,
                )[0]
                .clone(),
                statements_flattened,
            )
        };

        let without_arrays = {
            let mut flattener = Flattener::new(FieldPrime::get_required_bits());
            let mut functions_flattened = vec![];
            flattener.load_corelib(&mut functions_flattened);
            let arguments_flattened = vec![];
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
                    &arguments_flattened,
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
        let mut flattener = Flattener::new(FieldPrime::get_required_bits());
        assert_eq!(
            FlatVariable::new(0),
            flattener.use_variable(&String::from("a"))
        );
        assert_eq!(
            flattener.get_latest_var_substitution(&String::from("a")),
            FlatVariable::new(0)
        );
        assert_eq!(
            FlatVariable::new(1),
            flattener.use_variable(&String::from("a"))
        );
        assert_eq!(
            flattener.get_latest_var_substitution(&String::from("a")),
            FlatVariable::new(1)
        );
        assert_eq!(
            FlatVariable::new(2),
            flattener.use_variable(&String::from("a"))
        );
        assert_eq!(
            flattener.get_latest_var_substitution(&String::from("a")),
            FlatVariable::new(2)
        );
    }
}
