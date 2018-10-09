//! Module containing the `Flattener` to process a program that it is R1CS-able.
//!
//! @file flatten.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

use std::collections::{HashSet};
use typed_absy::*;
use field::Field;
use flat_absy::*;
use substitution::direct_substitution::DirectSubstitution;
use substitution::Substitution;
use helpers::{DirectiveStatement, Helper, RustHelper};
use types::Type;
use types::Signature;
use types::conversions::cast;
use absy::variable::Variable;
use absy::parameter::Parameter;
use bimap::BiMap;

/// Flattener, computes flattened program.
#[derive(Debug)]
pub struct Flattener {
    /// Number of bits needed to represent the maximum value.
    bits: usize,
    /// Vector containing all used variables while processing the program.
    variables: HashSet<FlatVariable>,
    /// Map of renamings for reassigned variables while processing the program.
    substitution: DirectSubstitution,
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
            substitution: DirectSubstitution::new(),
            next_var_idx: 0,
            bijection: BiMap::new(),
        }
    }

    /// Loads the standard library
    fn load_stdlib<T: Field>(
        &mut self,
        functions_flattened: &mut Vec<FlatFunction<T>>,
    ) -> () {

        // Load type casting functions
        functions_flattened.push(cast(&Type::Boolean, &Type::FieldElement));
        functions_flattened.push(cast(&Type::FieldElement, &Type::Boolean));

        // Load IfElse helpers
        let ie = TypedFunction {
            id: "_if_else_field".to_string(),
            arguments: vec![Parameter {
                id: Variable {
                    id: "condition".to_string(),
                    _type: Type::Boolean
                }, 
                private: true 
            },
            Parameter {
                id: Variable {
                    id: "consequence".to_string(),
                    _type: Type::FieldElement
                }, 
                private: true 
            },
            Parameter {
                id: Variable {
                    id: "alternative".to_string(),
                    _type: Type::FieldElement
                }, 
                private: true 
            }],
            statements: vec![
                TypedStatement::Definition(
                    Variable::field_element("condition_as_field"),
                    FieldElementExpression::FunctionCall(
                        "_bool_to_field".to_string(), 
                        vec![
                                BooleanExpression::Identifier("condition".to_string()).into()
                        ]
                    ).into()
                ),
                TypedStatement::Return(
                    vec![
                        FieldElementExpression::Add(
                            box FieldElementExpression::Mult(
                                box FieldElementExpression::Identifier("condition_as_field".to_string()),
                                box FieldElementExpression::Identifier("consequence".to_string()),
                            ),
                            box FieldElementExpression::Mult(
                                box FieldElementExpression::Sub(
                                    box FieldElementExpression::Number(T::one()),
                                    box FieldElementExpression::Identifier("condition_as_field".to_string())
                                ),
                                box FieldElementExpression::Identifier("alternative".to_string())
                            )
                        ).into()
                    ]
                )
            ],
            signature: Signature::new()
                .inputs(vec![Type::Boolean, Type::FieldElement, Type::FieldElement])
                .outputs(vec![Type::FieldElement])
        };

        let ief = self.flatten_function(
            functions_flattened,
            ie,
        );
        functions_flattened.push(ief);
    }

    /// Flattens a boolean expression
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `condition` - `Condition` that will be flattened.
    fn flatten_boolean_expression<T: Field>(
        &mut self,
        functions_flattened: &Vec<FlatFunction<T>>,
        arguments_flattened: &Vec<FlatParameter>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        expression: BooleanExpression<T>,
    ) -> FlatExpression<T> { // those will be booleans in the future
        match expression {
            BooleanExpression::Identifier(x) => FlatExpression::Identifier(self.bijection.get_by_left(&x).unwrap().clone()),
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
                statements_flattened
                    .push(FlatStatement::Definition(lhs_id, lhs_flattened));

                // check that lhs and rhs are within the right range, ie, their last two bits are zero

                // lhs
                {
                    // define variables for the bits
                    let lhs_bits: Vec<FlatVariable> = (0..self.bits).map(|_| self.use_sym()).collect();
                    
                    // add a directive to get the bits
                    statements_flattened.push(FlatStatement::Directive(DirectiveStatement::new(
                        lhs_bits.clone(),
                        Helper::Rust(RustHelper::Bits),
                        vec![lhs_id]
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

                    statements_flattened
                        .push(FlatStatement::Condition(
                                FlatExpression::Identifier(lhs_id), 
                                lhs_sum
                            )
                        );
                }

                // rhs
                let rhs_id = self.use_sym();
                statements_flattened
                    .push(FlatStatement::Definition(rhs_id, rhs_flattened));

                // rhs
                {
                    // define variables for the bits
                    let rhs_bits: Vec<FlatVariable> = (0..self.bits).map(|_| self.use_sym()).collect();

                    // add a directive to get the bits
                    statements_flattened.push(FlatStatement::Directive(DirectiveStatement::new(
                        rhs_bits.clone(),
                        Helper::Rust(RustHelper::Bits),
                        vec![rhs_id]
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

                    statements_flattened
                        .push(FlatStatement::Condition(
                                FlatExpression::Identifier(rhs_id), 
                                rhs_sum
                            )
                        );
                }

                // sym = (lhs * 2) - (rhs * 2)
                let subtraction_result_id = self.use_sym();

                statements_flattened.push(FlatStatement::Definition(
                    subtraction_result_id,
                    FlatExpression::Sub(
                        box FlatExpression::Mult(box FlatExpression::Number(T::from(2)), box FlatExpression::Identifier(lhs_id)),
                        box FlatExpression::Mult(box FlatExpression::Number(T::from(2)), box FlatExpression::Identifier(rhs_id)),
                    ),
                ));

                // define variables for the bits
                let sub_bits: Vec<FlatVariable> = (0..self.bits).map(|_| self.use_sym()).collect();

                // add a directive to get the bits
                statements_flattened.push(FlatStatement::Directive(DirectiveStatement::new(
                    sub_bits.clone(),
                    Helper::Rust(RustHelper::Bits),
                    vec![subtraction_result_id]
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

                statements_flattened
                    .push(FlatStatement::Condition(
                            FlatExpression::Identifier(subtraction_result_id), 
                            expr
                        )
                    );

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

                let name_x = self.use_sym();
                let name_y = self.use_sym();
                let name_m = self.use_sym();
                let name_1_y = self.use_sym();

                let x = self.flatten_field_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    FieldElementExpression::Sub(box lhs, box rhs),
                );

                statements_flattened.push(FlatStatement::Definition(name_x, x));
                statements_flattened.push(
                    FlatStatement::Directive(DirectiveStatement {
                        outputs: vec![name_y, name_m],
                        inputs: vec![name_x],
                        helper: Helper::Rust(RustHelper::ConditionEq)
                    })
                );
                statements_flattened.push(FlatStatement::Condition(
                    FlatExpression::Identifier(name_y),
                    FlatExpression::Mult(box FlatExpression::Identifier(name_x), box FlatExpression::Identifier(name_m)),
                ));
                statements_flattened.push(FlatStatement::Definition(
                    name_1_y,
                    FlatExpression::Sub(box FlatExpression::Number(T::one()), box FlatExpression::Identifier(name_y)),
                ));
                statements_flattened.push(FlatStatement::Condition(
                    FlatExpression::Number(T::zero()),
                    FlatExpression::Mult(box FlatExpression::Identifier(name_1_y), box FlatExpression::Identifier(name_x)),
                ));

                FlatExpression::Identifier(name_1_y)
            },
            BooleanExpression::Value(b) => {
                FlatExpression::Number(match b {
                    true => T::from(1),
                    false => T::from(0)
                })
            }
            _ => unimplemented!(),
        }
    }

    fn flatten_function_call<T: Field>(
        &mut self,
        functions_flattened: &Vec<FlatFunction<T>>,
        arguments_flattened: &Vec<FlatParameter>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        id: &String,
        return_types: Vec<Type>,
        param_expressions: &Vec<TypedExpression<T>>
    ) -> FlatExpressionList<T> {

        let passed_signature = Signature::new()
            .inputs(param_expressions.into_iter().map(|e| e.get_type()).collect())
            .outputs(return_types);

        for funct in functions_flattened {
            if funct.id == *id && funct.signature == passed_signature {
                // funct is now the called function

                // Stores prefixed variables

                let mut replacement_map = DirectSubstitution::new();

                // Handle complex parameters and assign values:
                // Rename Parameters, assign them to values in call. Resolve complex expressions with definitions
                for (i, param_expr) in param_expressions.clone().into_iter().enumerate() {
                    let rhs = self.flatten_expression(
                            functions_flattened,
                            arguments_flattened,
                            statements_flattened,
                            param_expr,
                        ).apply_recursive_substitution(&self.substitution);

                    let new_var = self.issue_new_variable();
                    statements_flattened
                        .push(FlatStatement::Definition(new_var, rhs));
                    replacement_map.insert(funct.arguments.get(i).unwrap().id.clone(), new_var);
                }

                // Ensure Renaming and correct returns:
                // add all flattened statements, adapt return statement
                for stat in funct.statements.clone() {
                    match stat {
                        // set return statements right sidreturne as expression result
                        FlatStatement::Return(list) => {
                            return FlatExpressionList {
                                expressions: list.expressions.into_iter().map(|x| x.apply_direct_substitution(&replacement_map)).collect()
                            }
                        },
                        FlatStatement::Definition(var, rhs) => {
                            let new_var = self.issue_new_variable();
                            replacement_map.insert(var, new_var);
                            let new_rhs = rhs.apply_direct_substitution(&replacement_map);
                            statements_flattened.push(
                                FlatStatement::Definition(new_var, new_rhs)
                            );
                        },
                        FlatStatement::Condition(lhs, rhs) => {
                            let new_lhs = lhs.apply_direct_substitution(&replacement_map);
                            let new_rhs = rhs.apply_direct_substitution(&replacement_map);
                            statements_flattened
                                .push(FlatStatement::Condition(new_lhs, new_rhs));
                        },
                        FlatStatement::Directive(d) => {
                            let new_outputs = d.outputs.into_iter().map(|o| {
                                let new_o = self.issue_new_variable();
                                replacement_map.insert(o, new_o);
                                new_o
                            }).collect();
                            let new_inputs = d.inputs.iter().map(|i| replacement_map.get(&i).unwrap()).collect();
                            statements_flattened.push(
                                FlatStatement::Directive(
                                    DirectiveStatement {
                                        outputs: new_outputs,
                                        inputs: new_inputs,
                                        helper: d.helper.clone()
                                    }
                                )
                            )
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
    ) -> FlatExpression<T> {
        match expr {
            TypedExpression::FieldElement(e) => 
                self.flatten_field_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    e,
                ),
            TypedExpression::Boolean(e) => 
                self.flatten_boolean_expression(
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
            FieldElementExpression::Identifier(x) => FlatExpression::Identifier(self.bijection.get_by_left(&x).unwrap().clone()),
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
                    statements_flattened
                        .push(FlatStatement::Definition(id, left_flattened));
                    FlatExpression::Identifier(id)
                };
                let new_right = if right_flattened.is_linear() {
                    right_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened
                        .push(FlatStatement::Definition(id, right_flattened));
                    FlatExpression::Identifier(id)
                };
                FlatExpression::Add(box new_left, box new_right)
            },
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
                    statements_flattened
                        .push(FlatStatement::Definition(id, left_flattened));
                    FlatExpression::Identifier(id)
                };
                let new_right = if right_flattened.is_linear() {
                    right_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened
                        .push(FlatStatement::Definition(id, right_flattened));
                    FlatExpression::Identifier(id)
                };
                FlatExpression::Sub(box new_left, box new_right)
            },
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
                    if let FlatExpression::Sub(..) = left_flattened {
                        let id = self.use_sym();
                        statements_flattened
                            .push(FlatStatement::Definition(id, left_flattened));
                        FlatExpression::Identifier(id)
                    } else {
                        left_flattened
                    }
                } else {
                    let id = self.use_sym();
                    statements_flattened
                        .push(FlatStatement::Definition(id, left_flattened));
                    FlatExpression::Identifier(id)
                };
                let new_right = if right_flattened.is_linear() {
                    if let FlatExpression::Sub(..) = right_flattened {
                        let id = self.use_sym();
                        statements_flattened
                            .push(FlatStatement::Definition(id, right_flattened));
                        FlatExpression::Identifier(id)
                    } else {
                        right_flattened
                    }
                } else {
                    let id = self.use_sym();
                    statements_flattened
                        .push(FlatStatement::Definition(id, right_flattened));
                    FlatExpression::Identifier(id)
                };
                FlatExpression::Mult(box new_left, box new_right)
            },
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
                let new_left = {
                    let id = self.use_sym();
                    statements_flattened
                        .push(FlatStatement::Definition(id, left_flattened));
                    FlatExpression::Identifier(id)
                };
                let new_right = {
                    let id = self.use_sym();
                    statements_flattened
                        .push(FlatStatement::Definition(id, right_flattened));
                    FlatExpression::Identifier(id)
                };
                FlatExpression::Div(box new_left, box new_right)
            },
            FieldElementExpression::Pow(box base, box exponent) => {
                match exponent {
                    FieldElementExpression::Number(ref e) => {
                        // flatten the base expression
                        let base_flattened = self.flatten_field_expression(
                                functions_flattened,
                                arguments_flattened,
                                statements_flattened,
                                base.clone(),
                            ).apply_recursive_substitution(&self.substitution);

                        // we require from the base to be linear
                        // TODO change that
                        assert!(base_flattened.is_linear());

                        match e {
                            // flatten(base ** 1) == flatten(base)
                            e if *e == T::one() => {
                                base_flattened
                            },
                            // flatten(base ** 2) == flatten(base) * flatten(base)
                            // in this case, no need to define an intermediate variable
                            // as if a is linear, a ** 2 quadratic
                            e if *e == T::from(2) => {
                                FlatExpression::Mult(box base_flattened.clone(), box base_flattened)
                            },
                            // flatten(base ** n) = flatten(base) * flatten(base ** (n-1))
                            e => {
                                // flatten(base ** (n-1))
                                let tmp_expression = self.flatten_field_expression(
                                    functions_flattened,
                                    arguments_flattened,
                                    statements_flattened,
                                    FieldElementExpression::Pow(
                                        box base,
                                        box FieldElementExpression::Number(e.clone() - T::one()),
                                    ),
                                ).apply_recursive_substitution(&self.substitution);

                                let id = self.use_sym();

                                statements_flattened.push(
                                    FlatStatement::Definition(id, tmp_expression));
                            
                                FlatExpression::Mult(
                                    box FlatExpression::Identifier(id),
                                    box base_flattened,
                                )
                            }
                        }
                    },
                    _ => panic!("Expected number as pow exponent"),
                }
            },
            FieldElementExpression::IfElse(box condition, box consequent, box alternative) => {
                self.flatten_function_call(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    &"_if_else_field".to_string(),
                    vec![Type::FieldElement],
                    &vec![condition.into(), consequent.into(), alternative.into()],
                ).expressions[0].clone()

            },
            FieldElementExpression::FunctionCall(ref id, ref param_expressions) => {
                let exprs_flattened = self.flatten_function_call(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    id,
                    vec![Type::FieldElement],
                    param_expressions
                );
                assert!(exprs_flattened.expressions.len() == 1); // outside of MultipleDefinition, FunctionCalls must return a single value
                exprs_flattened.expressions[0].clone()
            }
        }
    }

    pub fn flatten_statement<T: Field>(
        &mut self,
        functions_flattened: &mut Vec<FlatFunction<T>>,
        arguments_flattened: &Vec<FlatParameter>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        stat: TypedStatement<T>,
    ) {
        match stat {
            TypedStatement::Return(exprs) => {
                let flat_expressions = exprs.into_iter().map(|expr| 
                    self.flatten_expression(
                        functions_flattened,
                        arguments_flattened,
                        statements_flattened,
                        expr
                    ).apply_recursive_substitution(&self.substitution)
                ).collect();

                statements_flattened.push(
                    FlatStatement::Return(
                        FlatExpressionList {
                            expressions: flat_expressions
                        }
                    )
                );
            }
            TypedStatement::Declaration(_) => {
                // declarations have already been checked
                ()
            }
            TypedStatement::Definition(v, expr) => {

                // define n variables with n the number of primitive types for v_type
                // assign them to the n primitive types for expr

                let rhs = self.flatten_expression(
                        functions_flattened,
                        arguments_flattened,
                        statements_flattened,
                        expr
                    ).apply_recursive_substitution(&self.substitution);

                let var = self.use_variable(&v.id);
                // handle return of function call
                let var_to_replace = self.get_latest_var_substitution(&v.id);
                if !(var == var_to_replace) && self.variables.contains(&var_to_replace) && !self.substitution.contains_key(&var_to_replace){
                    self.substitution.insert(var_to_replace.clone(),var.clone());
                }

                statements_flattened.push(FlatStatement::Definition(var, rhs));
            }
            TypedStatement::Condition(expr1, expr2) => {

                // flatten expr1 and expr2 to n flattened expressions with n the number of primitive types for expr1
                // add n conditions to check equality of the n expressions

                match (expr1, expr2) {
                    (TypedExpression::FieldElement(e1), TypedExpression::FieldElement(e2)) => {

                        let (lhs, rhs) =
                            (
                                self.flatten_field_expression(
                                    functions_flattened,
                                    arguments_flattened,
                                    statements_flattened,
                                    e1
                                ).apply_recursive_substitution(&self.substitution),
                                self.flatten_field_expression(
                                    functions_flattened,
                                    arguments_flattened,
                                    statements_flattened,
                                    e2,
                                ).apply_recursive_substitution(&self.substitution),
                            );

                        if lhs.is_linear() {
                            statements_flattened.push(FlatStatement::Condition(lhs, rhs));
                        } else if rhs.is_linear() {
                            // swap so that left side is linear
                            statements_flattened.push(FlatStatement::Condition(rhs, lhs));
                        } else {
                            unimplemented!()
                        }

                    },
                    (TypedExpression::Boolean(e1), TypedExpression::Boolean(e2)) => {
                        
                        let (lhs, rhs) =
                            (
                                self.flatten_boolean_expression(
                                    functions_flattened,
                                    arguments_flattened,
                                    statements_flattened,
                                    e1
                                ).apply_recursive_substitution(&self.substitution),
                                self.flatten_boolean_expression(
                                    functions_flattened,
                                    arguments_flattened,
                                    statements_flattened,
                                    e2,
                                ).apply_recursive_substitution(&self.substitution),
                            );

                        if lhs.is_linear() {
                            statements_flattened.push(FlatStatement::Condition(lhs, rhs));
                        } else if rhs.is_linear() {
                            // swap so that left side is linear
                            statements_flattened.push(FlatStatement::Condition(rhs, lhs));
                        } else {
                            unimplemented!()
                        }
                    },
                    _ => panic!("non matching types in condition should have been caught at semantic stage")
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
                        let rhs_flattened = self.flatten_function_call(
                            functions_flattened,
                            arguments_flattened,
                            statements_flattened,
                            &fun_id,
                            var_types,
                            &exprs,
                        ).apply_recursive_substitution(&self.substitution);

                        // this will change for types that have multiple underlying fe
                        for (i, v) in vars.into_iter().enumerate() {
                            let var = self.use_variable(&v.id);
                            // handle return of function call
                            let var_to_replace = self.get_latest_var_substitution(&v.id);
                            if !(var == var_to_replace) && self.variables.contains(&var_to_replace) && !self.substitution.contains_key(&var_to_replace){
                                self.substitution.insert(var_to_replace.clone(),var.clone());
                            }
                            statements_flattened.push(FlatStatement::Definition(var, rhs_flattened.expressions[i].clone()));
                        }
                    },
                }
            },
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
        self.substitution = DirectSubstitution::new();

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
                        private: arg.private
                    });
                },
                Type::Boolean => {
                    arguments_flattened.push(FlatParameter {
                        id: self.use_variable(&arg.id.id), 
                        private: arg.private
                    });
                },
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
            signature: funct.signature
        }
    }

    /// Returns a flattened `Prog`ram based on the given `prog`.
    ///
    /// # Arguments
    ///
    /// * `prog` - `Prog`ram that will be flattened.
    pub fn flatten_program<T: Field>(&mut self, prog: TypedProg<T>) -> FlatProg<T> {
        let mut functions_flattened = Vec::new();

        self.load_stdlib(&mut functions_flattened);

        for func in prog.imported_functions {
            functions_flattened.push(func);
        }

        for func in prog.functions {
            let flattened_func = self.flatten_function(&mut functions_flattened, func);
            functions_flattened.push(flattened_func);
        }

        FlatProg {
            functions: functions_flattened
        }
    }


    /// Checks if the given name is a not used variable and returns a fresh variable.
    /// # Arguments
    ///
    /// * `name` - a String that holds the name of the variable
    fn use_variable(&mut self, name: &String) -> FlatVariable {
        // issue the variable we'll use
        let var = self.issue_new_variable();

        // {
        //     // we check if the name was already given a variable
        //     let id = self.bijection.get_by_left(name);

        //     match id {
        //         Some(id) => {
        //             // the name was already registered. We need to find its latest substitution
        //             let mut id = *id;
        //             // loop {
        //             //     match self.substitution.get(&id) {
        //             //         Some(x) => id = x,
        //             //         None => break,
        //             //     }
        //             // }
        //             // now `id` is the latest substitution of `name`

        //             // link it to the previous one
        //             //assert!(!(id == var));
        //             //self.bijection.insert(name.to_string(), var);
        //         },
        //         None => {

        //         }
        //     }
        // }

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
    use field::FieldPrime;
    use types::Type;
    use types::Signature;
    use absy::variable::Variable;

    #[test]
    fn multiple_definition() {

        // def foo()
        //     return 1, 2
        // def main()
        //     a, b = foo()

        let mut flattener = Flattener::new(FieldPrime::get_required_bits());
        let mut functions_flattened = vec![
            FlatFunction {
                id: "foo".to_string(),
                arguments: vec![],
                statements: vec![FlatStatement::Return(
                    FlatExpressionList {
                        expressions: vec![
                            FlatExpression::Number(FieldPrime::from(1)),
                            FlatExpression::Number(FieldPrime::from(2))
                        ]
                    }
                )],
                signature: Signature::new()
                    .inputs(vec![])
                    .outputs(vec![Type::FieldElement, Type::FieldElement])
            }
        ];
        let arguments_flattened = vec![];
        let mut statements_flattened = vec![];
        let statement = TypedStatement::MultipleDefinition(
            vec![
                Variable::field_element("a".to_string()),
                Variable::field_element("b".to_string())
            ],
            TypedExpressionList::FunctionCall("foo".to_string(), vec![], vec![Type::FieldElement, Type::FieldElement])
        );

        flattener.flatten_statement(
            &mut functions_flattened,
            &arguments_flattened,
            &mut statements_flattened,
            statement,
        );

        let a = FlatVariable::new(0);

        assert_eq!(
            statements_flattened[0]
            ,
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
        let mut functions_flattened = vec![
            FlatFunction {
                id: "dup".to_string(),
                arguments: vec![FlatParameter { id: a, private: true }],
                statements: vec![FlatStatement::Return(
                    FlatExpressionList {
                        expressions: vec![
                            FlatExpression::Identifier(a),
                            FlatExpression::Identifier(a),
                        ]
                    }
                )],
                signature: Signature::new()
                    .inputs(vec![Type::FieldElement])
                    .outputs(vec![Type::FieldElement, Type::FieldElement])
            }
        ];
        let statement = TypedStatement::MultipleDefinition(
            vec![
                Variable::field_element("a".to_string()),
                Variable::field_element("b".to_string())
            ],
            TypedExpressionList::FunctionCall("dup".to_string(), vec![TypedExpression::FieldElement(FieldElementExpression::Number(FieldPrime::from(2)))], vec![Type::FieldElement, Type::FieldElement])
        );

        let fun = TypedFunction {
            id: String::from("main"),
            arguments: vec![],
            statements: vec![statement],
            signature: Signature {
                inputs: vec![],
                outputs: vec![]
            }
        };

        let f = flattener.flatten_function(
            &mut functions_flattened,
            fun,
        );

        let a = FlatVariable::new(0);

        assert_eq!(
            f.statements[0]
            ,
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
        let mut functions_flattened = vec![
            FlatFunction {
                id: "foo".to_string(),
                arguments: vec![],
                statements: vec![FlatStatement::Return(
                    FlatExpressionList {
                        expressions: vec![
                            FlatExpression::Number(FieldPrime::from(1))
                        ]
                    }
                )],
                signature: Signature::new()
                    .inputs(vec![])
                    .outputs(vec![Type::FieldElement])
            }
        ];
        let arguments_flattened = vec![];
        let mut statements_flattened = vec![];
        let statement = TypedStatement::Definition(
            Variable::field_element("a".to_string()),
            TypedExpression::FieldElement(FieldElementExpression::FunctionCall("foo".to_string(), vec![]))
        );

        flattener.flatten_statement(
            &mut functions_flattened,
            &arguments_flattened,
            &mut statements_flattened,
            statement,
        );

        let a = FlatVariable::new(0);

        assert_eq!(
            statements_flattened[0]
            ,
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
                .outputs(vec![Type::FieldElement])
            ,
            arguments: vec![Parameter { id: Variable::field_element("a"), private: true }],
            statements: vec![
                TypedStatement::Definition(
                    Variable::field_element("a".to_string()), 
                    FieldElementExpression::Add(
                        box FieldElementExpression::Identifier("a".to_string()), 
                        box FieldElementExpression::Number(FieldPrime::from(1))
                    ).into()
                ),
                TypedStatement::Return(
                    vec![FieldElementExpression::Number(FieldPrime::from(1)).into()]
                )
            ],
        };

        let flat_funct = flattener.flatten_function(
            &mut functions_flattened,
            funct,
        );

        let a = FlatVariable::new(0);
        let a_0 = FlatVariable::new(1);

        assert_eq!(
            flat_funct.statements[0],
            FlatStatement::Definition(a_0, FlatExpression::Add(box FlatExpression::Identifier(a), box FlatExpression::Number(FieldPrime::from(1))))
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
                TypedStatement::Definition(Variable::field_element("a"), FieldElementExpression::Number(FieldPrime::from(3)).into()),
                TypedStatement::Return(vec![
                    FieldElementExpression::Identifier(String::from("a")).into()
                    ]
                )
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![Type::FieldElement]
            }
        };

        let main = TypedFunction {
            id: String::from("main"),
            arguments: vec![],
            statements: vec![
                TypedStatement::Return(vec![
                        FieldElementExpression::FunctionCall(String::from("foo"), vec![]).into()
                    ]
                )
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![Type::FieldElement]
            }
        };

        let mut flattener = Flattener::new(FieldPrime::get_required_bits());

        let foo_flattened = flattener.flatten_function(
            &mut vec![],
            foo
        );

        let expected = FlatFunction {
            id: String::from("main"),
            arguments: vec![],
            statements: vec![
                FlatStatement::Definition(FlatVariable::new(0), FlatExpression::Number(FieldPrime::from(3))),
                FlatStatement::Return(FlatExpressionList { 
                    expressions: vec![FlatExpression::Identifier(FlatVariable::new(0))]
                })
            ],
            signature: Signature::new().outputs(vec![Type::FieldElement])
        };


        let main_flattened = flattener.flatten_function(
            &mut vec![foo_flattened],
            main
        );

        assert_eq!(main_flattened, expected);
    }


    #[test]
    fn powers() {
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
                TypedStatement::Definition(Variable::field_element("a"), FieldElementExpression::Number(FieldPrime::from(7)).into()),
                TypedStatement::Definition(Variable::field_element("b"), FieldElementExpression::Pow(box FieldElementExpression::Identifier(String::from("a")), box FieldElementExpression::Number(FieldPrime::from(4))).into()),
                TypedStatement::Return(vec![
                    FieldElementExpression::Identifier(String::from("b")).into()
                    ]
                )
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![Type::FieldElement]
            }
        };

        let mut flattener = Flattener::new(FieldPrime::get_required_bits());

        let expected = FlatFunction {
            id: String::from("main"),
            arguments: vec![],
            statements: vec![
                FlatStatement::Definition(FlatVariable::new(0), FlatExpression::Number(FieldPrime::from(7))),
                FlatStatement::Definition(FlatVariable::new(1), FlatExpression::Mult(box FlatExpression::Identifier(FlatVariable::new(0)), box FlatExpression::Identifier(FlatVariable::new(0)))),
                FlatStatement::Definition(FlatVariable::new(2), FlatExpression::Mult(box FlatExpression::Identifier(FlatVariable::new(1)), box FlatExpression::Identifier(FlatVariable::new(0)))),
                FlatStatement::Definition(FlatVariable::new(3), FlatExpression::Mult(box FlatExpression::Identifier(FlatVariable::new(2)), box FlatExpression::Identifier(FlatVariable::new(0)))),
                FlatStatement::Return(FlatExpressionList {
                    expressions: vec![
                        FlatExpression::Identifier(FlatVariable::new(3))
                    ]
                })                
            ],
            signature: Signature::new().outputs(vec![Type::FieldElement])
        };

        let flattened = flattener.flatten_function(
            &mut vec![],
            function
        );

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
                statements: vec![TypedStatement::Return(
                    vec![
                            TypedExpression::FieldElement(FieldElementExpression::Number(FieldPrime::from(1)))
                        ]
                )],
                signature: Signature::new()
                    .inputs(vec![])
                    .outputs(vec![Type::FieldElement])
                ,
            },
            TypedFunction {
                id: "foo".to_string(),
                arguments: vec![],
                statements: vec![TypedStatement::Return(
                        vec![
                            TypedExpression::FieldElement(FieldElementExpression::Number(FieldPrime::from(1))),
                            TypedExpression::FieldElement(FieldElementExpression::Number(FieldPrime::from(2)))
                        ]
                )],
                signature: Signature::new()
                    .inputs(vec![])
                    .outputs(vec![Type::FieldElement, Type::FieldElement])
                ,
            },
            TypedFunction {
                id: "main".to_string(),
                arguments: vec![],
                statements: vec![
                    TypedStatement::Definition(Variable::field_element("a".to_string()), TypedExpression::FieldElement(FieldElementExpression::FunctionCall("foo".to_string(), vec![]))),
                    TypedStatement::MultipleDefinition(vec![Variable::field_element("b".to_string()), Variable::field_element("c".to_string())], TypedExpressionList::FunctionCall("foo".to_string(), vec![], vec![Type::FieldElement, Type::FieldElement])),
                    TypedStatement::Return(
                        vec![TypedExpression::FieldElement(FieldElementExpression::Number(FieldPrime::from(1)))]
                    )
                ],
                signature: Signature::new()
                    .inputs(vec![])
                    .outputs(vec![Type::FieldElement])
                ,
            }
        ];

        flattener.flatten_program(
            TypedProg {
                functions: functions,
                imported_functions: vec![],
                imports: vec![]
            }
        );

        // shouldn't panic
    }

    #[test]
    fn if_else() {

        let expression = 
            FieldElementExpression::IfElse(
                box BooleanExpression::Eq(
                    box FieldElementExpression::Number(FieldPrime::from(32)),
                    box FieldElementExpression::Number(FieldPrime::from(4))
                ),
                box FieldElementExpression::Number(FieldPrime::from(12)),
                box FieldElementExpression::Number(FieldPrime::from(51)),
            );


        let mut functions_flattened = vec![];
        let mut flattener = Flattener::new(FieldPrime::get_required_bits());

        flattener.load_stdlib(&mut functions_flattened);

        flattener.flatten_field_expression(
            &functions_flattened,
            &vec![],
            &mut vec![],
            expression
        );
    }

    #[test]
    fn next_variable() {
        let mut flattener = Flattener::new(FieldPrime::get_required_bits());
        assert_eq!(FlatVariable::new(0), flattener.use_variable(&String::from("a")));
        assert_eq!(flattener.get_latest_var_substitution(&String::from("a")), FlatVariable::new(0));
        assert_eq!(FlatVariable::new(1), flattener.use_variable(&String::from("a")));
        assert_eq!(flattener.get_latest_var_substitution(&String::from("a")), FlatVariable::new(1));
        assert_eq!(FlatVariable::new(2), flattener.use_variable(&String::from("a")));
        assert_eq!(flattener.get_latest_var_substitution(&String::from("a")), FlatVariable::new(2));
    }
}
