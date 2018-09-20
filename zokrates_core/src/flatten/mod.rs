//! Module containing the `Flattener` to process a program that it is R1CS-able.
//!
//! @file flatten.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

const BINARY_SEPARATOR: &str = "_b";


use std::collections::{HashSet, HashMap};
use typed_absy::*;
use field::Field;
use flat_absy::*;
use flat_absy::flat_parameter::FlatParameter;
use flat_absy::flat_variable::FlatVariable;
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
pub struct Flattener {
    /// Number of bits needed to represent the maximum value.
    bits: usize,
    /// Vector containing all used variables while processing the program.
    variables: HashSet<FlatVariable>,
    /// Map of renamings for reassigned variables while processing the program.
    substitution: DirectSubstitution,
    /// Map of function id to invocation counter
    function_calls: HashMap<String, usize>,
    /// Index of the next introduced variable while processing the program.
    next_var_idx: usize,
    /// bijection for name <=> id
    bijection: BiMap<String, FlatVariable>
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
            function_calls: HashMap::new(),
            next_var_idx: 0,
            bijection: BiMap::new()
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
                    Variable::from("condition_as_field"),
                    FieldElementExpression::FunctionCall(
                        "_bool_to_field".to_string(), 
                        vec![
                            TypedExpression::FieldElement(
                                FieldElementExpression::Identifier("condition".to_string()))
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
            signature: Signature {
                inputs: vec![Type::Boolean, Type::FieldElement, Type::FieldElement],
                outputs: vec![Type::FieldElement]
            }
        };

        let ief = self.flatten_function(
            functions_flattened,
            ie,
        );
        functions_flattened.push(ief);
    }

    /// Returns (condition true, condition false) `Identifier`s for the given condition.
    /// condition true = 1, if `condition` is true, 0 else
    /// condition false = 1, if `condition` is false, 0 else
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `condition` - `Condition` that will be flattened.
    fn flatten_condition<T: Field>(
        &mut self,
        functions_flattened: &Vec<FlatFunction<T>>,
        arguments_flattened: &Vec<FlatParameter>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        condition: BooleanExpression<T>,
    ) -> BooleanExpression<T> { // those will be booleans in the future
        match condition {
            BooleanExpression::Lt(box lhs, box rhs) => {

                // We know from semantic checking that lhs and rhs have the same type
                // What the condition will flatten to depends on that type

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

                // rhs
                let rhs_id = self.use_sym();
                statements_flattened
                    .push(FlatStatement::Definition(rhs_id, rhs_flattened));

                // check that lhs and rhs are within the right range, ie, their last two bits are zero

                // lhs
                {
                    // bitness checks
                    for i in 0..self.bits - 2 {
                        let new_id = self.use_binary_variable(&lhs_id, i);
                        statements_flattened.push(FlatStatement::Definition(
                            new_id,
                            FlatExpression::Mult(
                                box FlatExpression::Identifier(new_id.clone()),
                                box FlatExpression::Identifier(new_id),
                            ),
                        ));
                    }

                    // bit decomposition check
                    let mut lhs_sum = FlatExpression::Number(T::from(0));

                    for i in 0..self.bits - 2 {
                        lhs_sum = FlatExpression::Add(
                            box lhs_sum,
                            box FlatExpression::Mult(
                                box FlatExpression::Identifier(self.use_binary_variable(&lhs_id, i)),
                                box FlatExpression::Number(T::from(2).pow(i)),
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
                {
                    // bitness checks
                    for i in 0..self.bits - 2 {
                        let new_id = self.use_binary_variable(&lhs_id, i);
                        statements_flattened.push(FlatStatement::Definition(
                            new_id,
                            FlatExpression::Mult(
                                box FlatExpression::Identifier(new_id),
                                box FlatExpression::Identifier(new_id),
                            ),
                        ));
                    }

                    // bit decomposition check
                    let mut rhs_sum = FlatExpression::Number(T::from(0));

                    for i in 0..self.bits - 2 {
                        rhs_sum = FlatExpression::Add(
                            box rhs_sum,
                            box FlatExpression::Mult(
                                box FlatExpression::Identifier(self.use_binary_variable(&rhs_id, i)),
                                box FlatExpression::Number(T::from(2).pow(i)),
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

                // sym_b{i} = sym_b{i}**2  (bitness checks)
                for i in 0..self.bits {
                    let new_id = self.use_binary_variable(&subtraction_result_id, i);
                    statements_flattened.push(FlatStatement::Definition(
                        new_id,
                        FlatExpression::Mult(
                            box FlatExpression::Identifier(new_id),
                            box FlatExpression::Identifier(new_id),
                        ),
                    ));
                }

                // sum(sym_b{i} * 2**i)
                let mut expr = FlatExpression::Number(T::from(0));

                for i in 0..self.bits {
                    expr = FlatExpression::Add(
                        box expr,
                        box FlatExpression::Mult(
                            box FlatExpression::Identifier(self.use_binary_variable(&subtraction_result_id, i)),
                            box FlatExpression::Number(T::from(2).pow(i)),
                        ),
                    );
                }

                statements_flattened
                    .push(FlatStatement::Condition(
                            FlatExpression::Identifier(subtraction_result_id), 
                            expr
                        )
                    );

                // rename output to avoid conflicts with suffixes
                let cond_true_id = self.use_sym();
                statements_flattened
                    .push(FlatStatement::Definition(
                        cond_true_id,
                        FlatExpression::Identifier(FlatVariable::binary(subtraction_result_id.id, 0)))
                    );

                self.next_var_idx += 1;

                // we need to return string-based variables for the rest of flattening, so we use the bijection
                BooleanExpression::Identifier(self.bijection.get_by_right(&cond_true_id).unwrap().to_string())
            }
            BooleanExpression::Eq(box lhs, box rhs) => {

                // We know from semantic checking that lhs and rhs have the same type
                // What the condition will flatten to depends on that type

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

                BooleanExpression::Identifier(self.bijection.get_by_right(&name_1_y).unwrap().to_string())
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
        return_count: usize,
        param_expressions: &Vec<TypedExpression<T>>
    ) -> FlatExpressionList<T> {
        for funct in functions_flattened {
            if funct.id == *id && funct.arguments.len() == (*param_expressions).len() && funct.return_count == return_count {
                // funct is now the called function

                // Idea: variables are given a prefix.
                // It consists of the function name followed by a call counter value
                // e.g.: add_1_a_2

                // Stores prefixed variables

                let mut replacement_map = DirectSubstitution::new();

                // build prefix
                match self.function_calls.clone().get(&funct.id) {
                    Some(val) => {
                        self.function_calls.insert(funct.id.clone(),val+1);
                    }
                    None => {
                        self.function_calls.insert(funct.id.clone(),1);
                    }
                }
                let prefix = format!("{}_i{}o{}_{}_", funct.id.clone(), funct.arguments.len(), funct.return_count, self.function_calls.get(&funct.id).unwrap());

                // Handle complex parameters and assign values:
                // Rename Parameters, assign them to values in call. Resolve complex expressions with definitions
                for (i, param_expr) in param_expressions.clone().into_iter().enumerate() {
                    let new_var;

                    match param_expr {
                        TypedExpression::FieldElement(e) => {

                            // for field elements, flatten the input and assign it to a new variable
                            let rhs = self.flatten_field_expression(
                                functions_flattened,
                                arguments_flattened,
                                statements_flattened,
                                e,
                            ).apply_substitution(&self.substitution);
                            new_var = self.use_variable(&format!("{}param_{}", &prefix, i));
                            statements_flattened
                                .push(FlatStatement::Definition(new_var, rhs));
                        },
                        TypedExpression::Boolean(e) => {
                            match e {
                                BooleanExpression::Identifier(id) => {
                                    new_var = self.use_variable(&format!("{}param_{}", &prefix, i));
                                    // a bit hacky for now, to be removed when flatten_condition returns a flatexpression
                                    // basically extracted the bit of apply_substitution that handles identifiers
                                    let mut id = id;
                                    loop {
                                        match self.substitution.get(&self.bijection.get_by_left(&id).unwrap()) {
                                            Some(x) => id = x.to_string(),
                                            None => break,
                                        }
                                    }

                                    statements_flattened
                                        .push(FlatStatement::Definition(new_var, FlatExpression::Identifier(self.bijection.get_by_left(&id).unwrap().clone())));
                                },
                                _ => panic!("A boolean argument to a function has to be a identifier")
                            }
                        }
                    }
                    replacement_map.insert(FlatVariable::new(funct.arguments.get(i).unwrap().id.id), new_var);
                }

                // Ensure Renaming and correct returns:
                // add all flattened statements, adapt return statement
                for stat in funct.statements.clone() {
                    match stat {
                        // set return statements right side as expression result
                        FlatStatement::Return(list) => {
                            return FlatExpressionList {
                                expressions: list.expressions.into_iter().map(|x| x.apply_substitution(&replacement_map)).collect()
                            }
                        },
                        FlatStatement::Definition(var, rhs) => {
                            //let var_name = self.bijection.get_by_right(&var).unwrap();
                            let new_var = self.use_variable(&format!("{}{}", prefix, "dummy"));
                            replacement_map.insert(var, new_var);
                            let new_rhs = rhs.apply_substitution(&replacement_map);
                            statements_flattened.push(
                                FlatStatement::Definition(new_var, new_rhs)
                            );
                        },
                        FlatStatement::Condition(lhs, rhs) => {
                            let new_lhs = lhs.apply_substitution(&replacement_map);
                            let new_rhs = rhs.apply_substitution(&replacement_map);
                            statements_flattened
                                .push(FlatStatement::Condition(new_lhs, new_rhs));
                        },
                        FlatStatement::Directive(d) => {
                            let new_outputs = d.outputs.into_iter().map(|o| {
                            //let var_name = self.bijection.get_by_right(&o).unwrap();
                            let new_o = self.use_variable(&format!("{}{}", prefix, "dummy"));
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
            "TypedFunction definition for function {} with {:?} argument(s) not found.",
            id,
            param_expressions
        );
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
                // TODO currently assuming that base is number or variable
                match exponent {
                    FieldElementExpression::Number(ref x) if x > &T::one() => match base {
                        FieldElementExpression::Identifier(ref var) => {
                            let id = if x > &T::from(2) {
                                let tmp_expression = self.flatten_field_expression(
                                    functions_flattened,
                                    arguments_flattened,
                                    statements_flattened,
                                    FieldElementExpression::Pow(
                                        box FieldElementExpression::Identifier(var.to_string()),
                                        box FieldElementExpression::Number(x.clone() - T::one()),
                                    ),
                                );
                                let id = self.use_sym();
                                statements_flattened.push(
                                    FlatStatement::Definition(id, tmp_expression),
                                );
                                id
                            } else {
                                self.bijection.get_by_left(&var).unwrap().clone()
                            };
                            FlatExpression::Mult(
                                box FlatExpression::Identifier(id),
                                box FlatExpression::Identifier(self.bijection.get_by_left(&var).unwrap().clone()),
                            )
                        }
                        FieldElementExpression::Number(var) => FlatExpression::Mult(box FlatExpression::Number(var.clone()), box FlatExpression::Number(var)),
                        _ => panic!("Only variables and numbers allowed in pow base"),
                    },
                    _ => panic!("Expected number > 1 as pow exponent"),
                }
            },
            FieldElementExpression::IfElse(box condition, box consequent, box alternative) => {
                let condition = self.flatten_condition(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    condition,
                );

                self.flatten_function_call(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    &"_if_else_field".to_string(),
                    1,
                    &vec![condition.into(), consequent.into(), alternative.into()],
                ).expressions[0].clone()
            },
            FieldElementExpression::FunctionCall(ref id, ref param_expressions) => {
                let exprs_flattened = self.flatten_function_call(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    id,
                    1,
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

                let flat_expressions = exprs.into_iter().map(|expr| {
                    match expr {
                        TypedExpression::FieldElement(e) => {
                            self.flatten_field_expression(
                                functions_flattened,
                                arguments_flattened,
                                statements_flattened,
                                e,
                            ).apply_substitution(&self.substitution)
                        },
                        _ => panic!("Functions can only return expressions of type FieldElement")
                    }
                }).collect();

                statements_flattened.push(
                    FlatStatement::Return(
                        FlatExpressionList {
                            expressions: flat_expressions
                        }
                    )
                );
            }
            TypedStatement::Definition(v, expr) => {

                // define n variables with n the number of primitive types for v_type
                // assign them to the n primitive types for expr

                match expr {
                    TypedExpression::FieldElement(expr) => {
                        let rhs = self.flatten_field_expression(
                            functions_flattened,
                            arguments_flattened,
                            statements_flattened,
                            expr,
                        ).apply_substitution(&self.substitution);
                        let var = self.use_variable(&v.id);
                        // handle return of function call
                        let var_to_replace = self.get_latest_var_substitution(&v.id);
                        if !(var == var_to_replace) && self.variables.contains(&var_to_replace) && !self.substitution.contains_key(&var_to_replace){
                            self.substitution.insert(var_to_replace.clone(),var.clone());
                        }

                        statements_flattened.push(FlatStatement::Definition(var, rhs));
                    },
                    _ => panic!("Definitions must have type FieldElement")
                }
            }
            TypedStatement::Condition(expr1, expr2) => {

                // flatten expr1 and expr2 to n flattened expressions with n the number of primitive types for expr1
                // add n conditions to check equality of the n expressions

                match (expr1, expr2) {
                    (TypedExpression::FieldElement(e1), TypedExpression::FieldElement(e2)) => {
                        
                        let (lhs, rhs) = if e1.is_linear() {
                            (
                                self.flatten_field_expression(
                                    functions_flattened,
                                    arguments_flattened,
                                    statements_flattened,
                                    e1
                                ).apply_substitution(&self.substitution),
                                self.flatten_field_expression(
                                    functions_flattened,
                                    arguments_flattened,
                                    statements_flattened,
                                    e2,
                                ).apply_substitution(&self.substitution),
                            )
                        } else if e2.is_linear() {
                            (
                                self.flatten_field_expression(
                                    functions_flattened,
                                    arguments_flattened,
                                    statements_flattened,
                                    e2,
                                ).apply_substitution(&self.substitution),
                                self.flatten_field_expression(
                                    functions_flattened,
                                    arguments_flattened,
                                    statements_flattened,
                                    e1,
                                ).apply_substitution(&self.substitution),
                            )
                        } else {
                            unimplemented!()
                        };
                        statements_flattened.push(FlatStatement::Condition(lhs, rhs));
                    },
                    _ => panic!("Conditions (Assertions) must be applied to expressions of type FieldElement")
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
                
                match rhs {
                    TypedExpressionList::FunctionCall(fun_id, exprs, types) => {
                        let rhs_flattened = self.flatten_function_call(
                            functions_flattened,
                            arguments_flattened,
                            statements_flattened,
                            &fun_id,
                            vars.len(),
                            &exprs,
                        ).apply_substitution(&self.substitution);

                        for (i, v) in vars.into_iter().enumerate() {
                            let var_type = &types[i];

                            match var_type {
                                Type::FieldElement => {
                                    let var = self.use_variable(&v.id);
                                    // handle return of function call
                                    let var_to_replace = self.get_latest_var_substitution(&v.id);
                                    if !(var == var_to_replace) && self.variables.contains(&var_to_replace) && !self.substitution.contains_key(&var_to_replace){
                                        self.substitution.insert(var_to_replace, var);
                                    }
                                    statements_flattened.push(FlatStatement::Definition(var, rhs_flattened.expressions[i].clone()));
                                },
                                _ => panic!("MultipleDefinition has to define expressions of type FieldElement")
                            }
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

        // the flattened return count is the sum of the primitive elements for each type returned
        let return_count = funct.signature.outputs.iter().map(|output_type| output_type.get_primitive_count()).fold(0, |acc, x| acc + x);

        FlatFunction {
            id: funct.id.clone(),
            arguments: arguments_flattened,
            statements: statements_flattened,
            return_count: return_count,
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
    /// * `name` - A String that holds the name of the variable
    fn use_variable(&mut self, name: &String) -> FlatVariable {
        self.next_var_idx += 1;
        
        let var = {
            let id = self.bijection.get_by_left(name);

            match id {
                Some(id) => {
                    // the name was already registered. We need to find its latest substitution
                    let mut id = *id;
                    loop {
                        match self.substitution.get(&id) {
                            Some(x) => id = x,
                            None => break,
                        }
                    }
                    // now `id` is the latest substitution of `name`
                    // introduce a new variable with the current index
                    let var = FlatVariable::new(self.next_var_idx);
                    // link it to the previous one
                    self.substitution.insert(id, var);
                    // return the new var
                    var
                },
                None => {
                    // the name was not already registered.
                    // register it
                    let var = FlatVariable::new(self.next_var_idx);
                    var
                }
            }
        };

        self.bijection.insert(name.to_string(), var);

        var
    }

    fn use_binary_variable(&mut self, var: &FlatVariable, bit: usize) -> FlatVariable {
        FlatVariable {
            binary: Some(bit),
            ..var.clone()
        }
    }

    fn use_sym(&mut self) -> FlatVariable {
        self.next_var_idx += 1;

        let name = format!("sym_{}", self.next_var_idx);
        let var = FlatVariable::new(self.next_var_idx);
        self.bijection.insert(name, var);
        var
    }

    fn get_latest_var_substitution(&mut self, name: &String) -> FlatVariable {
        let mut latest_var = self.bijection.get_by_left(name).unwrap().clone();
        loop {
            match self.substitution.get(&latest_var) {
                Some(x) => latest_var = x,
                None => return latest_var,
            }
        }
    }
}

#[cfg(test)]
mod multiple_definition {
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
                return_count: 2
            }
        ];
        let arguments_flattened = vec![];
        let mut statements_flattened = vec![];
        let statement = TypedStatement::MultipleDefinition(
            vec![
                Variable::from("a".to_string()),
                Variable::from("b".to_string())
            ],
            TypedExpressionList::FunctionCall("foo".to_string(), vec![], vec![Type::FieldElement, Type::FieldElement])
        );

        flattener.flatten_statement(
            &mut functions_flattened,
            &arguments_flattened,
            &mut statements_flattened,
            statement,
        );

        assert_eq!(
            statements_flattened[0]
            ,
            FlatStatement::Definition("a".to_string(), FlatExpression::Number(FieldPrime::from(1)))
        );
    }

    #[test]
    fn multiple_definition2() {

        // def dup(x)
        //     return x, x
        // def main()
        //     a, b = dup(2)

        let mut flattener = Flattener::new(FieldPrime::get_required_bits());
        let mut functions_flattened = vec![
            FlatFunction {
                id: "dup".to_string(),
                arguments: vec![FlatParameter { id: "x".to_string(), private: true }],
                statements: vec![FlatStatement::Return(
                    FlatExpressionList {
                        expressions: vec![
                            FlatExpression::Identifier("x".to_string()),
                            FlatExpression::Identifier("x".to_string()),
                        ]
                    }
                )],
                return_count: 2
            }
        ];
        let arguments_flattened = vec![];
        let mut statements_flattened = vec![];
        let statement = TypedStatement::MultipleDefinition(
            vec![
                Variable::from("a".to_string()),
                Variable::from("b".to_string())
            ],
            TypedExpressionList::FunctionCall("dup".to_string(), vec![TypedExpression::FieldElement(FieldElementExpression::Number(FieldPrime::from(2)))], vec![Type::FieldElement, Type::FieldElement])
        );

        flattener.flatten_statement(
            &mut functions_flattened,
            &arguments_flattened,
            &mut statements_flattened,
            statement,
        );

        assert_eq!(
            statements_flattened[0]
            ,
            FlatStatement::Definition("dup_i1o2_1_param_0".to_string(), FlatExpression::Number(FieldPrime::from(2)))
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
                return_count: 1         
            }
        ];
        let arguments_flattened = vec![];
        let mut statements_flattened = vec![];
        let statement = TypedStatement::Definition(
            Variable::from("a".to_string()),
            TypedExpression::FieldElement(FieldElementExpression::FunctionCall("foo".to_string(), vec![]))
        );

        flattener.flatten_statement(
            &mut functions_flattened,
            &arguments_flattened,
            &mut statements_flattened,
            statement,
        );

        assert_eq!(
            statements_flattened[0]
            ,
            FlatStatement::Definition("a".to_string(), FlatExpression::Number(FieldPrime::from(1)))
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
            signature: Signature {
                inputs: vec![Type::FieldElement],
                outputs: vec![Type::FieldElement]
            },
            arguments: vec![Parameter { id: Variable::from("a"), private: true }],
            statements: vec![
                TypedStatement::Definition(
                    Variable::from("a".to_string()), 
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

        assert_eq!(
            flat_funct.statements[0],
            FlatStatement::Definition("a_0".to_string(), FlatExpression::Add(box FlatExpression::Identifier("a".to_string()), box FlatExpression::Number(FieldPrime::from(1))))
        );
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
                signature: Signature {
                    inputs: vec![],
                    outputs: vec![Type::FieldElement]
                },
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
                signature: Signature {
                    inputs: vec![],
                    outputs: vec![Type::FieldElement, Type::FieldElement]
                },
            },
            TypedFunction {
                id: "main".to_string(),
                arguments: vec![],
                statements: vec![
                    TypedStatement::Definition(Variable::from("a".to_string()), TypedExpression::FieldElement(FieldElementExpression::FunctionCall("foo".to_string(), vec![]))),
                    TypedStatement::MultipleDefinition(vec![Variable::from("b".to_string()), Variable::from("c".to_string())], TypedExpressionList::FunctionCall("foo".to_string(), vec![], vec![Type::FieldElement, Type::FieldElement])),
                    TypedStatement::Return(
                        vec![TypedExpression::FieldElement(FieldElementExpression::Number(FieldPrime::from(1)))]
                    )
                ],
                signature: Signature {
                    inputs: vec![],
                    outputs: vec![Type::FieldElement]
                },
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

}
