//! Module containing the `Flattener` to process a program that it is R1CS-able.
//!
//! @file flatten.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

const BINARY_SEPARATOR: &str = "_b";


use std::collections::{HashSet, HashMap};
use absy::*;
use field::Field;
use flat_absy::*;
use parameter::Parameter;
use direct_substitution::DirectSubstitution;
use substitution::Substitution;
use helpers::{DirectiveStatement};

/// Flattener, computes flattened program.
pub struct Flattener {
    /// Number of bits needed to represent the maximum value.
    bits: usize,
    /// Vector containing all used variables while processing the program.
    variables: HashSet<String>,
    /// Map of renamings for reassigned variables while processing the program.
    substitution: DirectSubstitution,
    /// Map of function id to invocation counter
    function_calls: HashMap<String, usize>,
    /// Index of the next introduced variable while processing the program.
    next_var_idx: usize,
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
        }
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
        arguments_flattened: &Vec<Parameter>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        condition: Condition<T>,
    ) -> (Expression<T>, Expression<T>) {
        match condition {
            Condition::Lt(lhs, rhs) => {
                let lhs_flattened = self.flatten_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    lhs,
                );
                let rhs_flattened = self.flatten_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    rhs,
                );

                let lhs_name = format!("sym_{}", self.next_var_idx);
                self.next_var_idx += 1;
                statements_flattened
                    .push(FlatStatement::Definition(lhs_name.to_string(), lhs_flattened));
                let rhs_name = format!("sym_{}", self.next_var_idx);
                self.next_var_idx += 1;
                statements_flattened
                    .push(FlatStatement::Definition(rhs_name.to_string(), rhs_flattened));

                let subtraction_result = format!("sym_{}", self.next_var_idx);
                self.next_var_idx += 1;
                statements_flattened.push(FlatStatement::Definition(
                    subtraction_result.to_string(),
                    FlatExpression::Sub(
                        box FlatExpression::Mult(box FlatExpression::Number(T::from(2)), box FlatExpression::Identifier(lhs_name.to_string())),
                        box FlatExpression::Mult(box FlatExpression::Number(T::from(2)), box FlatExpression::Identifier(rhs_name.to_string())),
                    ),
                ));
                for i in 0..self.bits {
                    let new_name = format!("{}{}{}", &subtraction_result, BINARY_SEPARATOR, i);
                    statements_flattened.push(FlatStatement::Definition(
                        new_name.to_string(),
                        FlatExpression::Mult(
                            box FlatExpression::Identifier(new_name.to_string()),
                            box FlatExpression::Identifier(new_name.to_string()),
                        ),
                    ));
                }
                let mut expr = FlatExpression::Add(
                    box FlatExpression::Identifier(format!("{}{}0", &subtraction_result, BINARY_SEPARATOR)), // * 2^0
                    box FlatExpression::Mult(
                        box FlatExpression::Identifier(format!("{}{}1", &subtraction_result, BINARY_SEPARATOR)),
                        box FlatExpression::Number(T::from(2)),
                    ),
                );
                for i in 1..self.bits / 2 {
                    expr = FlatExpression::Add(
                        box expr,
                        box FlatExpression::Add(
                            box FlatExpression::Mult(
                                box FlatExpression::Identifier(format!("{}{}{}", &subtraction_result, BINARY_SEPARATOR, 2 * i)),
                                box FlatExpression::Number(T::from(2).pow(2 * i)),
                            ),
                            box FlatExpression::Mult(
                                box FlatExpression::Identifier(format!("{}{}{}", &subtraction_result, BINARY_SEPARATOR, 2 * i + 1)),
                                box FlatExpression::Number(T::from(2).pow(2 * i + 1)),
                            ),
                        ),
                    );
                }
                if self.bits % 2 == 1 {
                    expr = FlatExpression::Add(
                        box expr,
                        box FlatExpression::Mult(
                            box FlatExpression::Identifier(format!("{}{}{}", &subtraction_result, BINARY_SEPARATOR, self.bits - 3)),
                            box FlatExpression::Number(T::from(2).pow(self.bits - 1)),
                        ),
                    )
                }
                statements_flattened
                    .push(FlatStatement::Definition(subtraction_result.to_string(), expr));

                let cond_true = format!("{}{}0", &subtraction_result, BINARY_SEPARATOR);
                let cond_false = format!("sym_{}", self.next_var_idx);
                self.next_var_idx += 1;
                statements_flattened.push(FlatStatement::Definition(
                    cond_false.to_string(),
                    FlatExpression::Sub(box FlatExpression::Number(T::one()), box FlatExpression::Identifier(cond_true.to_string())),
                ));
                (Expression::Identifier(cond_true), Expression::Identifier(cond_false))
            }
            Condition::Eq(lhs, rhs) => {
                // Wanted: (Y = (X != 0) ? 1 : 0)
                // X = a - b
                // # Y = if X == 0 then 0 else 1 fi
                // # M = if X == 0 then 1 else 1/X fi
                // Y == X * M
                // 0 == (1-Y) * X
                let name_x = format!("sym_{}", self.next_var_idx);
                self.next_var_idx += 1;
                let name_y = format!("sym_{}", self.next_var_idx);
                self.next_var_idx += 1;
                let name_m = format!("sym_{}", self.next_var_idx);
                self.next_var_idx += 1;
                let name_1_y = format!("sym_{}", self.next_var_idx);
                self.next_var_idx += 1;

                let x = self.flatten_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    Expression::Sub(box lhs, box rhs),
                );
                statements_flattened.push(FlatStatement::Definition(name_x.to_string(), x));
                statements_flattened.push(FlatStatement::Compiler(
                    name_y.to_string(),
                    Expression::IfElse(
                            box Condition::Eq(Expression::Identifier(name_x.to_string()), Expression::Number(T::zero())),
                            box Expression::Number(T::zero()),
                            box Expression::Number(T::one()),
                    ),
                ));
                statements_flattened.push(FlatStatement::Compiler(
                    name_m.to_string(),
                    Expression::IfElse(
                            box Condition::Eq(Expression::Identifier(name_x.to_string()), Expression::Number(T::zero())),
                            box Expression::Number(T::one()),
                            box Expression::Div(box Expression::Number(T::one()), box Expression::Identifier(name_x.to_string())),
                    ),
                ));
                statements_flattened.push(FlatStatement::Condition(
                    FlatExpression::Identifier(name_y.to_string()),
                    FlatExpression::Mult(box FlatExpression::Identifier(name_x.to_string()), box FlatExpression::Identifier(name_m)),
                ));
                statements_flattened.push(FlatStatement::Definition(
                    name_1_y.to_string(),
                    FlatExpression::Sub(box FlatExpression::Number(T::one()), box FlatExpression::Identifier(name_y.to_string())),
                ));
                statements_flattened.push(FlatStatement::Condition(
                    FlatExpression::Number(T::zero()),
                    FlatExpression::Mult(box FlatExpression::Identifier(name_1_y.to_string()), box FlatExpression::Identifier(name_x)),
                ));

                (Expression::Identifier(name_1_y), Expression::Identifier(name_y))
            }
            _ => unimplemented!(),
        }
    }

    fn flatten_function_call<T: Field>(
        &mut self,
        functions_flattened: &Vec<FlatFunction<T>>,
        arguments_flattened: &Vec<Parameter>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        id: &String,
        return_count: usize,
        param_expressions: &Vec<Expression<T>>
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
                for (i, param_expr) in param_expressions.iter().enumerate() {
                    let new_var;
                    match param_expr.apply_substitution(&self.substitution) {
                        Expression::Identifier(ref x) => {
                            new_var = format!("{}param_{}", &prefix, i);
                                statements_flattened
                                .push(FlatStatement::Definition(new_var.clone(), FlatExpression::Identifier(x.clone().to_string())));
                        },
                        _ => {
                            let expr_subbed = param_expr.apply_substitution(&self.substitution);
                            let rhs = self.flatten_expression(
                                functions_flattened,
                                arguments_flattened,
                                statements_flattened,
                                expr_subbed,
                            );
                            new_var = format!("{}param_{}", &prefix, i);
                            statements_flattened
                                .push(FlatStatement::Definition(new_var.clone(), rhs));
                        }
                    }
                    replacement_map.insert(funct.arguments.get(i).unwrap().id.clone(), new_var);
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
                            let new_var: String = format!("{}{}", prefix, var.clone());
                            replacement_map.insert(var, new_var.clone());
                            let new_rhs = rhs.apply_substitution(&replacement_map);
                            statements_flattened.push(
                                FlatStatement::Definition(new_var, new_rhs)
                            );
                        },
                        FlatStatement::Compiler(var, rhs) => {
                            let new_var: String = format!("{}{}", prefix, var.clone());
                            replacement_map.insert(var, new_var.clone());
                            let new_rhs = rhs.apply_substitution(&replacement_map);
                            statements_flattened.push(FlatStatement::Compiler(new_var, new_rhs));
                        },
                        FlatStatement::Condition(lhs, rhs) => {
                            let new_lhs = lhs.apply_substitution(&replacement_map);
                            let new_rhs = rhs.apply_substitution(&replacement_map);
                            statements_flattened
                                .push(FlatStatement::Condition(new_lhs, new_rhs));
                        },
                        FlatStatement::Directive(d) => {
                            let new_outputs = d.outputs.iter().map(|o| {
                                let new_o: String = format!("{}{}", prefix, o.clone());
                                replacement_map.insert(o.to_string(), new_o.clone());
                                new_o
                            }).collect();
                            let new_inputs = d.inputs.iter().map(|i| replacement_map.get(i).unwrap()).collect();
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
            "Function definition for function {} with {:?} argument(s) not found.",
            id,
            param_expressions
        );
    }

    /// Returns a flattened `Expression` based on the given `expr`.
    ///
    /// # Arguments
    ///
    /// * `functions_flattened` - Vector containing already flattened functions.
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `expr` - `Expresstion` that will be flattened.
    fn flatten_expression<T: Field>(
        &mut self,
        functions_flattened: &Vec<FlatFunction<T>>,
        arguments_flattened: &Vec<Parameter>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        expr: Expression<T>,
    ) -> FlatExpression<T> {
        match expr {
            Expression::Number(x) => FlatExpression::Number(x),
            Expression::Identifier(x) => FlatExpression::Identifier(x),
            Expression::Add(box left, box right) => {
                let left_flattened = self.flatten_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    left,
                );
                let right_flattened = self.flatten_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    right,
                );
                let new_left = if left_flattened.is_linear() {
                    left_flattened
                } else {
                    let new_name = format!("sym_{}", self.next_var_idx);
                    self.next_var_idx += 1;
                    statements_flattened
                        .push(FlatStatement::Definition(new_name.to_string(), left_flattened));
                    FlatExpression::Identifier(new_name)
                };
                let new_right = if right_flattened.is_linear() {
                    right_flattened
                } else {
                    let new_name = format!("sym_{}", self.next_var_idx);
                    self.next_var_idx += 1;
                    statements_flattened
                        .push(FlatStatement::Definition(new_name.to_string(), right_flattened));
                    FlatExpression::Identifier(new_name)
                };
                FlatExpression::Add(box new_left, box new_right)
            }
            Expression::Sub(box left, box right) => {
                let left_flattened = self.flatten_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    left,
                );
                let right_flattened = self.flatten_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    right,
                );
                let new_left = if left_flattened.is_linear() {
                    left_flattened
                } else {
                    let new_name = format!("sym_{}", self.next_var_idx);
                    self.next_var_idx += 1;
                    statements_flattened
                        .push(FlatStatement::Definition(new_name.to_string(), left_flattened));
                    FlatExpression::Identifier(new_name)
                };
                let new_right = if right_flattened.is_linear() {
                    right_flattened
                } else {
                    let new_name = format!("sym_{}", self.next_var_idx);
                    self.next_var_idx += 1;
                    statements_flattened
                        .push(FlatStatement::Definition(new_name.to_string(), right_flattened));
                    FlatExpression::Identifier(new_name)
                };
                FlatExpression::Sub(box new_left, box new_right)
            }
            Expression::Mult(box left, box right) => {
                let left_flattened = self.flatten_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    left,
                );
                let right_flattened = self.flatten_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    right,
                );
                let new_left = if left_flattened.is_linear() {
                    if let FlatExpression::Sub(..) = left_flattened {
                        let new_name = format!("sym_{}", self.next_var_idx);
                        self.next_var_idx += 1;
                        statements_flattened
                            .push(FlatStatement::Definition(new_name.to_string(), left_flattened));
                        FlatExpression::Identifier(new_name)
                    } else {
                        left_flattened
                    }
                } else {
                    let new_name = format!("sym_{}", self.next_var_idx);
                    self.next_var_idx += 1;
                    statements_flattened
                        .push(FlatStatement::Definition(new_name.to_string(), left_flattened));
                    FlatExpression::Identifier(new_name)
                };
                let new_right = if right_flattened.is_linear() {
                    if let FlatExpression::Sub(..) = right_flattened {
                        let new_name = format!("sym_{}", self.next_var_idx);
                        self.next_var_idx += 1;
                        statements_flattened
                            .push(FlatStatement::Definition(new_name.to_string(), right_flattened));
                        FlatExpression::Identifier(new_name)
                    } else {
                        right_flattened
                    }
                } else {
                    let new_name = format!("sym_{}", self.next_var_idx);
                    self.next_var_idx += 1;
                    statements_flattened
                        .push(FlatStatement::Definition(new_name.to_string(), right_flattened));
                    FlatExpression::Identifier(new_name)
                };
                FlatExpression::Mult(box new_left, box new_right)
            }
            Expression::Div(box left, box right) => {
                let left_flattened = self.flatten_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    left,
                );
                let right_flattened = self.flatten_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    right,
                );
                let new_left = {
                    let new_name = format!("sym_{}", self.next_var_idx);
                    self.next_var_idx += 1;
                    statements_flattened
                        .push(FlatStatement::Definition(new_name.to_string(), left_flattened));
                    FlatExpression::Identifier(new_name)
                };
                let new_right = {
                    let new_name = format!("sym_{}", self.next_var_idx);
                    self.next_var_idx += 1;
                    statements_flattened
                        .push(FlatStatement::Definition(new_name.to_string(), right_flattened));
                    FlatExpression::Identifier(new_name)
                };
                FlatExpression::Div(box new_left, box new_right)
            }
            Expression::Pow(base, exponent) => {
                // TODO currently assuming that base is number or variable
                match exponent {
                    box Expression::Number(ref x) if x > &T::one() => match base {
                        box Expression::Identifier(ref var) => {
                            let id = if x > &T::from(2) {
                                let tmp_expression = self.flatten_expression(
                                    functions_flattened,
                                    arguments_flattened,
                                    statements_flattened,
                                    Expression::Pow(
                                        box Expression::Identifier(var.to_string()),
                                        box Expression::Number(x.clone() - T::one()),
                                    ),
                                );
                                let new_name = format!("sym_{}", self.next_var_idx);
                                self.next_var_idx += 1;
                                statements_flattened.push(
                                    FlatStatement::Definition(new_name.to_string(), tmp_expression),
                                );
                                new_name
                            } else {
                                var.to_string()
                            };
                            FlatExpression::Mult(
                                box FlatExpression::Identifier(id.to_string()),
                                box FlatExpression::Identifier(var.to_string()),
                            )
                        }
                        box Expression::Number(var) => FlatExpression::Mult(box FlatExpression::Number(var.clone()), box FlatExpression::Number(var)),
                        _ => panic!("Only variables and numbers allowed in pow base"),
                    },
                    _ => panic!("Expected number > 1 as pow exponent"),
                }
            }
            Expression::IfElse(box condition, consequent, alternative) => {

                let (cond_true, cond_false) = self.flatten_condition(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    condition,
                );
                // (condition_true * consequent) + (condition_false * alternatuve)
                self.flatten_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    Expression::Add(
                        box Expression::Mult(box cond_true, consequent),
                        box Expression::Mult(box cond_false, alternative),
                    ),
                )
            }
            Expression::FunctionCall(ref id, ref param_expressions) => {
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

    pub fn flatten_expression_list<T: Field>(
        &mut self,
        functions_flattened: &mut Vec<FlatFunction<T>>,
        arguments_flattened: &Vec<Parameter>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        list: ExpressionList<T>,
    ) -> FlatExpressionList<T> {
        let flattened_exprs = list.expressions.into_iter().map(|x|
            self.flatten_expression(
                functions_flattened,
                arguments_flattened,
                statements_flattened,
                x.clone())
            ).collect();
        FlatExpressionList {
            expressions: flattened_exprs
        }
    }

    pub fn flatten_statement<T: Field>(
        &mut self,
        functions_flattened: &mut Vec<FlatFunction<T>>,
        arguments_flattened: &Vec<Parameter>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
        stat: &Statement<T>,
    ) {
        match *stat {
            Statement::Return(ref exprs) => {
                let exprs_subbed = exprs.apply_substitution(&self.substitution);
                let rhs = self.flatten_expression_list(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    exprs_subbed,
                );

                statements_flattened.push(FlatStatement::Return(rhs));
            }
            Statement::Definition(ref id, ref expr) => {
                let expr_subbed = expr.apply_substitution(&self.substitution);
                let rhs = self.flatten_expression(
                    functions_flattened,
                    arguments_flattened,
                    statements_flattened,
                    expr_subbed,
                );
                let var = self.use_variable(&id);
                // handle return of function call
                let var_to_replace = self.get_latest_var_substitution(&id);
                if !(var == var_to_replace) && self.variables.contains(&var_to_replace) && !self.substitution.contains_key(&var_to_replace){
                    self.substitution.insert(var_to_replace.clone().to_string(),var.clone());
                }

                statements_flattened.push(FlatStatement::Definition(var, rhs));
            }
            Statement::Condition(ref expr1, ref expr2) => {
                let expr1_subbed = expr1.apply_substitution(&self.substitution);
                let expr2_subbed = expr2.apply_substitution(&self.substitution);
                let (lhs, rhs) = if expr1_subbed.is_linear() {
                    (
                        self.flatten_expression(
                            functions_flattened,
                            arguments_flattened,
                            statements_flattened,
                            expr1_subbed
                        ),
                        self.flatten_expression(
                            functions_flattened,
                            arguments_flattened,
                            statements_flattened,
                            expr2_subbed,
                        ),
                    )
                } else if expr2_subbed.is_linear() {
                    (
                        self.flatten_expression(
                            functions_flattened,
                            arguments_flattened,
                            statements_flattened,
                            expr2_subbed,
                        ),
                        self.flatten_expression(
                            functions_flattened,
                            arguments_flattened,
                            statements_flattened,
                            expr1_subbed,
                        ),
                    )
                } else {
                    unimplemented!()
                };
                statements_flattened.push(FlatStatement::Condition(lhs, rhs));
            }
            Statement::For(ref var, ref start, ref end, ref statements) => {
                let mut current = start.clone();
                while &current < end {
                    statements_flattened.push(FlatStatement::Definition(
                        self.use_variable(&var),
                        FlatExpression::Number(current.clone()),
                    ));
                    for s in statements {
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
            Statement::MultipleDefinition(ref ids, ref rhs) => {
                let rhs_subbed = rhs.apply_substitution(&self.substitution);
                match rhs_subbed {
                    Expression::FunctionCall(ref fun_id, ref exprs) => {
                        let rhs_flattened = self.flatten_function_call(
                            functions_flattened,
                            arguments_flattened,
                            statements_flattened,
                            fun_id,
                            ids.len(),
                            exprs,
                        );

                        for (i, id) in ids.into_iter().enumerate() {
                            let var = self.use_variable(&id);
                            // handle return of function call
                            let var_to_replace = self.get_latest_var_substitution(&id);
                            if !(var == var_to_replace) && self.variables.contains(&var_to_replace) && !self.substitution.contains_key(&var_to_replace){
                                self.substitution.insert(var_to_replace.clone().to_string(),var.clone());
                            }
                            statements_flattened.push(FlatStatement::Definition(var, rhs_flattened.expressions[i].clone()));
                        }
                    },
                    _ => panic!("Right hand side of a MultipleDefinition should be a FunctionCall")
                }
            },
        }
    }

    /// Returns a flattened `Function` based on the given `funct`.
    ///
    /// # Arguments
    ///
    /// * `functions_flattened` - Vector where new flattened functions can be added.
    /// * `funct` - `Function` that will be flattened.
    pub fn flatten_function<T: Field>(
        &mut self,
        functions_flattened: &mut Vec<FlatFunction<T>>,
        funct: Function<T>,
    ) -> FlatFunction<T> {
        self.variables = HashSet::new();
        self.substitution = DirectSubstitution::new();
        self.next_var_idx = 0;
        let mut arguments_flattened: Vec<Parameter> = Vec::new();
        let mut statements_flattened: Vec<FlatStatement<T>> = Vec::new();
        // push parameters
        for arg in funct.arguments {
            arguments_flattened.push(Parameter {
                id: arg.id.to_string(),
                private: arg.private
            });
        }
        // flatten statements in functions and apply substitution
        for stat in funct.statements {
            self.flatten_statement(
                functions_flattened,
                &arguments_flattened,
                &mut statements_flattened,
                &stat,
            );
        }
        FlatFunction {
            id: funct.id,
            arguments: arguments_flattened,
            statements: statements_flattened,
            return_count: funct.return_count
        }
    }

    /// Returns a flattened `Prog`ram based on the given `prog`.
    ///
    /// # Arguments
    ///
    /// * `prog` - `Prog`ram that will be flattened.
    pub fn flatten_program<T: Field>(&mut self, prog: Prog<T>) -> FlatProg<T> {
        let mut functions_flattened = Vec::new();

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
    fn use_variable(&mut self, name: &String) -> String {
        let mut i = 0;
        let mut new_name = name.to_string();
        loop {
            if self.variables.contains(&new_name) {
                new_name = format!("{}_{}", &name, i);
                i += 1;
            } else {
                self.variables.insert(new_name.to_string());
                if i == 1 {
                    self.substitution
                        .insert(name.to_string(), new_name.to_string());
                } else if i > 1 {
                    self.substitution
                        .insert(format!("{}_{}", name, i - 2), new_name.to_string());
                }
                return new_name;
            }
        }
    }

    fn get_latest_var_substitution(&mut self, name: &String)->String{
        let mut latest_var = name.to_string();
        loop {
            match self.substitution.get(&latest_var) {
                Some(x) => latest_var = x.to_string(),
                None => return latest_var,
            }
        }
    }
}

#[cfg(test)]
mod multiple_definition {
    use super::*;
    use field::FieldPrime;

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
                return_count: 2,
            }
        ];
        let arguments_flattened = vec![];
        let mut statements_flattened = vec![];
        let statement = Statement::MultipleDefinition(
            vec![
                "a".to_string(),
                "b".to_string()
            ],
            Expression::FunctionCall("foo".to_string(), vec![])
        );

        flattener.flatten_statement(
            &mut functions_flattened,
            &arguments_flattened,
            &mut statements_flattened,
            &statement,
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
                arguments: vec![Parameter { id: "x".to_string(), private: true }],
                statements: vec![FlatStatement::Return(
                    FlatExpressionList {
                        expressions: vec![
                            FlatExpression::Identifier("x".to_string()),
                            FlatExpression::Identifier("x".to_string()),
                        ]
                    }
                )],
                return_count: 2,
            }
        ];
        let arguments_flattened = vec![];
        let mut statements_flattened = vec![];
        let statement = Statement::MultipleDefinition(
            vec![
                "a".to_string(),
                "b".to_string()
            ],
            Expression::FunctionCall("dup".to_string(), vec![Expression::Number(FieldPrime::from(2))])
        );

        flattener.flatten_statement(
            &mut functions_flattened,
            &arguments_flattened,
            &mut statements_flattened,
            &statement,
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
                return_count: 1,
            }
        ];
        let arguments_flattened = vec![];
        let mut statements_flattened = vec![];
        let statement = Statement::Definition(
            "a".to_string(),
            Expression::FunctionCall("foo".to_string(), vec![])
        );

        flattener.flatten_statement(
            &mut functions_flattened,
            &arguments_flattened,
            &mut statements_flattened,
            &statement,
        );

        assert_eq!(
            statements_flattened[0]
            ,
            FlatStatement::Definition("a".to_string(), FlatExpression::Number(FieldPrime::from(1)))
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
            Function {
                id: "foo".to_string(),
                arguments: vec![],
                statements: vec![Statement::Return(
                    ExpressionList {
                        expressions: vec![
                            Expression::Number(FieldPrime::from(1))
                        ]
                    }
                )],
                return_count: 1,
            },
            Function {
                id: "foo".to_string(),
                arguments: vec![],
                statements: vec![Statement::Return(
                    ExpressionList {
                        expressions: vec![
                            Expression::Number(FieldPrime::from(1)),
                            Expression::Number(FieldPrime::from(2))
                        ]
                    }
                )],
                return_count: 2,
            },
            Function {
                id: "main".to_string(),
                arguments: vec![],
                statements: vec![
                    Statement::Definition("a".to_string(), Expression::FunctionCall("foo".to_string(), vec![])),
                    Statement::MultipleDefinition(vec!["b".to_string(), "c".to_string()], Expression::FunctionCall("foo".to_string(), vec![])),
                    Statement::Return(ExpressionList {
                        expressions: vec![Expression::Number(FieldPrime::from(1))]
                    })
                ],
                return_count: 1
            }
        ];

        flattener.flatten_program(
            Prog {
                functions: functions,
                imported_functions: vec![],
                imports: vec![]
            }
        );

        // shouldn't panic
    }
}
