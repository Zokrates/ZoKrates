/**
 * @file flatten.rs
 * @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
 * @date 2017
 */

use absy::*;
use absy::Expression::*;

fn flatten_condition(statements_flattened: &mut Vec<Statement>, num_variables: &mut i32, condition: Condition) -> Expression {
    match condition {
        Condition::Lt(lhs, rhs) => {
            let lhs_flattened = flatten_expression(statements_flattened, num_variables, lhs);
            let rhs_flattened = flatten_expression(statements_flattened, num_variables, rhs);

            let lhs_name = format!("sym_{}", num_variables);
            *num_variables += 1;
            statements_flattened.push(Statement::Definition(lhs_name.to_string(), lhs_flattened));
            let rhs_name = format!("sym_{}", num_variables);
            *num_variables += 1;
            statements_flattened.push(Statement::Definition(rhs_name.to_string(), rhs_flattened));

            let cond_result = format!("sym_{}", num_variables);
            *num_variables += 1;
            statements_flattened.push(Statement::Definition(
                cond_result.to_string(),
                Sub(
                    box VariableReference(lhs_name.to_string()),
                    box VariableReference(rhs_name.to_string())
                )
            ));
            let bits = 8;
            for i in 0..bits {
                let new_name = format!("{}_b{}", &cond_result, i);
                statements_flattened.push(Statement::Definition(
                    new_name.to_string(),
                    Mult(
                        box VariableReference(new_name.to_string()),
                        box VariableReference(new_name.to_string())
                    )
                ));
            }
            let mut expr = VariableReference(format!("{}_b0", &cond_result)); // * 2^0
            for i in 1..bits - 1 {
                expr = Add(
                    box Mult(
                        box VariableReference(format!("{}_b{}", &cond_result, i)),
                        box NumberLiteral(2i32.pow(i))
                    ),
                    box expr
                );
            }
            expr = Add(
                box Mult(
                    box VariableReference(format!("{}_b{}", &cond_result, bits - 1)),
                    box NumberLiteral(-2i32.pow(bits - 1))
                ),
                box expr
            );
            statements_flattened.push(Statement::Definition(cond_result.to_string(), expr));

            let cond_true = format!("{}_b{}", &cond_result, bits - 1);
            VariableReference(cond_true)
        },
        _ => unimplemented!(),
    }
}

fn flatten_expression(statements_flattened: &mut Vec<Statement>, num_variables: &mut i32, expr: Expression) -> Expression {
    match expr {
        x @ NumberLiteral(_) |
        x @ VariableReference(_) => x,
        ref x @ Add(..) |
        ref x @ Sub(..) |
        ref x @ Mult(..) |
        ref x @ Div(..) if x.is_flattened() => x.clone(),
        Add(box left, box right) => {
            let left_flattened = flatten_expression(statements_flattened, num_variables, left);
            let right_flattened = flatten_expression(statements_flattened, num_variables, right);
            let new_left = if left_flattened.is_linear() {
                left_flattened
            } else {
                let new_name = format!("sym_{}", num_variables);
                *num_variables += 1;
                statements_flattened.push(Statement::Definition(new_name.to_string(), left_flattened));
                VariableReference(new_name)
            };
            let new_right = if right_flattened.is_linear() {
                right_flattened
            } else {
                let new_name = format!("sym_{}", num_variables);
                *num_variables += 1;
                statements_flattened.push(Statement::Definition(new_name.to_string(), right_flattened));
                VariableReference(new_name)
            };
            Add(box new_left, box new_right)
        },
        Sub(box left, box right) => {
            let left_flattened = flatten_expression(statements_flattened, num_variables, left);
            let right_flattened = flatten_expression(statements_flattened, num_variables, right);
            let new_left = if left_flattened.is_linear() {
                left_flattened
            } else {
                let new_name = format!("sym_{}", num_variables);
                *num_variables += 1;
                statements_flattened.push(Statement::Definition(new_name.to_string(), left_flattened));
                VariableReference(new_name)
            };
            let new_right = if right_flattened.is_linear() {
                right_flattened
            } else {
                let new_name = format!("sym_{}", num_variables);
                *num_variables += 1;
                statements_flattened.push(Statement::Definition(new_name.to_string(), right_flattened));
                VariableReference(new_name)
            };
            Sub(box new_left, box new_right)
        },
        Mult(box left, box right) => {
            let left_flattened = flatten_expression(statements_flattened, num_variables, left);
            let right_flattened = flatten_expression(statements_flattened, num_variables, right);
            let new_left = if left_flattened.is_linear() {
                left_flattened
            } else {
                let new_name = format!("sym_{}", num_variables);
                *num_variables += 1;
                statements_flattened.push(Statement::Definition(new_name.to_string(), left_flattened));
                VariableReference(new_name)
            };
            let new_right = if right_flattened.is_linear() {
                right_flattened
            } else {
                let new_name = format!("sym_{}", num_variables);
                *num_variables += 1;
                statements_flattened.push(Statement::Definition(new_name.to_string(), right_flattened));
                VariableReference(new_name)
            };
            Mult(box new_left, box new_right)
        },
        Div(box left, box right) => {
            let left_flattened = flatten_expression(statements_flattened, num_variables, left);
            let right_flattened = flatten_expression(statements_flattened, num_variables, right);
            let new_left = if left_flattened.is_linear() {
                left_flattened
            } else {
                let new_name = format!("sym_{}", num_variables);
                *num_variables += 1;
                statements_flattened.push(Statement::Definition(new_name.to_string(), left_flattened));
                VariableReference(new_name)
            };
            let new_right = if right_flattened.is_linear() {
                right_flattened
            } else {
                let new_name = format!("sym_{}", num_variables);
                *num_variables += 1;
                statements_flattened.push(Statement::Definition(new_name.to_string(), right_flattened));
                VariableReference(new_name)
            };
            Div(box new_left, box new_right)
        },
        Pow(base, exponent) => {
            // TODO currently assuming that base is number or variable
            match exponent {
                box NumberLiteral(x) if x > 1 => {
                    match base {
                        box VariableReference(ref var) => {
                            let id = if x > 2 {
                                let tmp_expression = flatten_expression(
                                    statements_flattened,
                                    num_variables,
                                    Pow(
                                        box VariableReference(var.to_string()),
                                        box NumberLiteral(x - 1)
                                    )
                                );
                                let new_name = format!("sym_{}", num_variables);
                                *num_variables += 1;
                                statements_flattened.push(Statement::Definition(new_name.to_string(), tmp_expression));
                                new_name
                            } else {
                                var.to_string()
                            };
                            Mult(
                                box VariableReference(id.to_string()),
                                box VariableReference(var.to_string())
                            )
                        },
                        box NumberLiteral(var) => Mult(
                            box NumberLiteral(var),
                            box NumberLiteral(var)
                        ),
                        _ => panic!("Only variables and numbers allowed in pow base")
                    }
                }
                _ => panic!("Expected number > 1 as pow exponent"),
            }
        },
        IfElse(box condition, consequent, alternative) => {
            let condition_true = flatten_condition(statements_flattened, num_variables, condition);
            let new_name = format!("sym_{}", num_variables);
            *num_variables += 1;
            // condition_false = 1 - condition_true
            statements_flattened.push(Statement::Definition(new_name.to_string(), Sub(box NumberLiteral(1), box condition_true.clone())));
            let condition_false = VariableReference(new_name);
            // (condition_true * consequent) + (condition_false * alternatuve)
            flatten_expression(
                statements_flattened,
                num_variables,
                Add(
                    box Mult(box condition_true, consequent),
                    box Mult(box condition_false, alternative)
                )
            )
        },
    }
}

pub fn flatten_program(prog: Prog) -> Prog {
    let mut statements_flattened = Vec::new();
    let mut num_variables: i32 = 0;
    for def in prog.statements {
        match def {
            Statement::Return(expr) => {
                let rhs = flatten_expression(&mut statements_flattened, &mut num_variables, expr);
                statements_flattened.push(Statement::Return(rhs));
            },
            Statement::Definition(id, expr) => {
                let rhs = flatten_expression(&mut statements_flattened, &mut num_variables, expr);
                statements_flattened.push(Statement::Definition(id, rhs));
            },
        }
    }
    Prog { id: prog.id, arguments: prog.arguments, statements: statements_flattened }
}
