extern crate regex;

use std::io::BufReader;
use std::io::prelude::*;
use std::fs::File;
use self::regex::Regex;
use ast::*;
use ast::Expression::*;

fn parse_expression_rhs(text: String) -> Expression {
    let op_regex = Regex::new(r"^((?P<lhs>[[:alnum:]]+)(?P<op>(\*\*|[\+\-\*/]))(?P<rhs>.+)|(?P<var>[[:alpha:]][[:alnum:]]*)|(?P<num>\d+))$").unwrap();
    let ifelse_regex = Regex::new(r"^(?P<condlhs>[[:alnum:]]+)(?P<conop><)(?P<condrhs>[[:alnum:]]+)\?(?P<consequent>[^:]+):(?P<alternative>[^:]+)$").unwrap();
    let variable_regex = Regex::new(r"^[[:alpha:]][[:alnum:]]*$").unwrap();
    let number_regex = Regex::new(r"^[[:digit:]]+$").unwrap();
    let line = text.replace(" ", "").replace("\t", "");
    match op_regex.captures(&line) {
        Some(x) => {
            if let Some(var) = x.name("var") {
                VariableReference(var.as_str().to_string())
            } else if let Some(num) = x.name("num") {
                NumberLiteral(num.as_str().parse::<i32>().unwrap())
            } else {
                let lhs = if variable_regex.is_match(&x["lhs"]) {
                    box VariableReference(x["lhs"].to_string())
                } else if number_regex.is_match(&x["lhs"]) {
                    box NumberLiteral(x["lhs"].parse::<i32>().unwrap())
                } else {
                    panic!("Could not read lhs: {:?}", &x["lhs"])
                };
                let rhs = if variable_regex.is_match(&x["rhs"]) {
                    box VariableReference(x["rhs"].to_string())
                } else if number_regex.is_match(&x["rhs"])  {
                    Box::new(NumberLiteral(x["rhs"].parse::<i32>().unwrap()))
                } else {
                    box parse_expression_rhs(x["rhs"].to_string())
                };
                match &x["op"] {
                    "+" => Add(lhs, rhs),
                    "-" => Sub(lhs, rhs),
                    "*" => Mult(lhs, rhs),
                    "/" => Div(lhs, rhs),
                    "**" if number_regex.is_match(&x["rhs"]) => Pow(lhs, rhs),
                    _ => unimplemented!(),
                }
            }
        },
        None => match ifelse_regex.captures(&line) {
            Some(x) => {
                println!("ifelse {:?}", x);
                let condition = match &x["conop"] {
                    "<" => Condition::Lt(parse_expression_rhs(x["condlhs"].to_string()), parse_expression_rhs(x["condrhs"].to_string())),
                    _ => unimplemented!(),
                };
                IfElse(box condition, box parse_expression_rhs(x["consequent"].to_string()), box parse_expression_rhs(x["alternative"].to_string()))
            },
            None => panic!("Could not parse rhs of expression: {:?}", text),
        },
    }
}

pub fn parse_program(file: File) -> Prog {
    let reader = BufReader::new(file);
    let mut lines = reader.lines();

    let id;
    let args;
    let def_regex = Regex::new(r"^def\s(?P<id>\D[a-zA-Z0-9]+)\(\s*([a-z]+)(,\s*[a-z]+)*\s*\):$").unwrap();
    let args_regex = Regex::new(r"\(\s*(?P<args>[a-z]+(,\s*[a-z]+)*)\s*\)").unwrap();
    loop { // search and make Prog
        match lines.next() {
            Some(Ok(ref x)) if x.starts_with("def") => {
                id = match def_regex.captures(x) {
                    Some(x) => x["id"].to_string(),
                    None => panic!("Wrong definition of function"),
                };
                args = match args_regex.captures(x) {
                    Some(x) => x["args"].replace(" ", "").replace("\t", "").split(",")
                                        .map(|p| Parameter { id: p.to_string() })
                                        .collect::<Vec<_>>(),
                    None => panic!("Wrong argument definition in function: {}", id),
                };
                break;
            },
            Some(Ok(ref x)) if x.trim().starts_with("//") || x == "" => {},
            None => panic!("End of file reached without function def"),
            Some(x) => panic!("Found '{:?}' outside of function", x),
        }
    };

    let mut defs = Vec::new();
    let definition_regex = Regex::new(r"(?P<lhs>[a-zA-Z]+)\s*=\s*(?P<rhs>[a-zA-Z0-9<\?:\s\+\-\*/]+)\s*$").unwrap();
    let return_regex = Regex::new(r"^return\s*(?P<rhs>[a-zA-Z0-9\s\+\-\*/]+)\s*$").unwrap();
    loop { // make list of Definition
        match lines.next() {
            Some(Ok(ref x)) if x.trim().starts_with("//") || x == "" => {},
            Some(Ok(ref line)) if line.trim().starts_with("return") => {
                match return_regex.captures(line.trim()) {
                    Some(x) => defs.push(Definition::Return(parse_expression_rhs(x["rhs"].to_string()))),
                    None => panic!("Wrong return definition in function: {}", id),
                }
            },
            Some(Ok(ref line)) => {
                match definition_regex.captures(line.trim()) {
                    Some(x) => defs.push(Definition::Definition(x["lhs"].to_string(), parse_expression_rhs(x["rhs"].to_string()))),
                    None => panic!("Wrong expression in function '{}':\n{}", id, line),
                }
            },
            None => break,
            Some(Err(e)) => panic!("Error while reading Definitions: {}", e),
        }
    }

    match defs.last() {
        Some(&Definition::Return(_)) => {},
        Some(x) => panic!("Last definition not Return: {}", x),
        None => panic!("Error while checking last definition"),
    }
    Prog { id: id, args: args, defs: defs }
}

fn flatten_condition(defs_flattened: &mut Vec<Definition>, num_variables: &mut i32, condition: Condition) -> Expression {
    match condition {
        Condition::Lt(lhs, rhs) => {
            let lhs_flattened = flatten_expression(defs_flattened, num_variables, lhs);
            let rhs_flattened = flatten_expression(defs_flattened, num_variables, rhs);

            let lhs_name = format!("sym_{}", num_variables);
            *num_variables += 1;
            defs_flattened.push(Definition::Definition(lhs_name.to_string(), lhs_flattened));
            let rhs_name = format!("sym_{}", num_variables);
            *num_variables += 1;
            defs_flattened.push(Definition::Definition(rhs_name.to_string(), rhs_flattened));

            let cond_result = format!("sym_{}", num_variables);
            *num_variables += 1;
            defs_flattened.push(Definition::Definition(
                cond_result.to_string(),
                Sub(
                    box VariableReference(lhs_name.to_string()),
                    box VariableReference(rhs_name.to_string())
                )
            ));
            let bits = 8;
            for i in 0..bits {
                let new_name = format!("{}_b{}", &cond_result, i);
                defs_flattened.push(Definition::Definition(
                    new_name.to_string(),
                    Mult(
                        box VariableReference(new_name.to_string()),
                        box VariableReference(new_name.to_string())
                    )
                ));
            }
            let mut expr = VariableReference(format!("{}_b0", &cond_result)); // * 2^0
            for i in 1..bits {
                expr = Add(
                    box Mult(
                        box VariableReference(format!("{}_b{}", &cond_result, i)),
                        box NumberLiteral(2i32.pow(i))
                    ),
                    box expr
                );
            }
            defs_flattened.push(Definition::Definition(cond_result.to_string(), expr));

            let cond_true = format!("{}_b{}", &cond_result, bits - 1);
            VariableReference(cond_true)
        }
    }
}

fn flatten_expression(defs_flattened: &mut Vec<Definition>, num_variables: &mut i32, expr: Expression) -> Expression {
    match expr {
        x @ NumberLiteral(_) |
        x @ VariableReference(_) => x,
        ref x @ Add(..) |
        ref x @ Sub(..) |
        ref x @ Mult(..) |
        ref x @ Div(..) if x.is_flattened() => x.clone(),
        Add(box left, box right) => {
            let left_flattened = flatten_expression(defs_flattened, num_variables, left);
            let right_flattened = flatten_expression(defs_flattened, num_variables, right);
            let new_left = if left_flattened.is_linear() {
                left_flattened
            } else {
                let new_name = format!("sym_{}", num_variables);
                *num_variables += 1;
                defs_flattened.push(Definition::Definition(new_name.to_string(), left_flattened));
                VariableReference(new_name)
            };
            let new_right = if right_flattened.is_linear() {
                right_flattened
            } else {
                let new_name = format!("sym_{}", num_variables);
                *num_variables += 1;
                defs_flattened.push(Definition::Definition(new_name.to_string(), right_flattened));
                VariableReference(new_name)
            };
            Add(box new_left, box new_right)
        },
        Sub(box left, box right) => {
            let left_flattened = flatten_expression(defs_flattened, num_variables, left);
            let right_flattened = flatten_expression(defs_flattened, num_variables, right);
            let new_left = if left_flattened.is_linear() {
                left_flattened
            } else {
                let new_name = format!("sym_{}", num_variables);
                *num_variables += 1;
                defs_flattened.push(Definition::Definition(new_name.to_string(), left_flattened));
                VariableReference(new_name)
            };
            let new_right = if right_flattened.is_linear() {
                right_flattened
            } else {
                let new_name = format!("sym_{}", num_variables);
                *num_variables += 1;
                defs_flattened.push(Definition::Definition(new_name.to_string(), right_flattened));
                VariableReference(new_name)
            };
            Sub(box new_left, box new_right)
        },
        Mult(box left, box right) => {
            let left_flattened = flatten_expression(defs_flattened, num_variables, left);
            let right_flattened = flatten_expression(defs_flattened, num_variables, right);
            let new_left = if left_flattened.is_linear() {
                left_flattened
            } else {
                let new_name = format!("sym_{}", num_variables);
                *num_variables += 1;
                defs_flattened.push(Definition::Definition(new_name.to_string(), left_flattened));
                VariableReference(new_name)
            };
            let new_right = if right_flattened.is_linear() {
                right_flattened
            } else {
                let new_name = format!("sym_{}", num_variables);
                *num_variables += 1;
                defs_flattened.push(Definition::Definition(new_name.to_string(), right_flattened));
                VariableReference(new_name)
            };
            Mult(box new_left, box new_right)
        },
        Div(box left, box right) => {
            let left_flattened = flatten_expression(defs_flattened, num_variables, left);
            let right_flattened = flatten_expression(defs_flattened, num_variables, right);
            let new_left = if left_flattened.is_linear() {
                left_flattened
            } else {
                let new_name = format!("sym_{}", num_variables);
                *num_variables += 1;
                defs_flattened.push(Definition::Definition(new_name.to_string(), left_flattened));
                VariableReference(new_name)
            };
            let new_right = if right_flattened.is_linear() {
                right_flattened
            } else {
                let new_name = format!("sym_{}", num_variables);
                *num_variables += 1;
                defs_flattened.push(Definition::Definition(new_name.to_string(), right_flattened));
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
                                    defs_flattened,
                                    num_variables,
                                    Pow(
                                        box VariableReference(var.to_string()),
                                        box NumberLiteral(x - 1)
                                    )
                                );
                                let new_name = format!("sym_{}", num_variables);
                                *num_variables += 1;
                                defs_flattened.push(Definition::Definition(new_name.to_string(), tmp_expression));
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
            let condition_true = flatten_condition(defs_flattened, num_variables, condition);
            let new_name = format!("sym_{}", num_variables);
            *num_variables += 1;
            // condition_false = 1 - condition_true
            defs_flattened.push(Definition::Definition(new_name.to_string(), Sub(box NumberLiteral(1), box condition_true.clone())));
            let condition_false = VariableReference(new_name);
            // (condition_true * consequent) + (condition_false * alternatuve)
            flatten_expression(
                defs_flattened,
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
    let mut defs_flattened = Vec::new();
    let mut num_variables: i32 = 0;
    for def in prog.defs {
        match def {
            Definition::Return(expr) => {
                let rhs = flatten_expression(&mut defs_flattened, &mut num_variables, expr);
                defs_flattened.push(Definition::Return(rhs));
            },
            Definition::Definition(id, expr) => {
                let rhs = flatten_expression(&mut defs_flattened, &mut num_variables, expr);
                defs_flattened.push(Definition::Definition(id, rhs));
            },
        }
    }
    Prog { id: prog.id, args: prog.args, defs: defs_flattened }
}
