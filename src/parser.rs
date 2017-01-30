extern crate regex;

use std::io::BufReader;
use std::io::prelude::*;
use std::fs::File;
use self::regex::Regex;
use ast::*;

pub fn parse_expression_rhs(text: String) -> Expression {
    let op_regex = Regex::new(r"^(?P<lhs>[[:alnum:]]+)(?P<op>(\*\*|[\+\-\*/]))(?P<rhs>.*)$").unwrap();
    let ifelse_regex = Regex::new(r"^(?P<condlhs>[[:alnum:]]+)(?P<conmid>==)(?P<conright>[[:alnum:]]+)\?(?P<consequent>[^:]+):(?P<alternative>[^:]+)$").unwrap();
    let variable_regex = Regex::new(r"^[[:alpha:]][[:alnum:]]*$").unwrap();
    let number_regex = Regex::new(r"^[[:digit:]]+$").unwrap();
    let line = text.replace(" ", "").replace("\t", "");
    match op_regex.captures(&line) {
        Some(x) => {
            let lhs = if variable_regex.is_match(&x["lhs"]) {
                Box::new(Expression::VariableReference(x["lhs"].to_string()))
            } else if number_regex.is_match(&x["lhs"]) {
                Box::new(Expression::NumberLiteral(x["lhs"].parse::<i32>().unwrap()))
            } else {
                panic!("Could not read lhs: {:?}", &x["lhs"])
            };
            let rhs = if variable_regex.is_match(&x["rhs"]) {
                Box::new(Expression::VariableReference(x["rhs"].to_string()))
            } else if number_regex.is_match(&x["rhs"])  {
                Box::new(Expression::NumberLiteral(x["rhs"].parse::<i32>().unwrap()))
            } else {
                Box::new(parse_expression_rhs(x["rhs"].to_string()))
            };
            match &x["op"] {
                "+" => Expression::Add(lhs, rhs),
                "-" => Expression::Sub(lhs, rhs),
                "*" => Expression::Mult(lhs, rhs),
                "/" => Expression::Div(lhs, rhs),
                "**" if number_regex.is_match(&x["rhs"]) => Expression::Pow(lhs, rhs),
                _ => unimplemented!(),
            }
        },
        None => match ifelse_regex.captures(&line) {
            Some(x) => {
                println!("ifelse {:?}", x);
                Expression::NumberLiteral(0)
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
    let definition_regex = Regex::new(r"(?P<lhs>[a-zA-Z]+)\s*=\s*(?P<rhs>[a-zA-Z0-9(==)\?:\s\+\-\*/]+)\s*$").unwrap();
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

pub fn flatten_rhs(defs_flattened: &mut Vec<Definition>, num_variables: &mut i32, rhs: Expression) -> Expression {
    match rhs {
        Expression::Pow(base, exponent) => {
            match exponent {
                box Expression::NumberLiteral(x) if x > 1 => {
                    match base {
                        box Expression::VariableReference(ref var) => {
                            let id = if x > 2 {
                                let tmp_expression = flatten_rhs(
                                    defs_flattened,
                                    num_variables,
                                    Expression::Pow(
                                        box Expression::VariableReference(var.to_string()),
                                        box Expression::NumberLiteral(x - 1)
                                    )
                                );
                                let new_name = format!("sym_{}", num_variables);
                                *num_variables += 1;
                                defs_flattened.push(Definition::Definition(new_name.to_string(), tmp_expression));
                                new_name
                            } else {
                                var.to_string()
                            };
                            Expression::Mult(
                                box Expression::VariableReference(id.to_string()),
                                box Expression::VariableReference(var.to_string())
                            )
                        },
                        box Expression::NumberLiteral(var) => Expression::Mult(
                            box Expression::NumberLiteral(var),
                            box Expression::NumberLiteral(var)
                        ),
                        _ => panic!("Only variables and numbers allowed in pow base")
                    }
                }
                _ => panic!("Expected number as pow exponent"),
            }
        },
        Expression::Add(left, right) => {
            // TODO currently assuming that left is always Number or Variable
            let new_right = match right {
                box Expression::NumberLiteral(x) => Expression::NumberLiteral(x),
                box Expression::VariableReference(ref x) => Expression::VariableReference(x.to_string()),
                box expr => {
                    let tmp_expression = flatten_rhs(
                        defs_flattened,
                        num_variables,
                        expr
                    );
                    let new_name = format!("sym_{}", num_variables);
                    *num_variables += 1;
                    defs_flattened.push(Definition::Definition(new_name.to_string(), tmp_expression));
                    Expression::VariableReference(new_name)
                },
            };
            Expression::Add(left, Box::new(new_right))
        },
        Expression::Sub(left, right) => {
            // TODO currently assuming that left is always Number or Variable
            let new_right = match right {
                box Expression::NumberLiteral(x) => Expression::NumberLiteral(x),
                box Expression::VariableReference(ref x) => Expression::VariableReference(x.to_string()),
                box expr => {
                    let tmp_expression = flatten_rhs(
                        defs_flattened,
                        num_variables,
                        expr
                    );
                    let new_name = format!("sym_{}", num_variables);
                    *num_variables += 1;
                    defs_flattened.push(Definition::Definition(new_name.to_string(), tmp_expression));
                    Expression::VariableReference(new_name)
                },
            };
            Expression::Sub(left, Box::new(new_right))
        },
        Expression::Mult(left, right) => {
            // TODO currently assuming that left is always Number or Variable
            let new_right = match right {
                box Expression::NumberLiteral(x) => Expression::NumberLiteral(x),
                box Expression::VariableReference(ref x) => Expression::VariableReference(x.to_string()),
                box expr => {
                    let tmp_expression = flatten_rhs(
                        defs_flattened,
                        num_variables,
                        expr
                    );
                    let new_name = format!("sym_{}", num_variables);
                    *num_variables += 1;
                    defs_flattened.push(Definition::Definition(new_name.to_string(), tmp_expression));
                    Expression::VariableReference(new_name)
                },
            };
            Expression::Mult(left, Box::new(new_right))
        },
        Expression::Div(left, right) => {
            // TODO currently assuming that left is always Number or Variable
            let new_right = match right {
                box Expression::NumberLiteral(x) => Expression::NumberLiteral(x),
                box Expression::VariableReference(ref x) => Expression::VariableReference(x.to_string()),
                box expr => {
                    let tmp_expression = flatten_rhs(
                        defs_flattened,
                        num_variables,
                        expr
                    );
                    let new_name = format!("sym_{}", num_variables);
                    *num_variables += 1;
                    defs_flattened.push(Definition::Definition(new_name.to_string(), tmp_expression));
                    Expression::VariableReference(new_name)
                },
            };
            Expression::Div(left, Box::new(new_right))
        },
        _ => panic!("Already flattened or not implemented"),
    }
}

pub fn flatten_program(prog: Prog) -> Prog {
    let mut defs_flattened = Vec::new();
    let mut num_variables: i32 = 0;
    for def in prog.defs {
        match def {
            Definition::Return(expr) => {
                let rhs = flatten_rhs(&mut defs_flattened, &mut num_variables, expr);
                defs_flattened.push(Definition::Return(rhs));
            },
            Definition::Definition(id, expr) => {
                let rhs = flatten_rhs(&mut defs_flattened, &mut num_variables, expr);
                defs_flattened.push(Definition::Definition(id, rhs));
            },
            Definition::IfElse(_, _, _) => unimplemented!(),
        }
    }
    Prog { id: prog.id, args: prog.args, defs: defs_flattened }
}
