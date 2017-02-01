use ast::*;
use std::collections::HashMap;

fn count_variables_add(expr: Expression) -> HashMap<String, i32> {
    let mut count = HashMap::new();
    match expr {
        Expression::Add(box lhs, box rhs) => {
            match (lhs, rhs) {
                (Expression::NumberLiteral(x), Expression::NumberLiteral(y)) => {
                    let num = count.entry("~one".to_string()).or_insert(0);
                    *num += x + y;
                },
                (Expression::VariableReference(v), Expression::NumberLiteral(x)) |
                (Expression::NumberLiteral(x), Expression::VariableReference(v)) => {
                    {
                        let num = count.entry("~one".to_string()).or_insert(0);
                        *num += x;
                    }
                    let var = count.entry(v).or_insert(0);
                    *var += 1;
                },
                (Expression::VariableReference(v1), Expression::VariableReference(v2)) => {
                    {
                        let var1 = count.entry(v1).or_insert(0);
                        *var1 += 1;
                    }
                    let var2 = count.entry(v2).or_insert(0);
                    *var2 += 1;
                },
                (Expression::NumberLiteral(x), e @ Expression::Add(..)) |
                (e @ Expression::Add(..), Expression::NumberLiteral(x)) => {
                    {
                        let num = count.entry("~one".to_string()).or_insert(0);
                        *num += x;
                    }
                    let vars = count_variables_add(e);
                    for (key, value) in &vars {
                        let val = count.entry(key.to_string()).or_insert(0);
                        *val += *value;
                    }
                },
                (Expression::VariableReference(v), e @ Expression::Add(..)) |
                (e @ Expression::Add(..), Expression::VariableReference(v)) => {
                    {
                        let var = count.entry(v).or_insert(0);
                        *var += 1;
                    }
                    let vars = count_variables_add(e);
                    for (key, value) in &vars {
                        let val = count.entry(key.to_string()).or_insert(0);
                        *val += *value;
                    }
                },
                (Expression::NumberLiteral(x), Expression::Mult(box Expression::NumberLiteral(n), box Expression::VariableReference(v))) |
                (Expression::NumberLiteral(x), Expression::Mult(box Expression::VariableReference(v), box Expression::NumberLiteral(n))) |
                (Expression::Mult(box Expression::NumberLiteral(n), box Expression::VariableReference(v)), Expression::NumberLiteral(x)) |
                (Expression::Mult(box Expression::VariableReference(v), box Expression::NumberLiteral(n)), Expression::NumberLiteral(x)) => {
                    {
                        let num = count.entry("~one".to_string()).or_insert(0);
                        *num += x;
                    }
                    let var = count.entry(v).or_insert(0);
                    *var += n;
                },
                e @ _ => panic!("Error: Add({}, {})", e.0, e.1),
            }
        },
        e @ _ => panic!("Definition::Add expected, got: {}", e),
    }
    count
}

pub fn r1cs_expression(idx: usize, expr: Expression, variables: &mut Vec<String>, a_row: &mut Vec<(usize, i32)>, b_row: &mut Vec<(usize, i32)>, c_row: &mut Vec<(usize, i32)>) {
    match expr {
        e @ Expression::Add(..) => {
            for (key, value) in count_variables_add(e) {
                a_row.push((variables.iter().position(|r| r == &key).unwrap(), value));
            }
            b_row.push((0, 1));
            c_row.push((idx, 1));
        },
        Expression::Sub(lhs, rhs) => { // a - b = c --> b + c = a
            for (key, value) in count_variables_add(Expression::Add(rhs, box Expression::VariableReference(variables[idx].to_string()))) {
                a_row.push((variables.iter().position(|r| r == &key).unwrap(), value));
            }
            b_row.push((0, 1));
            match lhs {
                box Expression::NumberLiteral(x) => c_row.push((0, x)),
                box Expression::VariableReference(x) => c_row.push((variables.iter().position(|r| r == &x).unwrap(), 1)),
                e @ _ => panic!("unimplemented: {}", e),
            };

            // a_row.push((idx, 1));
            // match lhs {
            //     box Expression::NumberLiteral(x) => c_row.push((0, x)),
            //     box Expression::VariableReference(x) => c_row.push((variables.iter().position(|r| r == &x).unwrap(), 1)),
            //     _ => panic!("Not flattened!"),
            // };
            // match rhs {
            //     box Expression::NumberLiteral(x) => b_row.push((0, x)),
            //     box Expression::VariableReference(x) => b_row.push((variables.iter().position(|r| r == &x).unwrap(), 1)),
            //     _ => panic!("Not flattened!"),
            // };
        },
        Expression::Mult(lhs, rhs) => {
            c_row.push((idx, 1));
            match lhs {
                box Expression::NumberLiteral(x) => a_row.push((0, x)),
                box Expression::VariableReference(x) => a_row.push((variables.iter().position(|r| r == &x).unwrap(), 1)),
                box e @ Expression::Add(..) => for (key, value) in count_variables_add(e) {
                    a_row.push((variables.iter().position(|r| r == &key).unwrap(), value));
                },
                e @ _ => panic!("Not flattened: {}", e),
            };
            match rhs {
                box Expression::NumberLiteral(x) => b_row.push((0, x)),
                box Expression::VariableReference(x) => b_row.push((variables.iter().position(|r| r == &x).unwrap(), 1)),
                box e @ Expression::Add(..) => for (key, value) in count_variables_add(e) {
                    b_row.push((variables.iter().position(|r| r == &key).unwrap(), value));
                },
                e @ _ => panic!("Not flattened: {}", e),
            };
        },
        Expression::Div(lhs, rhs) => { // a / b = c --> c * b = a
            a_row.push((idx, 1));
            match lhs {
                box Expression::NumberLiteral(x) => c_row.push((0, x)),
                box Expression::VariableReference(x) => c_row.push((variables.iter().position(|r| r == &x).unwrap(), 1)),
                _ => panic!("Not flattened!"),
            };
            match rhs {
                box Expression::NumberLiteral(x) => b_row.push((0, x)),
                box Expression::VariableReference(x) => b_row.push((variables.iter().position(|r| r == &x).unwrap(), 1)),
                _ => panic!("Not flattened!"),
            };
        },
        Expression::Pow(_, _) => panic!("Pow not flattened"),
        Expression::IfElse(_, _, _) => panic!("IfElse not flattened"),
        Expression::VariableReference(var) => {
            a_row.push((variables.iter().position(|r| r == &var).unwrap(), 1));
            b_row.push((0, 1));
            c_row.push((idx, 1));
        },
        Expression::NumberLiteral(x) => {
            a_row.push((0, x));
            b_row.push((0, 1));
            c_row.push((idx, 1));
        },
    }
}

pub fn r1cs_program(prog: &Prog) -> (Vec<String>, Vec<Vec<(usize, i32)>>, Vec<Vec<(usize, i32)>>, Vec<Vec<(usize, i32)>>){
    let mut variables: Vec<String> = Vec::new();
    variables.push("~one".to_string());
    let mut a: Vec<Vec<(usize, i32)>> = Vec::new();
    let mut b: Vec<Vec<(usize, i32)>> = Vec::new();
    let mut c: Vec<Vec<(usize, i32)>> = Vec::new();
    variables.extend(prog.args.iter().map(|x| format!("{}", x)));
    for def in &prog.defs {
        let mut a_row: Vec<(usize, i32)> = Vec::new();
        let mut b_row: Vec<(usize, i32)> = Vec::new();
        let mut c_row: Vec<(usize, i32)> = Vec::new();
        let idx = variables.len();
        match *def {
            Definition::Return(ref expr) => {
                variables.push("~out".to_string());
                r1cs_expression(idx, expr.clone(), &mut variables, &mut a_row, &mut b_row, &mut c_row);
            },
            Definition::Definition(ref id, ref expr) => {
                variables.push(id.to_string());
                r1cs_expression(idx, expr.clone(), &mut variables, &mut a_row, &mut b_row, &mut c_row);
            },
        }
        a.push(a_row);
        b.push(b_row);
        c.push(c_row);
    }
    (variables, a, b, c)
}
