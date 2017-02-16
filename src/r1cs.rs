/**
 * @file r1cs.rs
 * @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
 * @date 2017
 */

use absy::*;
use absy::Expression::*;
use std::collections::HashMap;

fn count_variables_add(expr: Expression) -> HashMap<String, i32> {
    let mut count = HashMap::new();
    match expr {
        NumberLiteral(x) => { count.insert("~one".to_string(), x); },
        VariableReference(var) => { count.insert(var, 1); },
        Add(box lhs, box rhs) => {
            match (lhs, rhs) {
                (NumberLiteral(x), NumberLiteral(y)) => {
                    let num = count.entry("~one".to_string()).or_insert(0);
                    *num += x + y;
                },
                (VariableReference(v), NumberLiteral(x)) |
                (NumberLiteral(x), VariableReference(v)) => {
                    {
                        let num = count.entry("~one".to_string()).or_insert(0);
                        *num += x;
                    }
                    let var = count.entry(v).or_insert(0);
                    *var += 1;
                },
                (VariableReference(v1), VariableReference(v2)) => {
                    {
                        let var1 = count.entry(v1).or_insert(0);
                        *var1 += 1;
                    }
                    let var2 = count.entry(v2).or_insert(0);
                    *var2 += 1;
                },
                (NumberLiteral(x), e @ Add(..)) |
                (e @ Add(..), NumberLiteral(x)) => {
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
                (VariableReference(v), e @ Add(..)) |
                (e @ Add(..), VariableReference(v)) => {
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
                (NumberLiteral(x), Mult(box NumberLiteral(n), box VariableReference(v))) |
                (NumberLiteral(x), Mult(box VariableReference(v), box NumberLiteral(n))) |
                (Mult(box NumberLiteral(n), box VariableReference(v)), NumberLiteral(x)) |
                (Mult(box VariableReference(v), box NumberLiteral(n)), NumberLiteral(x)) => {
                    {
                        let num = count.entry("~one".to_string()).or_insert(0);
                        *num += x;
                    }
                    let var = count.entry(v).or_insert(0);
                    *var += n;
                },
                (VariableReference(v1), Mult(box NumberLiteral(n), box VariableReference(v2))) |
                (VariableReference(v1), Mult(box VariableReference(v2), box NumberLiteral(n))) |
                (Mult(box NumberLiteral(n), box VariableReference(v2)), VariableReference(v1)) |
                (Mult(box VariableReference(v2), box NumberLiteral(n)), VariableReference(v1)) => {
                    {
                        let var = count.entry(v1).or_insert(0);
                        *var += 1;
                    }
                    let var = count.entry(v2).or_insert(0);
                    *var += n;
                },
                (e @ Add(..), Mult(box NumberLiteral(n), box VariableReference(v))) |
                (e @ Add(..), Mult(box VariableReference(v), box NumberLiteral(n))) |
                (Mult(box NumberLiteral(n), box VariableReference(v)), e @ Add(..)) |
                (Mult(box VariableReference(v), box NumberLiteral(n)), e @ Add(..)) => {
                    {
                        let var = count.entry(v).or_insert(0);
                        *var += n;
                    }
                    let vars = count_variables_add(e);
                    for (key, value) in &vars {
                        let val = count.entry(key.to_string()).or_insert(0);
                        *val += *value;
                    }
                },
                (Mult(box VariableReference(v1), box NumberLiteral(n1)), Mult(box VariableReference(v2), box NumberLiteral(n2))) => {
                    {
                        let var = count.entry(v1).or_insert(0);
                        *var += n1;
                    }
                    let var = count.entry(v2).or_insert(0);
                    *var += n2;
                },
                e @ _ => panic!("Error: Add({}, {})", e.0, e.1),
            }
        },
        e @ _ => panic!("Statement::Add expected, got: {}", e),
    }
    count
}

// lhs = rhy
fn swap_sub(lhs: &Expression, rhs: &Expression) -> (Expression, Expression) {
    match (lhs.clone(), rhs.clone()) {
        // TODO need all cases? need more?
        (v1 @ NumberLiteral(_), v2 @ NumberLiteral(_)) |
        (v1 @ VariableReference(_), v2 @ NumberLiteral(_)) |
        (v1 @ NumberLiteral(_), v2 @ VariableReference(_)) |
        (v1 @ VariableReference(_), v2 @ VariableReference(_)) |
        (v1 @ VariableReference(_), v2 @ Mult(..)) |
        (v1 @ Mult(..), v2 @ VariableReference(_)) => (v1, v2),
        (Add(left, box right), var @ VariableReference(_)) |
        (var @ VariableReference(_), Add(left, box right)) => { // var = left + right
            let (l, r) = swap_sub(&var, &right);
            (l, Add(left, box r))
        },
        (Sub(box left, box right), v @ VariableReference(_)) |
        (v @ VariableReference(_), Sub(box left, box right)) |
        (Sub(box left, box right), v @ NumberLiteral(_)) |
        (v @ NumberLiteral(_), Sub(box left, box right)) => {
            let (l, r) = swap_sub(&left, &right);
            (Add(box v, box r), l)
        },
        e @ _ => panic!("Unexpected input: {} = {}", e.0, e.1),
    }
}

pub fn r1cs_expression(idx: usize, expr: Expression, variables: &mut Vec<String>, a_row: &mut Vec<(usize, i32)>, b_row: &mut Vec<(usize, i32)>, c_row: &mut Vec<(usize, i32)>) {
    match expr {
        e @ Add(..) |
        e @ Sub(..) => { // a - b = c --> b + c = a
            let (lhs, rhs) = swap_sub(&VariableReference(variables[idx].to_string()), &e);
            for (key, value) in count_variables_add(rhs) {
                a_row.push((variables.iter().position(|r| r == &key).unwrap(), value));
            }
            b_row.push((0, 1));
            for (key, value) in count_variables_add(lhs) {
                c_row.push((variables.iter().position(|r| r == &key).unwrap(), value));
            }
        },
        Mult(lhs, rhs) => {
            c_row.push((idx, 1));
            match lhs {
                box NumberLiteral(x) => a_row.push((0, x)),
                box VariableReference(x) => a_row.push((variables.iter().position(|r| r == &x).unwrap(), 1)),
                box e @ Add(..) => for (key, value) in count_variables_add(e) {
                    a_row.push((variables.iter().position(|r| r == &key).unwrap(), value));
                },
                e @ _ => panic!("Not flattened: {}", e),
            };
            match rhs {
                box NumberLiteral(x) => b_row.push((0, x)),
                box VariableReference(x) => b_row.push((variables.iter().position(|r| r == &x).unwrap(), 1)),
                box e @ Add(..) => for (key, value) in count_variables_add(e) {
                    b_row.push((variables.iter().position(|r| r == &key).unwrap(), value));
                },
                e @ _ => panic!("Not flattened: {}", e),
            };
        },
        Div(lhs, rhs) => { // a / b = c --> c * b = a
            a_row.push((idx, 1));
            match lhs {
                box NumberLiteral(x) => c_row.push((0, x)),
                box VariableReference(x) => c_row.push((variables.iter().position(|r| r == &x).unwrap(), 1)),
                _ => unimplemented!(),
            };
            match rhs {
                box NumberLiteral(x) => b_row.push((0, x)),
                box VariableReference(x) => b_row.push((variables.iter().position(|r| r == &x).unwrap(), 1)),
                _ => unimplemented!(),
            };
        },
        Pow(_, _) => panic!("Pow not flattened"),
        IfElse(_, _, _) => panic!("IfElse not flattened"),
        VariableReference(var) => {
            a_row.push((variables.iter().position(|r| r == &var).unwrap(), 1));
            b_row.push((0, 1));
            c_row.push((idx, 1));
        },
        NumberLiteral(x) => {
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
    variables.extend(prog.arguments.iter().map(|x| format!("{}", x)));
    for def in &prog.statements {
        let mut a_row: Vec<(usize, i32)> = Vec::new();
        let mut b_row: Vec<(usize, i32)> = Vec::new();
        let mut c_row: Vec<(usize, i32)> = Vec::new();
        let idx = variables.len();
        match *def {
            Statement::Return(ref expr) => {
                variables.push("~out".to_string());
                r1cs_expression(idx, expr.clone(), &mut variables, &mut a_row, &mut b_row, &mut c_row);
            },
            Statement::Definition(ref id, ref expr) => {
                variables.push(id.to_string());
                r1cs_expression(idx, expr.clone(), &mut variables, &mut a_row, &mut b_row, &mut c_row);
            },
            Statement::Condition(..) => unimplemented!(),
        }
        a.push(a_row);
        b.push(b_row);
        c.push(c_row);
    }
    (variables, a, b, c)
}
