use ast::*;

pub fn r1cs_expression(idx: usize, expr: Expression, variables: &mut Vec<String>, a_row: &mut Vec<(usize, i32)>, b_row: &mut Vec<(usize, i32)>, c_row: &mut Vec<(usize, i32)>) {
    match expr {
        Expression::Add(lhs, rhs) => {
            c_row.push((idx, 1));
            match (lhs, rhs) {
                (box Expression::VariableReference(ref x1), box Expression::VariableReference(ref x2)) if x1 == x2 => {
                    a_row.push((variables.iter().position(|r| r == x1).unwrap(), 2));
                    b_row.push((0, 1));
                },
                (box Expression::VariableReference(ref x1), box Expression::VariableReference(ref x2)) /*if x1 != x2*/ => {
                    a_row.push((variables.iter().position(|r| r == x1).unwrap(), 1));
                    a_row.push((variables.iter().position(|r| r == x2).unwrap(), 1));
                    b_row.push((0, 1));
                },
                (box Expression::NumberLiteral(num), box Expression::VariableReference(ref x)) |
                (box Expression::VariableReference(ref x), box Expression::NumberLiteral(num)) => {
                    a_row.push((0, num));
                    a_row.push((variables.iter().position(|r| r == x).unwrap(), 1));
                    b_row.push((0, 1));
                }
                _ => panic!("Not flattened!"),
            }
        },
        Expression::Sub(lhs, rhs) => { // a - b = c --> c + b = a
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
        Expression::Mult(lhs, rhs) => {
            c_row.push((idx, 1));
            match lhs {
                box Expression::NumberLiteral(x) => a_row.push((0, x)),
                box Expression::VariableReference(x) => a_row.push((variables.iter().position(|r| r == &x).unwrap(), 1)),
                _ => panic!("Not flattened!"),
            };
            match rhs {
                box Expression::NumberLiteral(x) => b_row.push((0, x)),
                box Expression::VariableReference(x) => b_row.push((variables.iter().position(|r| r == &x).unwrap(), 1)),
                _ => panic!("Not flattened!"),
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
