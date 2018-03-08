//! Module containing necessary functions to convert a flattened program or expression to r1cs.
//!
//! @file r1cs.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de
//! @date 2017

use std::collections::HashMap;
use absy::*;
use absy::Expression::*;
use field::Field;

/// Returns a vector of summands of the given `Expression`.
///
/// # Arguments
///
/// * `expr` - `Expression` to be split to summands.
///
/// # Example
///
/// a + 2*b + (c - d) -> [a, 2*b, c-d]
fn get_summands<T: Field>(expr: &Expression<T>) -> Vec<&Expression<T>> {
    let mut trace = Vec::new();
    let mut add = Vec::new();
    trace.push(expr);
    loop {
        if let Some(e) = trace.pop() {
            match *e {
                ref e @ Number(_) | ref e @ Identifier(_) | ref e @ Mult(..) | ref e @ Sub(..)
                    if e.is_linear() =>
                {
                    add.push(e)
                }
                Add(ref l, ref r) => {
                    trace.push(l);
                    trace.push(r);
                }
                ref e => panic!("Not covered: {}", e),
            }
        } else {
            return add;
        }
    }
}

/// Returns a `HashMap` containing variables and the number of occurences
///
/// # Arguments
///
/// * `expr` - Expression only containing Numbers, Variables, Add and Mult
///
/// # Example
///
/// `7 * x + 4 * y + x` -> { x => 8, y = 4 }
fn count_variables_add<T: Field>(expr: &Expression<T>) -> HashMap<String, T> {
    let summands = get_summands(expr);
    let mut count = HashMap::new();
    for s in summands {
        match *s {
            Number(ref x) => {
                let num = count.entry("~one".to_string()).or_insert(T::zero());
                *num = num.clone() + x;
            }
            Identifier(ref v) => {
                let num = count.entry(v.to_string()).or_insert(T::zero());
                *num = num.clone() + T::one();
            }
            Mult(box Number(ref x1), box Number(ref x2)) => {
                let num = count.entry("~one".to_string()).or_insert(T::zero());
                *num = num.clone() + x1 + x2;
            }
            Mult(box Number(ref x), box Identifier(ref v)) |
            Mult(box Identifier(ref v), box Number(ref x)) => {
                let num = count.entry(v.to_string()).or_insert(T::zero());
                *num = num.clone() + x;
            }
            ref e => panic!("Not covered: {}", e),
        }
    }
    count
}

/// Returns an equation equivalent to `lhs == rhs` only using `Add` and `Mult`
///
/// # Arguments
///
/// * `lhs` - Leht hand side of the equation
/// * `rhs` - Right hand side of the equation
fn swap_sub<T: Field>(lhs: &Expression<T>, rhs: &Expression<T>) -> (Expression<T>, Expression<T>) {
    let mut left = get_summands(lhs);
    let mut right = get_summands(rhs);
    let mut run = true;
    while run {
        run = false;
        for i in 0..left.len() {
            match *left[i] {
                ref e @ Number(_) | ref e @ Identifier(_) | ref e @ Mult(..) if e.is_linear() => {}
                Sub(ref l, ref r) => {
                    run = true;
                    left.swap_remove(i);
                    left.extend(get_summands(l));
                    right.extend(get_summands(r));
                }
                ref e => panic!("Unexpected: {}", e),
            }
        }
        for i in 0..right.len() {
            match *right[i] {
                ref e @ Number(_) | ref e @ Identifier(_) | ref e @ Mult(..) if e.is_linear() => {}
                Sub(ref l, ref r) => {
                    run = true;
                    right.swap_remove(i);
                    right.extend(get_summands(l));
                    left.extend(get_summands(r));
                }
                ref e => panic!("Unexpected: {}", e),
            }
        }
    }
    if let Some(left_init) = left.pop() {
        if let Some(right_init) = right.pop() {
            return (
                left.iter()
                    .fold(left_init.clone(), |acc, &x| Add(box acc, box x.clone())),
                right
                    .iter()
                    .fold(right_init.clone(), |acc, &x| Add(box acc, box x.clone())),
            );
        }
    }
    panic!("Unexpected");
}

/// Calculates one R1CS row representation for `linear_expr` = `expr`.
/// (<C,x> = <A,x>*<B,x>)
///
/// # Arguments
///
/// * `linear_expr` - Left hand side of the equation, has to be linear
/// * `expr` - Right hand side of the equation
/// * `variables` - A mutual vector that contains all existing variables. Not found variables will be added.
/// * `a_row` - Result row of matrix A
/// * `b_row` - Result row of matrix B
/// * `c_row` - Result row of matrix C
fn r1cs_expression<T: Field>(
    linear_expr: Expression<T>,
    expr: Expression<T>,
    variables: &mut Vec<String>,
    a_row: &mut Vec<(usize, T)>,
    b_row: &mut Vec<(usize, T)>,
    c_row: &mut Vec<(usize, T)>,
) {
    assert!(linear_expr.is_linear());

    match expr {
        e @ Add(..) | e @ Sub(..) => {
            let (lhs, rhs) = swap_sub(&linear_expr, &e);
            for (key, value) in count_variables_add(&rhs) {
                a_row.push((get_variable_idx(variables, &key), value));
            }
            b_row.push((0, T::one()));
            for (key, value) in count_variables_add(&lhs) {
                c_row.push((get_variable_idx(variables, &key), value));
            }
        }
        Mult(lhs, rhs) => {
            match lhs {
                box Number(x) => a_row.push((0, x)),
                box Identifier(x) => a_row.push((get_variable_idx(variables, &x), T::one())),
                box e @ Add(..) => for (key, value) in count_variables_add(&e) {
                    a_row.push((get_variable_idx(variables, &key), value));
                },
                e @ _ => panic!("Not flattened: {}", e),
            };
            match rhs {
                box Number(x) => b_row.push((0, x)),
                box Identifier(x) => b_row.push((get_variable_idx(variables, &x), T::one())),
                box e @ Add(..) => for (key, value) in count_variables_add(&e) {
                    b_row.push((get_variable_idx(variables, &key), value));
                },
                e @ _ => panic!("Not flattened: {}", e),
            };
            for (key, value) in count_variables_add(&linear_expr) {
                c_row.push((get_variable_idx(variables, &key), value));
            }
        }
        Div(lhs, rhs) => {
            // a / b = c --> c * b = a
            match lhs {
                box Number(x) => c_row.push((0, x)),
                box Identifier(x) => c_row.push((get_variable_idx(variables, &x), T::one())),
                box e @ Add(..) => for (key, value) in count_variables_add(&e) {
                    c_row.push((get_variable_idx(variables, &key), value));
                },
                box e @ Sub(..) => {
                    return r1cs_expression(
                        Mult(box linear_expr, rhs),
                        e,
                        variables,
                        a_row,
                        b_row,
                        c_row,
                    )
                }
                box Mult(box Number(ref x1), box Number(ref x2)) => {
                    c_row.push((0, x1.clone() * x2))
                }
                box Mult(box Number(ref x), box Identifier(ref v)) |
                box Mult(box Identifier(ref v), box Number(ref x)) => {
                    c_row.push((get_variable_idx(variables, v), x.clone()))
                }
                e @ _ => panic!("(lhs) not supported: {:?}", e),
            };
            match rhs {
                box Number(x) => b_row.push((0, x)),
                box Identifier(x) => b_row.push((get_variable_idx(variables, &x), T::one())),
                box Mult(box Number(ref x1), box Number(ref x2)) => {
                    b_row.push((0, x1.clone() * x2))
                }
                box Mult(box Number(ref x), box Identifier(ref v)) |
                box Mult(box Identifier(ref v), box Number(ref x)) => {
                    b_row.push((get_variable_idx(variables, v), x.clone()))
                }
                e @ _ => panic!("(rhs) not supported: {:?}", e),
            };
            for (key, value) in count_variables_add(&linear_expr) {
                a_row.push((get_variable_idx(variables, &key), value));
            }
        }
        Pow(_, _) => panic!("Pow not flattened"),
        IfElse(_, _, _) => panic!("IfElse not flattened"),
        FunctionCall(_, _) => panic!("FunctionCall not flattened"),
        Identifier(var) => {
            a_row.push((get_variable_idx(variables, &var), T::one()));
            b_row.push((0, T::one()));
            for (key, value) in count_variables_add(&linear_expr) {
                c_row.push((get_variable_idx(variables, &key), value));
            }
        }
        Number(x) => {
            a_row.push((0, x));
            b_row.push((0, T::one()));
            for (key, value) in count_variables_add(&linear_expr) {
                c_row.push((get_variable_idx(variables, &key), value));
            }
        }
    }
}

/// Returns the index of `var` in the vector `variables` or adds `var`.
///
/// # Arguments
///
/// * `variables` - A mutual vector that contains all existing variables. Not found variables will be added.
/// * `var` - Variable to be searched for.
fn get_variable_idx(variables: &mut Vec<String>, var: &String) -> usize {
    match variables.iter().position(|r| r == var) {
        Some(x) => x,
        None => {
            variables.push(var.to_string());
            variables.len() - 1
        }
    }
}

/// Calculates one R1CS row representation of a program and returns (V, A, B, C) so that:
/// * `V` contains all used variables and the index in the vector represents the used number in `A`, `B`, `C`
/// * `<A,x>*<B,x> = <C,x>` for a witness `x`
///
/// # Arguments
///
/// * `prog` - The program the representation is calculated for.
pub fn r1cs_program<T: Field>(
    prog: &Prog<T>,
) -> (
    Vec<String>,
    usize,
    Vec<Vec<(usize, T)>>,
    Vec<Vec<(usize, T)>>,
    Vec<Vec<(usize, T)>>,
) {
    let mut variables: Vec<String> = Vec::new();
    variables.push("~one".to_string());
    let mut a: Vec<Vec<(usize, T)>> = Vec::new();
    let mut b: Vec<Vec<(usize, T)>> = Vec::new();
    let mut c: Vec<Vec<(usize, T)>> = Vec::new();

    //Only the main function is relevant in this step, since all calls to other functions were resolved during flattening
    let main = prog.functions
        .iter()
        .find(|x: &&Function<T>| x.id == "main".to_string())
        .unwrap();
    variables.extend(main.arguments.iter().filter(|x| !x.private).map(|x| format!("{}", x)));

    // ~out is added after main's arguments as we want variables (columns)
    // in the r1cs to be aligned like "public inputs | private inputs"
    for i in 0..main.return_count {
        variables.push(format!("~out_{}", i).to_string());
    }

    // position where private part of witness starts
    let private_inputs_offset = variables.len();

    for def in &main.statements {
        match *def {
            Statement::Return(ref list) => {
                for (i, val) in list.expressions.iter().enumerate() {
                    let mut a_row: Vec<(usize, T)> = Vec::new();
                    let mut b_row: Vec<(usize, T)> = Vec::new();
                    let mut c_row: Vec<(usize, T)> = Vec::new();
                    r1cs_expression(
                        Identifier(format!("~out_{}", i).to_string()),
                        val.clone(),
                        &mut variables,
                        &mut a_row,
                        &mut b_row,
                        &mut c_row,
                    );
                    a.push(a_row);
                    b.push(b_row);
                    c.push(c_row);
                }
            },
            Statement::Definition(_, _) => continue,
            Statement::Condition(ref expr1, ref expr2) => {
                let mut a_row: Vec<(usize, T)> = Vec::new();
                let mut b_row: Vec<(usize, T)> = Vec::new();
                let mut c_row: Vec<(usize, T)> = Vec::new();
                r1cs_expression(
                    expr1.clone(),
                    expr2.clone(),
                    &mut variables,
                    &mut a_row,
                    &mut b_row,
                    &mut c_row,
                );
                a.push(a_row);
                b.push(b_row);
                c.push(c_row);
            },
            Statement::For(..) => panic!("For-loop not flattened"),
            Statement::Compiler(..) => continue,
            Statement::MultipleDefinition(..) => unimplemented!(),
        }
    }
    (variables, private_inputs_offset, a, b, c)
}

#[cfg(test)]
mod tests {
    use super::*;
    use field::FieldPrime;
    use std::cmp::Ordering;

    /// Sort function for tuples `(x, y)` which sorts based on `x` first.
    /// If `x` is equal, `y` is used for comparison.
    fn sort_tup<A: Ord, B: Ord>(a: &(A, B), b: &(A, B)) -> Ordering {
        if a.0 == b.0 {
            a.1.cmp(&b.1)
        } else {
            a.0.cmp(&b.0)
        }
    }

    #[cfg(test)]
    mod r1cs_expression {
        use super::*;

        #[test]
        fn add() {
            // x = y + 5
            let lhs = Identifier(String::from("x"));
            let rhs = Add(
                box Identifier(String::from("y")),
                box Number(FieldPrime::from(5)),
            );
            let mut variables: Vec<String> = vec!["~one", "x", "y"]
                .iter()
                .map(|&x| String::from(x))
                .collect();
            let mut a_row: Vec<(usize, FieldPrime)> = Vec::new();
            let mut b_row: Vec<(usize, FieldPrime)> = Vec::new();
            let mut c_row: Vec<(usize, FieldPrime)> = Vec::new();

            r1cs_expression(lhs, rhs, &mut variables, &mut a_row, &mut b_row, &mut c_row);
            a_row.sort_by(sort_tup);
            b_row.sort_by(sort_tup);
            c_row.sort_by(sort_tup);
            assert_eq!(
                vec![(0, FieldPrime::from(5)), (2, FieldPrime::from(1))],
                a_row
            );
            assert_eq!(vec![(0, FieldPrime::from(1))], b_row);
            assert_eq!(vec![(1, FieldPrime::from(1))], c_row);
        }

        #[test]
        fn add_sub_mix() {
            // (x + y) - ((z + 3*x) - y) == (x - y) + ((2*x - 4*y) + (4*y - 2*z))
            // --> (x + y) + y + 4y + 2z + y == x + 2x + 4y + (z + 3x)
            // <=> x + 7*y + 2*z == 6*x + 4y + z
            let lhs = Sub(
                box Add(
                    box Identifier(String::from("x")),
                    box Identifier(String::from("y")),
                ),
                box Sub(
                    box Add(
                        box Identifier(String::from("z")),
                        box Mult(
                            box Number(FieldPrime::from(3)),
                            box Identifier(String::from("x")),
                        ),
                    ),
                    box Identifier(String::from("y")),
                ),
            );
            let rhs = Add(
                box Sub(
                    box Identifier(String::from("x")),
                    box Identifier(String::from("y")),
                ),
                box Add(
                    box Sub(
                        box Mult(
                            box Number(FieldPrime::from(2)),
                            box Identifier(String::from("x")),
                        ),
                        box Mult(
                            box Number(FieldPrime::from(4)),
                            box Identifier(String::from("y")),
                        ),
                    ),
                    box Sub(
                        box Mult(
                            box Number(FieldPrime::from(4)),
                            box Identifier(String::from("y")),
                        ),
                        box Mult(
                            box Number(FieldPrime::from(2)),
                            box Identifier(String::from("z")),
                        ),
                    ),
                ),
            );
            let mut variables: Vec<String> = vec!["~one", "x", "y", "z"]
                .iter()
                .map(|&x| String::from(x))
                .collect();
            let mut a_row: Vec<(usize, FieldPrime)> = Vec::new();
            let mut b_row: Vec<(usize, FieldPrime)> = Vec::new();
            let mut c_row: Vec<(usize, FieldPrime)> = Vec::new();

            r1cs_expression(lhs, rhs, &mut variables, &mut a_row, &mut b_row, &mut c_row);
            a_row.sort_by(sort_tup);
            b_row.sort_by(sort_tup);
            c_row.sort_by(sort_tup);
            assert_eq!(
                vec![
                    (1, FieldPrime::from(6)),
                    (2, FieldPrime::from(4)),
                    (3, FieldPrime::from(1)),
                ],
                a_row
            );
            assert_eq!(vec![(0, FieldPrime::from(1))], b_row);
            assert_eq!(
                vec![
                    (1, FieldPrime::from(1)),
                    (2, FieldPrime::from(7)),
                    (3, FieldPrime::from(2)),
                ],
                c_row
            );
        }

        #[test]
        fn sub() {
            // 7 * x + y == 3 * y - z * 6
            let lhs = Add(
                box Mult(
                    box Number(FieldPrime::from(7)),
                    box Identifier(String::from("x")),
                ),
                box Identifier(String::from("y")),
            );
            let rhs = Sub(
                box Mult(
                    box Number(FieldPrime::from(3)),
                    box Identifier(String::from("y")),
                ),
                box Mult(
                    box Identifier(String::from("z")),
                    box Number(FieldPrime::from(6)),
                ),
            );
            let mut variables: Vec<String> = vec!["~one", "x", "y", "z"]
                .iter()
                .map(|&x| String::from(x))
                .collect();
            let mut a_row: Vec<(usize, FieldPrime)> = Vec::new();
            let mut b_row: Vec<(usize, FieldPrime)> = Vec::new();
            let mut c_row: Vec<(usize, FieldPrime)> = Vec::new();

            r1cs_expression(lhs, rhs, &mut variables, &mut a_row, &mut b_row, &mut c_row);
            a_row.sort_by(sort_tup);
            b_row.sort_by(sort_tup);
            c_row.sort_by(sort_tup);
            assert_eq!(vec![(2, FieldPrime::from(3))], a_row); // 3 * y
            assert_eq!(vec![(0, FieldPrime::from(1))], b_row); // 1
            assert_eq!(
                vec![
                    (1, FieldPrime::from(7)),
                    (2, FieldPrime::from(1)),
                    (3, FieldPrime::from(6)),
                ],
                c_row
            ); // (7 * x + y) + z * 6
        }

        #[test]
        fn sub_multiple() {
            // (((3 * y) - (z * 2)) - (x * 12)) == (a - x)
            // --> 3*y + x == a + 12*x + 2*z
            let lhs = Sub(
                box Sub(
                    box Mult(
                        box Number(FieldPrime::from(3)),
                        box Identifier(String::from("y")),
                    ),
                    box Mult(
                        box Identifier(String::from("z")),
                        box Number(FieldPrime::from(2)),
                    ),
                ),
                box Mult(
                    box Identifier(String::from("x")),
                    box Number(FieldPrime::from(12)),
                ),
            );
            let rhs = Sub(
                box Identifier(String::from("a")),
                box Identifier(String::from("x")),
            );
            let mut variables: Vec<String> = vec!["~one", "x", "y", "z", "a"]
                .iter()
                .map(|&x| String::from(x))
                .collect();
            let mut a_row: Vec<(usize, FieldPrime)> = Vec::new();
            let mut b_row: Vec<(usize, FieldPrime)> = Vec::new();
            let mut c_row: Vec<(usize, FieldPrime)> = Vec::new();

            r1cs_expression(lhs, rhs, &mut variables, &mut a_row, &mut b_row, &mut c_row);
            a_row.sort_by(sort_tup);
            b_row.sort_by(sort_tup);
            c_row.sort_by(sort_tup);
            assert_eq!(
                vec![
                    (1, FieldPrime::from(12)),
                    (3, FieldPrime::from(2)),
                    (4, FieldPrime::from(1)),
                ],
                a_row
            ); // a + 12*x + 2*z
            assert_eq!(vec![(0, FieldPrime::from(1))], b_row); // 1
            assert_eq!(
                vec![(1, FieldPrime::from(1)), (2, FieldPrime::from(3))],
                c_row
            ); // 3*y + x
        }

        #[test]
        fn add_mult() {
            // 4 * b + 3 * a + 3 * c == (3 * a + 6 * b + 4 * c) * (31 * a + 4 * c)
            let lhs = Add(
                box Add(
                    box Mult(
                        box Number(FieldPrime::from(4)),
                        box Identifier(String::from("b")),
                    ),
                    box Mult(
                        box Number(FieldPrime::from(3)),
                        box Identifier(String::from("a")),
                    ),
                ),
                box Mult(
                    box Number(FieldPrime::from(3)),
                    box Identifier(String::from("c")),
                ),
            );
            let rhs = Mult(
                box Add(
                    box Add(
                        box Mult(
                            box Number(FieldPrime::from(3)),
                            box Identifier(String::from("a")),
                        ),
                        box Mult(
                            box Number(FieldPrime::from(6)),
                            box Identifier(String::from("b")),
                        ),
                    ),
                    box Mult(
                        box Number(FieldPrime::from(4)),
                        box Identifier(String::from("c")),
                    ),
                ),
                box Add(
                    box Mult(
                        box Number(FieldPrime::from(31)),
                        box Identifier(String::from("a")),
                    ),
                    box Mult(
                        box Number(FieldPrime::from(4)),
                        box Identifier(String::from("c")),
                    ),
                ),
            );
            let mut variables: Vec<String> = vec!["~one", "a", "b", "c"]
                .iter()
                .map(|&x| String::from(x))
                .collect();
            let mut a_row: Vec<(usize, FieldPrime)> = Vec::new();
            let mut b_row: Vec<(usize, FieldPrime)> = Vec::new();
            let mut c_row: Vec<(usize, FieldPrime)> = Vec::new();

            r1cs_expression(lhs, rhs, &mut variables, &mut a_row, &mut b_row, &mut c_row);
            a_row.sort_by(sort_tup);
            b_row.sort_by(sort_tup);
            c_row.sort_by(sort_tup);
            assert_eq!(
                vec![
                    (1, FieldPrime::from(3)),
                    (2, FieldPrime::from(6)),
                    (3, FieldPrime::from(4)),
                ],
                a_row
            );
            assert_eq!(
                vec![(1, FieldPrime::from(31)), (3, FieldPrime::from(4))],
                b_row
            );
            assert_eq!(
                vec![
                    (1, FieldPrime::from(3)),
                    (2, FieldPrime::from(4)),
                    (3, FieldPrime::from(3)),
                ],
                c_row
            );
        }

        #[test]
        fn div() {
            // x = (3 * x) / (y * 6) --> x * (y * 6) = 3 * x
            let lhs = Identifier(String::from("x"));
            let rhs = Div(
                box Mult(
                    box Number(FieldPrime::from(3)),
                    box Identifier(String::from("x")),
                ),
                box Mult(
                    box Identifier(String::from("y")),
                    box Number(FieldPrime::from(6)),
                ),
            );
            let mut variables: Vec<String> = vec!["~one", "x", "y"]
                .iter()
                .map(|&x| String::from(x))
                .collect();
            let mut a_row: Vec<(usize, FieldPrime)> = Vec::new();
            let mut b_row: Vec<(usize, FieldPrime)> = Vec::new();
            let mut c_row: Vec<(usize, FieldPrime)> = Vec::new();

            r1cs_expression(lhs, rhs, &mut variables, &mut a_row, &mut b_row, &mut c_row);
            a_row.sort_by(sort_tup);
            b_row.sort_by(sort_tup);
            c_row.sort_by(sort_tup);
            assert_eq!(vec![(1, FieldPrime::from(1))], a_row); // x
            assert_eq!(vec![(2, FieldPrime::from(6))], b_row); // y * 6
            assert_eq!(vec![(1, FieldPrime::from(3))], c_row); // 3 * x
        }
    }
}
