//! Module containing necessary functions to convert a flattened program or expression to r1cs.
//!
//! @file r1cs.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
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
                ref e @ NumberLiteral(_) |
                ref e @ VariableReference(_) |
                ref e @ Mult(..) |
                ref e @ Sub(..) if e.is_linear() => add.push(e),
                Add(ref l, ref r) => {
                    trace.push(l);
                    trace.push(r);
                },
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
            NumberLiteral(ref x) => {
                let num = count.entry("~one".to_string()).or_insert(T::zero());
                *num = num.clone() + x;
            },
            VariableReference(ref v) => {
                let num = count.entry(v.to_string()).or_insert(T::zero());
                *num = num.clone() + T::one();
            },
            Mult(box NumberLiteral(ref x1), box NumberLiteral(ref x2)) => {
                let num = count.entry("~one".to_string()).or_insert(T::zero());
                *num = num.clone() + x1 + x2;
            },
            Mult(box NumberLiteral(ref x), box VariableReference(ref v)) |
            Mult(box VariableReference(ref v), box NumberLiteral(ref x)) => {
                let num = count.entry(v.to_string()).or_insert(T::zero());
                *num = num.clone() + x;
            },
            ref e => panic!("Not covered: {}", e),
        }
    }
    count
}

/// Returns an equotation equivalent to `lhs == rhs` only using `Add` and `Mult`
///
/// # Arguments
///
/// * `lhs` - Leht hand side of the equotation
/// * `rhs` - Right hand side of the equotation
fn swap_sub<T: Field>(lhs: &Expression<T>, rhs: &Expression<T>) -> (Expression<T>, Expression<T>) {
    let mut left = get_summands(lhs);
    let mut right = get_summands(rhs);
    let mut run = true;
    while run {
        run = false;
        for i in 0..left.len() {
            match *left[i] {
                ref e @ NumberLiteral(_) |
                ref e @ VariableReference(_) |
                ref e @ Mult(..) if e.is_linear() => {},
                Sub(ref l, ref r) => {
                    run = true;
                    left.swap_remove(i);
                    left.extend(get_summands(l));
                    right.extend(get_summands(r));
                },
                ref e => panic!("Unexpected: {}", e),
            }
        }
        for i in 0..right.len() {
            match *right[i] {
                ref e @ NumberLiteral(_) |
                ref e @ VariableReference(_) |
                ref e @ Mult(..) if e.is_linear() => {},
                Sub(ref l, ref r) => {
                    run = true;
                    right.swap_remove(i);
                    right.extend(get_summands(l));
                    left.extend(get_summands(r));
                },
                ref e => panic!("Unexpected: {}", e),
            }
        }
    }
    if let Some(left_init) = left.pop() {
        if let Some(right_init) = right.pop() {
            return (
                left.iter().fold(left_init.clone(), |acc, &x| Add(box acc, box x.clone())),
                right.iter().fold(right_init.clone(), |acc, &x| Add(box acc, box x.clone()))
            );
        }
    }
    panic!("Unexpected");
}

/// Calculates one R1CS row representation for `linear_expr` = `expr`.
/// (<A,x>*<B,c> = <C,x>)
///
/// # Arguments
///
/// * `linear_expr` - Leht hand side of the equotation, has to be linear
/// * `expr` - Right hand side of the equotation
/// * `variables` - A mutual vector that contains all existing variables. Not found variables will be added.
/// * `a_row` - Result row of matrix A
/// * `b_row` - Result row of matrix B
/// * `c_row` - Result row of matrix C
fn r1cs_expression<T: Field>(linear_expr: Expression<T>, expr: Expression<T>, variables: &mut Vec<String>, a_row: &mut Vec<(usize, T)>, b_row: &mut Vec<(usize, T)>, c_row: &mut Vec<(usize, T)>) {
    assert!(linear_expr.is_linear());
    match expr {
        e @ Add(..) |
        e @ Sub(..) => {
            let (lhs, rhs) = swap_sub(&linear_expr, &e);
            for (key, value) in count_variables_add(&rhs) {
                a_row.push((get_variable_idx(variables, &key), value));
            }
            b_row.push((0, T::one()));
            for (key, value) in count_variables_add(&lhs) {
                c_row.push((get_variable_idx(variables, &key), value));
            }
        },
        Mult(lhs, rhs) => {
            match lhs {
                box NumberLiteral(x) => a_row.push((0, x)),
                box VariableReference(x) => a_row.push((get_variable_idx(variables, &x), T::one())),
                box e @ Add(..) => for (key, value) in count_variables_add(&e) {
                    a_row.push((get_variable_idx(variables, &key), value));
                },
                e @ _ => panic!("Not flattened: {}", e),
            };
            match rhs {
                box NumberLiteral(x) => b_row.push((0, x)),
                box VariableReference(x) => b_row.push((get_variable_idx(variables, &x), T::one())),
                box e @ Add(..) => for (key, value) in count_variables_add(&e) {
                    b_row.push((get_variable_idx(variables, &key), value));
                },
                e @ _ => panic!("Not flattened: {}", e),
            };
            for (key, value) in count_variables_add(&linear_expr) {
                c_row.push((get_variable_idx(variables, &key), value));
            }
        },
        Div(lhs, rhs) => { // a / b = c --> c * b = a
            match lhs {
                box NumberLiteral(x) => c_row.push((0, x)),
                box VariableReference(x) => c_row.push((get_variable_idx(variables, &x), T::one())),
                box e @ Add(..) => for (key, value) in count_variables_add(&e) {
                    c_row.push((get_variable_idx(variables, &key), value));
                },
                box e @ Sub(..) => return r1cs_expression(Mult(box linear_expr, rhs), e, variables, a_row, b_row, c_row),
                box Mult(box NumberLiteral(ref x1), box NumberLiteral(ref x2)) => c_row.push((0, x1.clone() * x2)),
                box Mult(box NumberLiteral(ref x), box VariableReference(ref v)) |
                box Mult(box VariableReference(ref v), box NumberLiteral(ref x)) => c_row.push((get_variable_idx(variables, v), x.clone())),
                e @ _ => panic!("(lhs) not supported: {:?}", e),
            };
            match rhs {
                box NumberLiteral(x) => b_row.push((0, x)),
                box VariableReference(x) => b_row.push((get_variable_idx(variables, &x), T::one())),
                box Mult(box NumberLiteral(ref x1), box NumberLiteral(ref x2)) => b_row.push((0, x1.clone() * x2)),
                box Mult(box NumberLiteral(ref x), box VariableReference(ref v)) |
                box Mult(box VariableReference(ref v), box NumberLiteral(ref x)) => b_row.push((get_variable_idx(variables, v), x.clone())),
                e @ _ => panic!("(rhs) not supported: {:?}", e),
            };
            for (key, value) in count_variables_add(&linear_expr) {
                a_row.push((get_variable_idx(variables, &key), value));
            }
        },
        Pow(_, _) => panic!("Pow not flattened"),
        IfElse(_, _, _) => panic!("IfElse not flattened"),
        VariableReference(var) => {
            a_row.push((get_variable_idx(variables, &var), T::one()));
            b_row.push((0, T::one()));
            for (key, value) in count_variables_add(&linear_expr) {
                c_row.push((get_variable_idx(variables, &key), value));
            }
        },
        NumberLiteral(x) => {
            a_row.push((0, x));
            b_row.push((0, T::one()));
            for (key, value) in count_variables_add(&linear_expr) {
                c_row.push((get_variable_idx(variables, &key), value));
            }
        },
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
/// * `<A,x>*<B,c> = <C,x>` for a witness `x`
///
/// # Arguments
///
/// * `prog` - The program the representation is calculated for.
pub fn r1cs_program<T: Field>(prog: &Prog<T>) -> (Vec<String>, Vec<Vec<(usize, T)>>, Vec<Vec<(usize, T)>>, Vec<Vec<(usize, T)>>){
    let mut variables: Vec<String> = Vec::new();
    variables.push("~one".to_string());
    let mut a: Vec<Vec<(usize, T)>> = Vec::new();
    let mut b: Vec<Vec<(usize, T)>> = Vec::new();
    let mut c: Vec<Vec<(usize, T)>> = Vec::new();
    variables.extend(prog.arguments.iter().map(|x| format!("{}", x)));
    for def in &prog.statements {
        let mut a_row: Vec<(usize, T)> = Vec::new();
        let mut b_row: Vec<(usize, T)> = Vec::new();
        let mut c_row: Vec<(usize, T)> = Vec::new();
        match *def {
            Statement::Return(ref expr) => r1cs_expression(VariableReference("~out".to_string()), expr.clone(), &mut variables, &mut a_row, &mut b_row, &mut c_row),
            Statement::Definition(ref id, ref expr) => r1cs_expression(VariableReference(id.to_string()), expr.clone(), &mut variables, &mut a_row, &mut b_row, &mut c_row),
            Statement::Condition(ref expr1, ref expr2) => r1cs_expression(expr1.clone(), expr2.clone(), &mut variables, &mut a_row, &mut b_row, &mut c_row),
            Statement::Compiler(..) => continue,
        }
        a.push(a_row);
        b.push(b_row);
        c.push(c_row);
    }
    (variables, a, b, c)
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
            let lhs = VariableReference(String::from("x"));
            let rhs = Add(box VariableReference(String::from("y")), box NumberLiteral(FieldPrime::from(5)));
            let mut variables: Vec<String> = vec!["~one", "x", "y"].iter().map(|&x| String::from(x)).collect();
            let mut a_row: Vec<(usize, FieldPrime)> = Vec::new();
            let mut b_row: Vec<(usize, FieldPrime)> = Vec::new();
            let mut c_row: Vec<(usize, FieldPrime)> = Vec::new();

            r1cs_expression(lhs, rhs, &mut variables, &mut a_row, &mut b_row, &mut c_row);
            a_row.sort_by(sort_tup);
            b_row.sort_by(sort_tup);
            c_row.sort_by(sort_tup);
            assert_eq!(vec![(0, FieldPrime::from(5)), (2, FieldPrime::from(1))], a_row);
            assert_eq!(vec![(0, FieldPrime::from(1))], b_row);
            assert_eq!(vec![(1, FieldPrime::from(1))], c_row);
        }

        #[test]
        fn add_sub_mix() {
            // (x + y) - ((z + 3*x) - y) == (x - y) + ((2*x - 4*y) + (4*y - 2*z))
            // --> (x + y) + y + 4y + 2z + y == x + 2x + 4y + (z + 3x)
            // <=> x + 7*y + 2*z == 6*x + 4y + z
            let lhs = Sub(
                box Add(box VariableReference(String::from("x")), box VariableReference(String::from("y"))),
                box Sub(
                    box Add(
                        box VariableReference(String::from("z")),
                        box Mult(box NumberLiteral(FieldPrime::from(3)), box VariableReference(String::from("x")))
                    ),
                    box VariableReference(String::from("y"))
                )
            );
            let rhs = Add(
                box Sub(box VariableReference(String::from("x")), box VariableReference(String::from("y"))),
                box Add(
                    box Sub(
                        box Mult(box NumberLiteral(FieldPrime::from(2)), box VariableReference(String::from("x"))),
                        box Mult(box NumberLiteral(FieldPrime::from(4)), box VariableReference(String::from("y")))
                    ),
                    box Sub(
                        box Mult(box NumberLiteral(FieldPrime::from(4)), box VariableReference(String::from("y"))),
                        box Mult(box NumberLiteral(FieldPrime::from(2)), box VariableReference(String::from("z")))
                    )
                )
            );
            let mut variables: Vec<String> = vec!["~one", "x", "y", "z"].iter().map(|&x| String::from(x)).collect();
            let mut a_row: Vec<(usize, FieldPrime)> = Vec::new();
            let mut b_row: Vec<(usize, FieldPrime)> = Vec::new();
            let mut c_row: Vec<(usize, FieldPrime)> = Vec::new();

            r1cs_expression(lhs, rhs, &mut variables, &mut a_row, &mut b_row, &mut c_row);
            a_row.sort_by(sort_tup);
            b_row.sort_by(sort_tup);
            c_row.sort_by(sort_tup);
            assert_eq!(vec![(1, FieldPrime::from(6)), (2, FieldPrime::from(4)), (3, FieldPrime::from(1))], a_row);
            assert_eq!(vec![(0, FieldPrime::from(1))], b_row);
            assert_eq!(vec![(1, FieldPrime::from(1)), (2, FieldPrime::from(7)), (3, FieldPrime::from(2))], c_row);
        }

        #[test]
        fn sub() {
            // 7 * x + y == 3 * y - z * 6
            let lhs = Add(
                box Mult(box NumberLiteral(FieldPrime::from(7)), box VariableReference(String::from("x"))),
                box VariableReference(String::from("y"))
            );
            let rhs = Sub(
                box Mult(box NumberLiteral(FieldPrime::from(3)), box VariableReference(String::from("y"))),
                box Mult(box VariableReference(String::from("z")), box NumberLiteral(FieldPrime::from(6)))
            );
            let mut variables: Vec<String> = vec!["~one", "x", "y", "z"].iter().map(|&x| String::from(x)).collect();
            let mut a_row: Vec<(usize, FieldPrime)> = Vec::new();
            let mut b_row: Vec<(usize, FieldPrime)> = Vec::new();
            let mut c_row: Vec<(usize, FieldPrime)> = Vec::new();

            r1cs_expression(lhs, rhs, &mut variables, &mut a_row, &mut b_row, &mut c_row);
            a_row.sort_by(sort_tup);
            b_row.sort_by(sort_tup);
            c_row.sort_by(sort_tup);
            assert_eq!(vec![(2, FieldPrime::from(3))], a_row); // 3 * y
            assert_eq!(vec![(0, FieldPrime::from(1))], b_row); // 1
            assert_eq!(vec![(1, FieldPrime::from(7)), (2, FieldPrime::from(1)), (3, FieldPrime::from(6))], c_row); // (7 * x + y) + z * 6
        }

        #[test]
        fn sub_multiple() {
            // (((3 * y) - (z * 2)) - (x * 12)) == (a - x)
            // --> 3*y + x == a + 12*x + 2*z
            let lhs = Sub(
                box Sub(
                    box Mult(box NumberLiteral(FieldPrime::from(3)), box VariableReference(String::from("y"))),
                    box Mult(box VariableReference(String::from("z")), box NumberLiteral(FieldPrime::from(2)))
                ),
                box Mult(box VariableReference(String::from("x")), box NumberLiteral(FieldPrime::from(12)))
            );
            let rhs = Sub(
                box VariableReference(String::from("a")),
                box VariableReference(String::from("x"))
            );
            let mut variables: Vec<String> = vec!["~one", "x", "y", "z", "a"].iter().map(|&x| String::from(x)).collect();
            let mut a_row: Vec<(usize, FieldPrime)> = Vec::new();
            let mut b_row: Vec<(usize, FieldPrime)> = Vec::new();
            let mut c_row: Vec<(usize, FieldPrime)> = Vec::new();

            r1cs_expression(lhs, rhs, &mut variables, &mut a_row, &mut b_row, &mut c_row);
            a_row.sort_by(sort_tup);
            b_row.sort_by(sort_tup);
            c_row.sort_by(sort_tup);
            assert_eq!(vec![(1, FieldPrime::from(12)), (3, FieldPrime::from(2)), (4, FieldPrime::from(1))], a_row); // a + 12*x + 2*z
            assert_eq!(vec![(0, FieldPrime::from(1))], b_row); // 1
            assert_eq!(vec![(1, FieldPrime::from(1)), (2, FieldPrime::from(3))], c_row); // 3*y + x
        }

        #[test]
        fn add_mult() {
            // 4 * b + 3 * a + 3 * c == (3 * a + 6 * b + 4 * c) * (31 * a + 4 * c)
            let lhs = Add(
                box Add(
                    box Mult(box NumberLiteral(FieldPrime::from(4)), box VariableReference(String::from("b"))),
                    box Mult(box NumberLiteral(FieldPrime::from(3)), box VariableReference(String::from("a")))
                ),
                box Mult(box NumberLiteral(FieldPrime::from(3)), box VariableReference(String::from("c")))
            );
            let rhs = Mult(
                box Add(
                    box Add(
                        box Mult(box NumberLiteral(FieldPrime::from(3)), box VariableReference(String::from("a"))),
                        box Mult(box NumberLiteral(FieldPrime::from(6)), box VariableReference(String::from("b")))
                    ),
                    box Mult(box NumberLiteral(FieldPrime::from(4)), box VariableReference(String::from("c")))
                ),
                box Add(
                    box Mult(box NumberLiteral(FieldPrime::from(31)), box VariableReference(String::from("a"))),
                    box Mult(box NumberLiteral(FieldPrime::from(4)), box VariableReference(String::from("c")))
                )
            );
            let mut variables: Vec<String> = vec!["~one", "a", "b", "c"].iter().map(|&x| String::from(x)).collect();
            let mut a_row: Vec<(usize, FieldPrime)> = Vec::new();
            let mut b_row: Vec<(usize, FieldPrime)> = Vec::new();
            let mut c_row: Vec<(usize, FieldPrime)> = Vec::new();

            r1cs_expression(lhs, rhs, &mut variables, &mut a_row, &mut b_row, &mut c_row);
            a_row.sort_by(sort_tup);
            b_row.sort_by(sort_tup);
            c_row.sort_by(sort_tup);
            assert_eq!(vec![(1, FieldPrime::from(3)), (2, FieldPrime::from(6)), (3, FieldPrime::from(4))], a_row);
            assert_eq!(vec![(1, FieldPrime::from(31)), (3, FieldPrime::from(4))], b_row);
            assert_eq!(vec![(1, FieldPrime::from(3)), (2, FieldPrime::from(4)), (3, FieldPrime::from(3))], c_row);
        }

        #[test]
        fn div() {
            // x = (3 * x) / (y * 6) --> x * (y * 6) = 3 * x
            let lhs = VariableReference(String::from("x"));
            let rhs = Div(
                box Mult(box NumberLiteral(FieldPrime::from(3)), box VariableReference(String::from("x"))),
                box Mult(box VariableReference(String::from("y")), box NumberLiteral(FieldPrime::from(6)))
            );
            let mut variables: Vec<String> = vec!["~one", "x", "y"].iter().map(|&x| String::from(x)).collect();
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

// old recursive implementations

// /// Returns a `HashMap` containing variables and the number of occurences
// ///
// /// # Arguments
// ///
// /// * `expr` - Expression only containing Numbers, Variables, Add and Mult
// ///
// /// # Example
// ///
// /// `7 * x + 4 * y + x` -> { x => 8, y = 4 }
// fn count_variables_add<T: Field>(expr: &Expression<T>) -> HashMap<String, T> {
//     let mut count = HashMap::new();
//     match expr.clone() {
//         NumberLiteral(x) => { count.insert("~one".to_string(), x); },
//         VariableReference(var) => { count.insert(var, T::one()); },
//         Mult(box NumberLiteral(x1), box NumberLiteral(x2)) => { count.insert("~one".to_string(), x1 * x2); },
//         Mult(box NumberLiteral(x), box VariableReference(var)) |
//         Mult(box VariableReference(var), box NumberLiteral(x)) => { count.insert(var, x); },
//         Add(box lhs, box rhs) => {
//             match (lhs, rhs) {
//                 (NumberLiteral(x), NumberLiteral(y)) => {
//                     let num = count.entry("~one".to_string()).or_insert(T::zero());
//                     *num = num.clone() + x + y;
//                 },
//                 (VariableReference(v), NumberLiteral(x)) |
//                 (NumberLiteral(x), VariableReference(v)) => {
//                     {
//                         let num = count.entry("~one".to_string()).or_insert(T::zero());
//                         *num = num.clone() + x;
//                     }
//                     let var = count.entry(v).or_insert(T::zero());
//                     *var = var.clone() + T::one();
//                 },
//                 (VariableReference(v1), VariableReference(v2)) => {
//                     {
//                         let var1 = count.entry(v1).or_insert(T::zero());
//                         *var1 = var1.clone() + T::one();
//                     }
//                     let var2 = count.entry(v2).or_insert(T::zero());
//                     *var2 = var2.clone() + T::one();
//                 },
//                 (NumberLiteral(x), e @ Add(..)) |
//                 (e @ Add(..), NumberLiteral(x)) => {
//                     {
//                         let num = count.entry("~one".to_string()).or_insert(T::zero());
//                         *num = num.clone() + x;
//                     }
//                     let vars = count_variables_add(&e);
//                     for (key, value) in &vars {
//                         let val = count.entry(key.to_string()).or_insert(T::zero());
//                         *val = val.clone() + value;
//                     }
//                 },
//                 (VariableReference(v), e @ Add(..)) |
//                 (e @ Add(..), VariableReference(v)) => {
//                     {
//                         let var = count.entry(v).or_insert(T::zero());
//                         *var = var.clone() + T::one();
//                     }
//                     let vars = count_variables_add(&e);
//                     for (key, value) in &vars {
//                         let val = count.entry(key.to_string()).or_insert(T::zero());
//                         *val = val.clone() + value;
//                     }
//                 },
//                 (NumberLiteral(x), Mult(box NumberLiteral(n), box VariableReference(v))) |
//                 (NumberLiteral(x), Mult(box VariableReference(v), box NumberLiteral(n))) |
//                 (Mult(box NumberLiteral(n), box VariableReference(v)), NumberLiteral(x)) |
//                 (Mult(box VariableReference(v), box NumberLiteral(n)), NumberLiteral(x)) => {
//                     {
//                         let num = count.entry("~one".to_string()).or_insert(T::zero());
//                         *num = num.clone() + x;
//                     }
//                     let var = count.entry(v).or_insert(T::zero());
//                     *var = var.clone() + n;
//                 },
//                 (VariableReference(v1), Mult(box NumberLiteral(n), box VariableReference(v2))) |
//                 (VariableReference(v1), Mult(box VariableReference(v2), box NumberLiteral(n))) |
//                 (Mult(box NumberLiteral(n), box VariableReference(v2)), VariableReference(v1)) |
//                 (Mult(box VariableReference(v2), box NumberLiteral(n)), VariableReference(v1)) => {
//                     {
//                         let var = count.entry(v1).or_insert(T::zero());
//                         *var = var.clone() + T::one();
//                     }
//                     let var = count.entry(v2).or_insert(T::zero());
//                     *var = var.clone() + n;
//                 },
//                 (e @ Add(..), Mult(box NumberLiteral(n), box VariableReference(v))) |
//                 (e @ Add(..), Mult(box VariableReference(v), box NumberLiteral(n))) |
//                 (Mult(box NumberLiteral(n), box VariableReference(v)), e @ Add(..)) |
//                 (Mult(box VariableReference(v), box NumberLiteral(n)), e @ Add(..)) => {
//                     {
//                         let var = count.entry(v).or_insert(T::zero());
//                         *var = var.clone() + n;
//                     }
//                     let vars = count_variables_add(&e);
//                     for (key, value) in &vars {
//                         let val = count.entry(key.to_string()).or_insert(T::zero());
//                         *val = val.clone() + value;
//                     }
//                 },
//                 (Mult(box NumberLiteral(n1), box VariableReference(v1)), Mult(box NumberLiteral(n2), box VariableReference(v2))) |
//                 (Mult(box VariableReference(v1), box NumberLiteral(n1)), Mult(box NumberLiteral(n2), box VariableReference(v2))) |
//                 (Mult(box NumberLiteral(n1), box VariableReference(v1)), Mult(box VariableReference(v2), box NumberLiteral(n2))) |
//                 (Mult(box VariableReference(v1), box NumberLiteral(n1)), Mult(box VariableReference(v2), box NumberLiteral(n2))) => {
//                     {
//                         let var = count.entry(v1).or_insert(T::zero());
//                         *var = var.clone() + n1;
//                     }
//                     let var = count.entry(v2).or_insert(T::zero());
//                     *var = var.clone() + n2;
//                 },
//                 (e1 @ Add(..), e2 @ Add(..)) => {
//                     {
//                         let vars = count_variables_add(&e1);
//                         for (key, value) in &vars {
//                             let val = count.entry(key.to_string()).or_insert(T::zero());
//                             *val = val.clone() + value;
//                         }
//                     }
//                     let vars = count_variables_add(&e2);
//                     for (key, value) in &vars {
//                         let val = count.entry(key.to_string()).or_insert(T::zero());
//                         *val = val.clone() + value;
//                     }
//                 }
//                 e @ _ => panic!("Error: unexpected Add({}, {})", e.0, e.1),
//             }
//         },
//         e @ _ => panic!("Statement::Add/Mult[linear] expected, got: {}", e),
//     }
//     count
// }

// /// Returns an equotation equivalent to `lhs == rhs` only using `Add` and `Mult`
// ///
// /// # Arguments
// ///
// /// * `lhs` - Leht hand side of the equotation
// /// * `rhs` - Right hand side of the equotation
// fn swap_sub_recursive<T: Field>(lhs: &Expression<T>, rhs: &Expression<T>) -> (Expression<T>, Expression<T>) {
//     // assert that Mult on lhs or rhs is linear!
//     match (lhs.clone(), rhs.clone()) {
//         // recursion end
//         (v1 @ NumberLiteral(_), v2 @ NumberLiteral(_)) |
//         (v1 @ VariableReference(_), v2 @ NumberLiteral(_)) |
//         (v1 @ NumberLiteral(_), v2 @ VariableReference(_)) |
//         (v1 @ VariableReference(_), v2 @ VariableReference(_)) |
//         (v1 @ VariableReference(_), v2 @ Mult(..)) |
//         (v1 @ Mult(..), v2 @ VariableReference(_)) |
//         (v1 @ NumberLiteral(_), v2 @ Mult(..)) |
//         (v1 @ Mult(..), v2 @ NumberLiteral(_)) |
//         (v1 @ Mult(..), v2 @ Mult(..)) => {
//             assert!(v1.is_linear());
//             assert!(v2.is_linear());
//             (v1, v2)
//         },
//         // Num/Var/Mult = Add
//         (v @ NumberLiteral(_), Add(left, right)) |
//         (v @ VariableReference(_), Add(left, right)) |
//         (v @ Mult(..), Add(left, right)) => {
//             assert!(v.is_linear());
//             let (l1, r1) = swap_sub(&v, &left);
//             let (l2, r2) = swap_sub(&l1, &right);
//             (l2, Add(box r1, box r2))
//         },
//         // Add = Num/Var/Mult
//         (Add(left, right), v @ NumberLiteral(_)) |
//         (Add(left, right), v @ VariableReference(_)) |
//         (Add(left, right), v @ Mult(..)) => { // v = left + right
//             assert!(v.is_linear());
//             let (l1, r1) = swap_sub(&left, &v);
//             let (l2, r2) = swap_sub(&right, &r1);
//             (Add(box l1, box l2), r2)
//         },
//         // Sub = Var/Num/Mult
//         (Sub(box left, box right), v @ VariableReference(_)) |
//         (Sub(box left, box right), v @ NumberLiteral(_)) |
//         (Sub(box left, box right), v @ Mult(..)) => {
//             assert!(v.is_linear());
//             let (l, r) = swap_sub(&left, &right);
//             (l, Add(box v, box r))
//         },
//         // Var/Num/Mult = Sub
//         (v @ VariableReference(_), Sub(box left, box right)) |
//         (v @ NumberLiteral(_), Sub(box left, box right)) |
//         (v @ Mult(..), Sub(box left, box right)) => {
//             assert!(v.is_linear());
//             let (l, r) = swap_sub(&left, &right);
//             (Add(box v, box r), l)
//         },
//         // Add = Add
//         (Add(box left1, box right1), Add(box left2, box right2)) => {
//             let (l1, r1) = swap_sub(&left1, &left2);
//             let (l2, r2) = swap_sub(&right1, &right2);
//             (Add(box l1, box l2), Add(box r1, box r2))
//         },
//         // Sub = Add
//         (Sub(box left_s, box right_s), Add(box left_a, box right_a)) => {
//             let (l1, r1) = swap_sub(&left_s, &right_s);
//             let (l2, r2) = swap_sub(&l1, &left_a);
//             let (l3, r3) = swap_sub(&l2, &right_a);
//             (l3, Add(box r1, box Add(box r2, box r3)))
//         },
//         // Add = Sub
//         (Add(box left_a, box right_a), Sub(box left_s, box right_s)) => {
//             let (l1, r1) = swap_sub(&left_s, &right_s);
//             let (l2, r2) = swap_sub(&l1, &left_a);
//             let (l3, r3) = swap_sub(&l2, &right_a);
//             (Add(box r1, box Add(box r2, box r3)), l3)
//         },
//         // Sub = Sub
//         (Sub(box l1, box r1), Sub(l2, r2)) => {
//             let (lhs1, rhs1) = swap_sub(&l1, &r1);
//             let (lhs2, rhs2) = swap_sub(&l2, &r2);
//             (Add(box lhs1, box rhs2), Add(box lhs2, box rhs1))
//         },
//         e @ _ => panic!("Input not covered: {} = {}", e.0, e.1),
//     }
// }
