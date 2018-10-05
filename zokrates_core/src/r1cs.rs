//! Module containing necessary functions to convert a flattened program or expression to r1cs.
//!
//! @file r1cs.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de
//! @date 2017

use flat_absy::flat_variable::FlatVariable;
use std::collections::HashMap;
use std::mem;
use flat_absy::*;
use flat_absy::FlatExpression::*;
use field::Field;

/// Returns a vector of summands of the given `FlatExpression`.
///
/// # Arguments
///
/// * `expr` - `FlatExpression` to be split to summands.
///
/// # Example
///
/// a + 2*b + (c - d) -> [a, 2*b, c-d]
fn get_summands<T: Field>(expr: &FlatExpression<T>) -> Vec<&FlatExpression<T>> {
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

/// Returns a `HashMap` containing variables and the number of occurrences
///
/// # Arguments
///
/// * `expr` - FlatExpression only containing Numbers, Variables, Add and Mult
///
/// # Example
///
/// `7 * x + 4 * y + x` -> { x => 8, y = 4 }
fn count_variables_add<T: Field>(expr: &FlatExpression<T>) -> HashMap<FlatVariable, T> {
    let summands = get_summands(expr);
    let mut count = HashMap::new();
    for s in summands {
        match *s {
            Number(ref x) => {
                let num = count.entry(FlatVariable::one()).or_insert(T::zero());
                *num = num.clone() + x;
            }
            Identifier(ref v) => {
                let num = count.entry(*v).or_insert(T::zero());
                *num = num.clone() + T::one();
            }
            Mult(box Number(ref x1), box Number(ref x2)) => {
                let num = count.entry(FlatVariable::one()).or_insert(T::zero());
                *num = num.clone() + x1 + x2;
            }
            Mult(box Number(ref x), box Identifier(ref v)) |
            Mult(box Identifier(ref v), box Number(ref x)) => {
                let num = count.entry(*v).or_insert(T::zero());
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
/// * `lhs` - Left hand side of the equation
/// * `rhs` - Right hand side of the equation
fn swap_sub<T: Field>(lhs: &FlatExpression<T>, rhs: &FlatExpression<T>) -> (FlatExpression<T>, FlatExpression<T>) {
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
/// (<C,x> = <a,x>*<B,x>)
///
/// # Arguments
///
/// * `linear_expr` - Left hand side of the equation, has to be linear
/// * `expr` - Right hand side of the equation
/// * `variables` - a mutual vector that contains all existing variables. Not found variables will be added.
/// * `a_row` - Result row of matrix a
/// * `b_row` - Result row of matrix B
/// * `c_row` - Result row of matrix C
fn r1cs_expression<T: Field>(
    linear_expr: FlatExpression<T>,
    expr: FlatExpression<T>,
    variables: &mut HashMap<FlatVariable, usize>,
    a_row: &mut Vec<(usize, T)>,
    b_row: &mut Vec<(usize, T)>,
    c_row: &mut Vec<(usize, T)>,
) {
    assert!(linear_expr.is_linear());

    match expr {
        e @ Add(..) | e @ Sub(..) => {
            let (lhs, rhs) = swap_sub(&linear_expr, &e);
            for (key, value) in count_variables_add(&rhs) {
                a_row.push((provide_variable_idx(variables, &key), value));
            }
            b_row.push((0, T::one()));
            for (key, value) in count_variables_add(&lhs) {
                c_row.push((provide_variable_idx(variables, &key), value));
            }
        }
        Mult(lhs, rhs) => {
            match lhs {
                box Number(x) => a_row.push((0, x)),
                box Identifier(x) => a_row.push((provide_variable_idx(variables, &x), T::one())),
                box e @ Add(..) => for (key, value) in count_variables_add(&e) {
                    a_row.push((provide_variable_idx(variables, &key), value));
                },
                e @ _ => panic!("Not flattened: {}", e),
            };
            match rhs {
                box Number(x) => b_row.push((0, x)),
                box Identifier(x) => b_row.push((provide_variable_idx(variables, &x), T::one())),
                box e @ Add(..) => for (key, value) in count_variables_add(&e) {
                    b_row.push((provide_variable_idx(variables, &key), value));
                },
                e @ _ => panic!("Not flattened: {}", e),
            };
            for (key, value) in count_variables_add(&linear_expr) {
                c_row.push((provide_variable_idx(variables, &key), value));
            }
        }
        Div(lhs, rhs) => {
            // a / b = c --> c * b = a
            match lhs {
                box Number(x) => c_row.push((0, x)),
                box Identifier(x) => c_row.push((provide_variable_idx(variables, &x), T::one())),
                box e @ Add(..) => for (key, value) in count_variables_add(&e) {
                    c_row.push((provide_variable_idx(variables, &key), value));
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
                    c_row.push((provide_variable_idx(variables, v), x.clone()))
                }
                e @ _ => panic!("(lhs) not supported: {:?}", e),
            };
            match rhs {
                box Number(x) => b_row.push((0, x)),
                box Identifier(x) => b_row.push((provide_variable_idx(variables, &x), T::one())),
                box Mult(box Number(ref x1), box Number(ref x2)) => {
                    b_row.push((0, x1.clone() * x2))
                }
                box Mult(box Number(ref x), box Identifier(ref v)) |
                box Mult(box Identifier(ref v), box Number(ref x)) => {
                    b_row.push((provide_variable_idx(variables, v), x.clone()))
                }
                e @ _ => panic!("(rhs) not supported: {:?}", e),
            };
            for (key, value) in count_variables_add(&linear_expr) {
                a_row.push((provide_variable_idx(variables, &key), value));
            }
        }
        Identifier(var) => {
            a_row.push((provide_variable_idx(variables, &var), T::one()));
            b_row.push((0, T::one()));
            for (key, value) in count_variables_add(&linear_expr) {
                c_row.push((provide_variable_idx(variables, &key), value));
            }
        }
        Number(x) => {
            a_row.push((0, x));
            b_row.push((0, T::one()));
            for (key, value) in count_variables_add(&linear_expr) {
                c_row.push((provide_variable_idx(variables, &key), value));
            }
        }
    }
}

/// Returns the index of `var` in `variables`, adding `var` with incremented index if it not yet exists.
///
/// # Arguments
///
/// * `variables` - A mutual map that maps all existing variables to their index.
/// * `var` - Variable to be searched for.
fn provide_variable_idx(variables: &mut HashMap<FlatVariable, usize>, var: &FlatVariable) -> usize {
    let index = variables.len();
    *variables.entry(*var).or_insert(index)
}

/// Calculates one R1CS row representation of a program and returns (V, A, B, C) so that:
/// * `V` contains all used variables and the index in the vector represents the used number in `A`, `B`, `C`
/// * `<A,x>*<B,x> = <C,x>` for a witness `x`
///
/// # Arguments
///
/// * `prog` - The program the representation is calculated for.
pub fn r1cs_program<T: Field>(
    prog: &FlatProg<T>,
) -> (
    Vec<FlatVariable>,
    usize,
    Vec<Vec<(usize, T)>>,
    Vec<Vec<(usize, T)>>,
    Vec<Vec<(usize, T)>>,
) {
    let mut variables: HashMap<FlatVariable, usize> = HashMap::new();
    provide_variable_idx(&mut variables, &FlatVariable::one());
    let mut a: Vec<Vec<(usize, T)>> = Vec::new();
    let mut b: Vec<Vec<(usize, T)>> = Vec::new();
    let mut c: Vec<Vec<(usize, T)>> = Vec::new();

    //Only the main function is relevant in this step, since all calls to other functions were resolved during flattening
    let main = prog.functions
        .iter()
        .find(|x: &&FlatFunction<T>| x.id == "main".to_string())
        .unwrap();

    for x in main.arguments.iter().filter(|x| !x.private) {
        provide_variable_idx(&mut variables, &x.id);
    }

    // ~out is added after main's arguments as we want variables (columns)
    // in the r1cs to be aligned like "public inputs | private inputs"
    let main_return_count = main.signature.outputs.iter().map(|t| t.get_primitive_count()).fold(0, |acc, x| acc + x);

    for i in 0..main_return_count {
        provide_variable_idx(&mut variables, &FlatVariable::public(i));
    }

    // position where private part of witness starts
    let private_inputs_offset = variables.len();

    for def in &main.statements {
        match *def {
            FlatStatement::Return(ref list) => {
                for (i, val) in list.expressions.iter().enumerate() {
                    let mut a_row = Vec::new();
                    let mut b_row = Vec::new();
                    let mut c_row = Vec::new();
                    r1cs_expression(
                        Identifier(FlatVariable::public(i)),
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
            FlatStatement::Definition(ref id, ref rhs) => {
                let mut a_row = Vec::new();
                let mut b_row = Vec::new();
                let mut c_row = Vec::new();
                r1cs_expression(
                    FlatExpression::Identifier(*id),
                    rhs.clone(),
                    &mut variables,
                    &mut a_row,
                    &mut b_row,
                    &mut c_row,
                );
                a.push(a_row);
                b.push(b_row);
                c.push(c_row);
            },
            FlatStatement::Condition(ref expr1, ref expr2) => {
                let mut a_row = Vec::new();
                let mut b_row = Vec::new();
                let mut c_row = Vec::new();
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
            FlatStatement::Directive(..) => continue
        }
    }

    // Convert map back into list ordered by index
    let mut variables_list = vec![FlatVariable::new(0); variables.len()];
    for (k, v) in variables.drain() {
        assert_eq!(variables_list[v], FlatVariable::new(0));
        mem::replace(&mut variables_list[v], k);
    }
    (variables_list, private_inputs_offset, a, b, c)
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

            let one = FlatVariable::one();
            let x = FlatVariable::new(0);
            let y = FlatVariable::new(1);

            let lhs = Identifier(x);
            let rhs = Add(
                box Identifier(y),
                box Number(FieldPrime::from(5)),
            );

            let mut variables: HashMap<FlatVariable, usize> = HashMap::new();
            variables.insert(one, 0);
            variables.insert(x, 1);
            variables.insert(y, 2);
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

            let one = FlatVariable::one();
            let x = FlatVariable::new(0);
            let y = FlatVariable::new(1);
            let z = FlatVariable::new(2);

            let lhs = Sub(
                box Add(
                    box Identifier(x),
                    box Identifier(y),
                ),
                box Sub(
                    box Add(
                        box Identifier(z),
                        box Mult(
                            box Number(FieldPrime::from(3)),
                            box Identifier(x),
                        ),
                    ),
                    box Identifier(y),
                ),
            );
            let rhs = Add(
                box Sub(
                    box Identifier(x),
                    box Identifier(y),
                ),
                box Add(
                    box Sub(
                        box Mult(
                            box Number(FieldPrime::from(2)),
                            box Identifier(x),
                        ),
                        box Mult(
                            box Number(FieldPrime::from(4)),
                            box Identifier(y),
                        ),
                    ),
                    box Sub(
                        box Mult(
                            box Number(FieldPrime::from(4)),
                            box Identifier(y),
                        ),
                        box Mult(
                            box Number(FieldPrime::from(2)),
                            box Identifier(z),
                        ),
                    ),
                ),
            );

            let mut variables: HashMap<FlatVariable, usize> = HashMap::new();
            variables.insert(one, 0);
            variables.insert(x, 1);
            variables.insert(y, 2);
            variables.insert(z, 3);

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

            let one = FlatVariable::one();
            let x = FlatVariable::new(0);
            let y = FlatVariable::new(1);
            let z = FlatVariable::new(2);

            let lhs = Add(
                box Mult(
                    box Number(FieldPrime::from(7)),
                    box Identifier(x),
                ),
                box Identifier(y),
            );
            let rhs = Sub(
                box Mult(
                    box Number(FieldPrime::from(3)),
                    box Identifier(y),
                ),
                box Mult(
                    box Identifier(z),
                    box Number(FieldPrime::from(6)),
                ),
            );

            let mut variables: HashMap<FlatVariable, usize> = HashMap::new();
            variables.insert(one, 0);
            variables.insert(x, 1);
            variables.insert(y, 2);
            variables.insert(z, 3);

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

            let one = FlatVariable::one();
            let x = FlatVariable::new(0);
            let y = FlatVariable::new(1);
            let z = FlatVariable::new(2);
            let a = FlatVariable::new(3);

            let lhs = Sub(
                box Sub(
                    box Mult(
                        box Number(FieldPrime::from(3)),
                        box Identifier(y),
                    ),
                    box Mult(
                        box Identifier(z),
                        box Number(FieldPrime::from(2)),
                    ),
                ),
                box Mult(
                    box Identifier(x),
                    box Number(FieldPrime::from(12)),
                ),
            );
            let rhs = Sub(
                box Identifier(a),
                box Identifier(x),
            );

            let mut variables: HashMap<FlatVariable, usize> = HashMap::new();
            variables.insert(one, 0);
            variables.insert(x, 1);
            variables.insert(y, 2);
            variables.insert(z, 3);
            variables.insert(a, 4);

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
            // 4 * y + 3 * x + 3 * z == (3 * x + 6 * y + 4 * z) * (31 * x + 4 * z)

            let one = FlatVariable::one();
            let x = FlatVariable::new(0);
            let y = FlatVariable::new(1);
            let z = FlatVariable::new(2);

            let lhs = Add(
                box Add(
                    box Mult(
                        box Number(FieldPrime::from(4)),
                        box Identifier(y),
                    ),
                    box Mult(
                        box Number(FieldPrime::from(3)),
                        box Identifier(x),
                    ),
                ),
                box Mult(
                    box Number(FieldPrime::from(3)),
                    box Identifier(z),
                ),
            );
            let rhs = Mult(
                box Add(
                    box Add(
                        box Mult(
                            box Number(FieldPrime::from(3)),
                            box Identifier(x),
                        ),
                        box Mult(
                            box Number(FieldPrime::from(6)),
                            box Identifier(y),
                        ),
                    ),
                    box Mult(
                        box Number(FieldPrime::from(4)),
                        box Identifier(z),
                    ),
                ),
                box Add(
                    box Mult(
                        box Number(FieldPrime::from(31)),
                        box Identifier(x),
                    ),
                    box Mult(
                        box Number(FieldPrime::from(4)),
                        box Identifier(z),
                    ),
                ),
            );

            let mut variables: HashMap<FlatVariable, usize> = HashMap::new();
            variables.insert(one, 0);
            variables.insert(x, 1);
            variables.insert(y, 2);
            variables.insert(z, 3);

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

            let one = FlatVariable::one();
            let x = FlatVariable::new(0);
            let y = FlatVariable::new(1);

            let lhs = Identifier(x);
            let rhs = Div(
                box Mult(
                    box Number(FieldPrime::from(3)),
                    box Identifier(x),
                ),
                box Mult(
                    box Identifier(y),
                    box Number(FieldPrime::from(6)),
                ),
            );

            let mut a_row = Vec::new();
            let mut b_row = Vec::new();
            let mut c_row = Vec::new();

            let mut variables: HashMap<FlatVariable, usize> = HashMap::new();
            variables.insert(one, 0);
            variables.insert(x, 1);
            variables.insert(y, 2);

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
