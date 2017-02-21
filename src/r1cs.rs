//
// @file r1cs.rs
// @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
// @date 2017

use absy::*;
use absy::Expression::*;
use std::collections::HashMap;
use field::Field;

fn count_variables_add<T: Field>(expr: &Expression<T>) -> HashMap<String, T> {
    let mut count = HashMap::new();
    match expr.clone() {
        NumberLiteral(x) => { count.insert("~one".to_string(), x); },
        VariableReference(var) => { count.insert(var, T::one()); },
        Mult(box NumberLiteral(x1), box NumberLiteral(x2)) => { count.insert("~one".to_string(), x1 * x2); },
        Mult(box NumberLiteral(x), box VariableReference(var)) |
        Mult(box VariableReference(var), box NumberLiteral(x)) => { count.insert(var, x); },
        Add(box lhs, box rhs) => {
            match (lhs, rhs) {
                (NumberLiteral(x), NumberLiteral(y)) => {
                    let num = count.entry("~one".to_string()).or_insert(T::zero());
                    *num = num.clone() + x + y;
                },
                (VariableReference(v), NumberLiteral(x)) |
                (NumberLiteral(x), VariableReference(v)) => {
                    {
                        let num = count.entry("~one".to_string()).or_insert(T::zero());
                        *num = num.clone() + x;
                    }
                    let var = count.entry(v).or_insert(T::zero());
                    *var = var.clone() + T::one();
                },
                (VariableReference(v1), VariableReference(v2)) => {
                    {
                        let var1 = count.entry(v1).or_insert(T::zero());
                        *var1 = var1.clone() + T::one();
                    }
                    let var2 = count.entry(v2).or_insert(T::zero());
                    *var2 = var2.clone() + T::one();
                },
                (NumberLiteral(x), e @ Add(..)) |
                (e @ Add(..), NumberLiteral(x)) => {
                    {
                        let num = count.entry("~one".to_string()).or_insert(T::zero());
                        *num = num.clone() + x;
                    }
                    let vars = count_variables_add(&e);
                    for (key, value) in &vars {
                        let val = count.entry(key.to_string()).or_insert(T::zero());
                        *val = val.clone() + value;
                    }
                },
                (VariableReference(v), e @ Add(..)) |
                (e @ Add(..), VariableReference(v)) => {
                    {
                        let var = count.entry(v).or_insert(T::zero());
                        *var = var.clone() + T::one();
                    }
                    let vars = count_variables_add(&e);
                    for (key, value) in &vars {
                        let val = count.entry(key.to_string()).or_insert(T::zero());
                        *val = val.clone() + value;
                    }
                },
                (NumberLiteral(x), Mult(box NumberLiteral(n), box VariableReference(v))) |
                (NumberLiteral(x), Mult(box VariableReference(v), box NumberLiteral(n))) |
                (Mult(box NumberLiteral(n), box VariableReference(v)), NumberLiteral(x)) |
                (Mult(box VariableReference(v), box NumberLiteral(n)), NumberLiteral(x)) => {
                    {
                        let num = count.entry("~one".to_string()).or_insert(T::zero());
                        *num = num.clone() + x;
                    }
                    let var = count.entry(v).or_insert(T::zero());
                    *var = var.clone() + n;
                },
                (VariableReference(v1), Mult(box NumberLiteral(n), box VariableReference(v2))) |
                (VariableReference(v1), Mult(box VariableReference(v2), box NumberLiteral(n))) |
                (Mult(box NumberLiteral(n), box VariableReference(v2)), VariableReference(v1)) |
                (Mult(box VariableReference(v2), box NumberLiteral(n)), VariableReference(v1)) => {
                    {
                        let var = count.entry(v1).or_insert(T::zero());
                        *var = var.clone() + T::one();
                    }
                    let var = count.entry(v2).or_insert(T::zero());
                    *var = var.clone() + n;
                },
                (e @ Add(..), Mult(box NumberLiteral(n), box VariableReference(v))) |
                (e @ Add(..), Mult(box VariableReference(v), box NumberLiteral(n))) |
                (Mult(box NumberLiteral(n), box VariableReference(v)), e @ Add(..)) |
                (Mult(box VariableReference(v), box NumberLiteral(n)), e @ Add(..)) => {
                    {
                        let var = count.entry(v).or_insert(T::zero());
                        *var = var.clone() + n;
                    }
                    let vars = count_variables_add(&e);
                    for (key, value) in &vars {
                        let val = count.entry(key.to_string()).or_insert(T::zero());
                        *val = val.clone() + value;
                    }
                },
                (Mult(box NumberLiteral(n1), box VariableReference(v1)), Mult(box NumberLiteral(n2), box VariableReference(v2))) |
                (Mult(box VariableReference(v1), box NumberLiteral(n1)), Mult(box NumberLiteral(n2), box VariableReference(v2))) |
                (Mult(box NumberLiteral(n1), box VariableReference(v1)), Mult(box VariableReference(v2), box NumberLiteral(n2))) |
                (Mult(box VariableReference(v1), box NumberLiteral(n1)), Mult(box VariableReference(v2), box NumberLiteral(n2))) => {
                    {
                        let var = count.entry(v1).or_insert(T::zero());
                        *var = var.clone() + n1;
                    }
                    let var = count.entry(v2).or_insert(T::zero());
                    *var = var.clone() + n2;
                },
                e @ _ => panic!("Error: Add({}, {})", e.0, e.1),
            }
        },
        e @ _ => panic!("Statement::Add/Mult[linear] expected, got: {}", e),
    }
    count
}

// lhs = rhy
fn swap_sub<T: Field>(lhs: &Expression<T>, rhs: &Expression<T>) -> (Expression<T>, Expression<T>) {
    // assert that Mult on lhs or rhs is linear!
    match (lhs.clone(), rhs.clone()) {
        // recursion end
        (v1 @ NumberLiteral(_), v2 @ NumberLiteral(_)) |
        (v1 @ VariableReference(_), v2 @ NumberLiteral(_)) |
        (v1 @ NumberLiteral(_), v2 @ VariableReference(_)) |
        (v1 @ VariableReference(_), v2 @ VariableReference(_)) |
        (v1 @ VariableReference(_), v2 @ Mult(..)) |
        (v1 @ Mult(..), v2 @ VariableReference(_)) |
        (v1 @ NumberLiteral(_), v2 @ Mult(..)) |
        (v1 @ Mult(..), v2 @ NumberLiteral(_)) |
        (v1 @ Mult(..), v2 @ Mult(..)) => {
            assert!(v1.is_linear());
            assert!(v2.is_linear());
            (v1, v2)
        },
        // Add
        (Add(left, right), var @ NumberLiteral(_)) |
        (var @ NumberLiteral(_), Add(left, right)) |
        (Add(left, right), var @ VariableReference(_)) |
        (var @ VariableReference(_), Add(left, right)) |
        (var @ Mult(..), Add(left, right)) |
        (Add(left, right), var @ Mult(..)) => { // var = left + right
            let (l1, r1) = swap_sub(&var, &right);
            let (l2, r2) = swap_sub(&l1, &left);
            (l2, Add(box r2, box r1))
        },
        // Sub = Var/Num/Add/Mult
        (Sub(box left, box right), v @ VariableReference(_)) |
        (Sub(box left, box right), v @ NumberLiteral(_)) |
        (Sub(box left, box right), v @ Add(..)) |
        (Sub(box left, box right), v @ Mult(..)) => {
            assert!(v.is_linear());
            let (l, r) = swap_sub(&left, &right);
            (l, Add(box v, box r))
        },
        // Var/Num/Add/Mult = Sub
        (v @ VariableReference(_), Sub(box left, box right)) |
        (v @ NumberLiteral(_), Sub(box left, box right)) |
        (v @ Add(..), Sub(box left, box right)) |
        (v @ Mult(..), Sub(box left, box right)) => {
            assert!(v.is_linear());
            let (l, r) = swap_sub(&left, &right);
            (Add(box v, box r), l)
        },
        // Sub = Sub
        (Sub(box l1, box r1), Sub(l2, r2)) => {
            println!("1: {} - {}", l1, r1);
            println!("2: {} - {}", l2, r2);
            let (lhs1, rhs1) = swap_sub(&l1, &r1);
            println!("11: {} = {}", lhs1, rhs1);
            let (lhs2, rhs2) = swap_sub(&l2, &r2);
            println!("12: {} = {}", lhs2, rhs2);
            (Add(box lhs1, box rhs2), Add(box lhs2, box rhs1))
        },
        e @ _ => panic!("Input not covered: {} = {}", e.0, e.1),
    }
}

pub fn r1cs_expression<T: Field>(linear_expr: Expression<T>, expr: Expression<T>, variables: &mut Vec<String>, a_row: &mut Vec<(usize, T)>, b_row: &mut Vec<(usize, T)>, c_row: &mut Vec<(usize, T)>) {
    assert!(linear_expr.is_linear());
    match expr {
        e @ Add(..) |
        e @ Sub(..) => { // a - b = c --> b + c = a
            let (lhs, rhs) = swap_sub(&linear_expr, &e);
            for (key, value) in count_variables_add(&rhs) {
                a_row.push((variables.iter().position(|r| r == &key).unwrap(), value));
            }
            b_row.push((0, T::one()));
            for (key, value) in count_variables_add(&lhs) {
                c_row.push((variables.iter().position(|r| r == &key).unwrap(), value));
            }
        },
        Mult(lhs, rhs) => {
            match lhs {
                box NumberLiteral(x) => a_row.push((0, x)),
                box VariableReference(x) => a_row.push((variables.iter().position(|r| r == &x).unwrap(), T::one())),
                box e @ Add(..) => for (key, value) in count_variables_add(&e) {
                    a_row.push((variables.iter().position(|r| r == &key).unwrap(), value));
                },
                e @ _ => panic!("Not flattened: {}", e),
            };
            match rhs {
                box NumberLiteral(x) => b_row.push((0, x)),
                box VariableReference(x) => b_row.push((variables.iter().position(|r| r == &x).unwrap(), T::one())),
                box e @ Add(..) => for (key, value) in count_variables_add(&e) {
                    b_row.push((variables.iter().position(|r| r == &key).unwrap(), value));
                },
                e @ _ => panic!("Not flattened: {}", e),
            };
            for (key, value) in count_variables_add(&linear_expr) {
                c_row.push((variables.iter().position(|r| r == &key).unwrap(), value));
            }
        },
        Div(lhs, rhs) => { // a / b = c --> c * b = a
            match lhs {
                box NumberLiteral(x) => c_row.push((0, x)),
                box VariableReference(x) => c_row.push((variables.iter().position(|r| r == &x).unwrap(), T::one())),
                box e @ Add(..) => for (key, value) in count_variables_add(&e) {
                    c_row.push((variables.iter().position(|r| r == &key).unwrap(), value));
                },
                box e @ Sub(..) => return r1cs_expression(Mult(box linear_expr, rhs), e, variables, a_row, b_row, c_row),
                box Mult(box NumberLiteral(ref x1), box NumberLiteral(ref x2)) => c_row.push((0, x1.clone() * x2)),
                box Mult(box NumberLiteral(ref x), box VariableReference(ref v)) |
                box Mult(box VariableReference(ref v), box NumberLiteral(ref x)) => c_row.push((variables.iter().position(|r| r == v).unwrap(), x.clone())),
                e @ _ => panic!("not implemented yet: {:?}", e),
            };
            match rhs {
                box NumberLiteral(x) => b_row.push((0, x)),
                box VariableReference(x) => b_row.push((variables.iter().position(|r| r == &x).unwrap(), T::one())),
                box Mult(box NumberLiteral(ref x1), box NumberLiteral(ref x2)) => b_row.push((0, x1.clone() * x2)),
                box Mult(box NumberLiteral(ref x), box VariableReference(ref v)) |
                box Mult(box VariableReference(ref v), box NumberLiteral(ref x)) => b_row.push((variables.iter().position(|r| r == v).unwrap(), x.clone())),
                _ => unimplemented!(),
            };
            for (key, value) in count_variables_add(&linear_expr) {
                a_row.push((variables.iter().position(|r| r == &key).unwrap(), value));
            }
        },
        Pow(_, _) => panic!("Pow not flattened"),
        IfElse(_, _, _) => panic!("IfElse not flattened"),
        VariableReference(var) => {
            a_row.push((variables.iter().position(|r| r == &var).unwrap(), T::one()));
            b_row.push((0, T::one()));
            for (key, value) in count_variables_add(&linear_expr) {
                c_row.push((variables.iter().position(|r| r == &key).unwrap(), value));
            }
        },
        NumberLiteral(x) => {
            a_row.push((0, x));
            b_row.push((0, T::one()));
            for (key, value) in count_variables_add(&linear_expr) {
                c_row.push((variables.iter().position(|r| r == &key).unwrap(), value));
            }
        },
    }
}

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
            Statement::Return(ref expr) => {
                variables.push("~out".to_string());
                r1cs_expression(VariableReference("~out".to_string()), expr.clone(), &mut variables, &mut a_row, &mut b_row, &mut c_row);
            },
            Statement::Definition(ref id, ref expr) => {
                variables.push(id.to_string());
                r1cs_expression(VariableReference(id.to_string()), expr.clone(), &mut variables, &mut a_row, &mut b_row, &mut c_row);
            },
            Statement::Condition(ref expr1, ref expr2) => {
                r1cs_expression(expr1.clone(), expr2.clone(), &mut variables, &mut a_row, &mut b_row, &mut c_row);
            },
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
