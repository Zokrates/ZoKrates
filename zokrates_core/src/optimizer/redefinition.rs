//! Module containing the `RedefinitionOptimizer` to remove code of the form
// ```
// b := a
// c := b
// ```
// and replace by
// ```
// c := a
// ```

// # Redefinition rules

// ## Defined variables

// We say that a variable `v` is defined in constraint `c_n` or an ir program if there exists a constraint `c_i` with `i < n` of the form:
// ```
// q == k * v
// where:
// - q is quadratic and does not contain `v`
// - k is a scalar
// ```

// ## Optimization rules

// We maintain, `s` a set of substitutions as a mapping of `(variable => linear_combination)`. It starts empty.

// - input variables are inserted in the substitution as `(v, [(1, v)])`
// - the `~one` variable is inserted as `(~one, [(1, ~one)])`
// - For each directive, for each variable `v` introduced, insert `(v, [(1, v)])`
// - For each constraint `c`, we replace all variables by their value in `s` if any, otherwise leave them unchanged. Let's call `c_0` the resulting constraint. We either return `c_0` or nothing based on the form of `c_0`:
//     - `~one * lin == k * v if v isn't defined`: insert `(v, lin / k)` and return nothing
//     - `q == k * v if v isn't defined`: insert `(v, [(1, v)])` and return `c_0`
//     - otherwise return `c_0`

use crate::flat_absy::flat_variable::FlatVariable;
use crate::ir::folder::{fold_function, Folder};
use crate::ir::LinComb;
use crate::ir::*;
use num::Zero;
use std::collections::HashMap;
use zokrates_field::field::Field;

#[derive(Debug)]
pub struct RedefinitionOptimizer<T: Field> {
    /// Map of renamings for reassigned variables while processing the program.
    substitution: HashMap<FlatVariable, LinComb<T>>,
}

impl<T: Field> RedefinitionOptimizer<T> {
    fn new() -> RedefinitionOptimizer<T> {
        RedefinitionOptimizer {
            substitution: HashMap::new(),
        }
    }

    pub fn optimize(p: Prog<T>) -> Prog<T> {
        RedefinitionOptimizer::new().fold_module(p)
    }
}

impl<T: Field> Folder<T> for RedefinitionOptimizer<T> {
    fn fold_statement(&mut self, s: Statement<T>) -> Vec<Statement<T>> {
        match s {
            Statement::Constraint(quad, lin) => {
                let quad = self.fold_quadratic_combination(quad);
                let lin = self.fold_linear_combination(lin);

                let (keep_constraint, to_insert) = match lin.try_summand() {
                    // if the right side is a single variable
                    Some((variable, coefficient)) => {
                        match self.substitution.get(&variable) {
                            // if the variable is already defined
                            Some(_) => (true, None),
                            // if the variable is not defined yet
                            None => match quad.try_linear() {
                                // if the left side is linear
                                Some(l) => (false, Some((variable, l / &coefficient))),
                                // if the left side isn't linear
                                None => (true, Some((variable, variable.into()))),
                            },
                        }
                    }
                    None => (true, None),
                };

                // insert into the substitution map
                match to_insert {
                    Some((k, v)) => {
                        self.substitution.insert(k, v);
                    }
                    None => {}
                };

                // decide whether the constraint should be kept
                match keep_constraint {
                    false => vec![],
                    true => vec![Statement::Constraint(quad, lin)],
                }
            }
            Statement::Directive(d) => {
                let d = self.fold_directive(d);
                // to prevent the optimiser from replacing variables introduced by directives, add them to the substitution
                for o in d.outputs.iter() {
                    self.substitution.insert(o.clone(), o.clone().into());
                }
                vec![Statement::Directive(d)]
            }
        }
    }

    fn fold_linear_combination(&mut self, lc: LinComb<T>) -> LinComb<T> {
        // for each summand, check if it is equal to a linear term in our substitution, otherwise keep it as is
        lc.0.into_iter()
            .map(|(variable, coefficient)| {
                self.substitution
                    .get(&variable)
                    .map(|l| l.clone() * &coefficient)
                    .unwrap_or(LinComb::summand(coefficient, variable))
            })
            .fold(LinComb::zero(), |acc, x| acc + x)
    }

    fn fold_argument(&mut self, a: FlatVariable) -> FlatVariable {
        // to prevent the optimiser from replacing user input, add it to the substitution
        self.substitution.insert(a.clone(), a.clone().into());
        a
    }

    fn fold_function(&mut self, fun: Function<T>) -> Function<T> {
        self.substitution.drain();

        // to prevent the optimiser from replacing outputs, add them to the substitution
        self.substitution
            .extend(fun.returns.iter().map(|x| (x.clone(), x.clone().into())));

        // to prevent the optimiser from replacing ~one, add it to the substitution
        self.substitution
            .insert(FlatVariable::one(), FlatVariable::one().into());

        fold_function(self, fun)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn remove_synonyms() {
        // def main(x):
        //    y = x
        //    z = y
        //    return z

        let x = FlatVariable::new(0);
        let y = FlatVariable::new(1);
        let z = FlatVariable::new(2);

        let f: Function<FieldPrime> = Function {
            id: "foo".to_string(),
            arguments: vec![x],
            statements: vec![Statement::definition(y, x), Statement::definition(z, y)],
            returns: vec![z.into()],
        };

        let optimized: Function<FieldPrime> = Function {
            id: "foo".to_string(),
            arguments: vec![x],
            statements: vec![Statement::definition(z, x)],
            returns: vec![z],
        };

        let mut optimizer = RedefinitionOptimizer::new();
        assert_eq!(optimizer.fold_function(f), optimized);
    }

    #[test]
    fn keep_one() {
        // def main(x):
        //    one = x
        //    return one

        let one = FlatVariable::one();
        let x = FlatVariable::new(1);

        let f: Function<FieldPrime> = Function {
            id: "foo".to_string(),
            arguments: vec![x],
            statements: vec![Statement::definition(one, x)],
            returns: vec![x.into()],
        };

        let optimized = f.clone();

        let mut optimizer = RedefinitionOptimizer::new();
        assert_eq!(optimizer.fold_function(f), optimized);
    }

    #[test]
    fn remove_synonyms_in_condition() {
        // def main(x) -> (1):
        //    y = x
        //    z = y
        //    z == y
        //    return z

        // ->

        // def main(x) -> (1)
        //    x == x // will be eliminated as a tautology
        //    return x

        let x = FlatVariable::new(0);
        let y = FlatVariable::new(1);
        let z = FlatVariable::new(2);

        let f: Function<FieldPrime> = Function {
            id: "foo".to_string(),
            arguments: vec![x],
            statements: vec![
                Statement::definition(y, x),
                Statement::definition(z, y),
                Statement::constraint(z, y),
            ],
            returns: vec![z.into()],
        };

        let optimized: Function<FieldPrime> = Function {
            id: "foo".to_string(),
            arguments: vec![x],
            statements: vec![Statement::definition(z, x), Statement::constraint(z, x)],
            returns: vec![z.into()],
        };

        let mut optimizer = RedefinitionOptimizer::new();
        assert_eq!(optimizer.fold_function(f), optimized);
    }

    #[test]
    fn remove_multiple_synonyms() {
        // def main(x) -> (2):
        //    y = x
        //    t = 1
        //    z = y
        //    w = t
        //    return z, w

        // ->

        // def main(x):
        //  return x, 1

        let x = FlatVariable::new(0);
        let y = FlatVariable::new(1);
        let z = FlatVariable::new(2);
        let t = FlatVariable::new(3);
        let w = FlatVariable::new(4);

        let f: Function<FieldPrime> = Function {
            id: "foo".to_string(),
            arguments: vec![x],
            statements: vec![
                Statement::definition(y, x),
                Statement::definition(t, FieldPrime::from(1)),
                Statement::definition(z, y),
                Statement::definition(w, t),
            ],
            returns: vec![z, w],
        };

        let optimized: Function<FieldPrime> = Function {
            id: "foo".to_string(),
            arguments: vec![x],
            statements: vec![
                Statement::definition(z, x),
                Statement::definition(w, FieldPrime::from(1)),
            ],
            returns: vec![z, w],
        };

        let mut optimizer = RedefinitionOptimizer::new();

        assert_eq!(optimizer.fold_function(f), optimized);
    }

    #[test]
    fn substitute_lincomb() {
        // def main(x, y) -> (1):
        //     a = x + y
        //     b = a + x + y
        //     c = b + x + y
        //     2*c == 6*x + 6*y
        //     r = a + b + c
        //     return r

        // ->

        // def main(x, y) -> (1):
        //    6*x + 6*y == 6*x + 6*y // will be eliminated as a tautology
        //    return 6*x + 6*y

        let x = FlatVariable::new(0);
        let y = FlatVariable::new(1);
        let a = FlatVariable::new(2);
        let b = FlatVariable::new(3);
        let c = FlatVariable::new(4);
        let r = FlatVariable::new(5);

        let f: Function<FieldPrime> = Function {
            id: "foo".to_string(),
            arguments: vec![x, y],
            statements: vec![
                Statement::definition(a, LinComb::from(x) + LinComb::from(y)),
                Statement::definition(b, LinComb::from(a) + LinComb::from(x) + LinComb::from(y)),
                Statement::definition(c, LinComb::from(b) + LinComb::from(x) + LinComb::from(y)),
                Statement::constraint(
                    LinComb::summand(2, c),
                    LinComb::summand(6, x) + LinComb::summand(6, y),
                ),
                Statement::definition(r, LinComb::from(a) + LinComb::from(b) + LinComb::from(c)),
            ],
            returns: vec![r],
        };

        let optimized: Function<FieldPrime> = Function {
            id: "foo".to_string(),
            arguments: vec![x, y],
            statements: vec![
                Statement::constraint(
                    LinComb::summand(6, x) + LinComb::summand(6, y),
                    LinComb::summand(6, x) + LinComb::summand(6, y),
                ),
                Statement::definition(r, LinComb::summand(6, x) + LinComb::summand(6, y)),
            ],
            returns: vec![r],
        };

        let mut optimizer = RedefinitionOptimizer::new();
        assert_eq!(optimizer.fold_function(f), optimized);
    }

    #[test]
    fn keep_existing_quadratic_variable() {
        // def main(x, y) -> ():
        //     z = x * y
        //     z = x
        //     return

        // ->

        // def main(x, y) -> ():
        //     z = x * y
        //     z = x
        //     return

        let x = FlatVariable::new(0);
        let y = FlatVariable::new(1);
        let z = FlatVariable::new(2);

        let f: Function<FieldPrime> = Function {
            id: "main".to_string(),
            arguments: vec![x, y],
            statements: vec![
                Statement::definition(
                    z,
                    QuadComb::from_linear_combinations(LinComb::from(x), LinComb::from(y)),
                ),
                Statement::definition(z, LinComb::from(x)),
            ],
            returns: vec![],
        };

        let optimized = f.clone();

        let mut optimizer = RedefinitionOptimizer::new();
        assert_eq!(optimizer.fold_function(f), optimized);
    }

    #[test]
    fn keep_existing_variable() {
        // def main(x) -> (1):
        //     x == 1
        //     x == 2
        //     return x

        // ->

        // unchanged

        let x = FlatVariable::new(0);

        let f: Function<FieldPrime> = Function {
            id: "foo".to_string(),
            arguments: vec![x],
            statements: vec![
                Statement::constraint(x, FieldPrime::from(1)),
                Statement::constraint(x, FieldPrime::from(2)),
            ],
            returns: vec![x.into()],
        };

        let optimized = f.clone();

        let mut optimizer = RedefinitionOptimizer::new();
        assert_eq!(optimizer.fold_function(f), optimized);
    }
}
