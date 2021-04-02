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

// We maintain `s`, a set of substitutions as a mapping of `(variable => linear_combination)`. It starts empty.
// We also maintain `i`, a set of variables that should be ignored when trying to substitute. It starts empty.

// - input variables are inserted into `i`
// - the `~one` variable is inserted into `i`
// - For each directive
//      - if all directive inputs are of the form as `coeff * ~one`, execute the solver with all `coeff` as inputs, introducing `res`
//        as the output, and insert `(v, o)` into `s` for `(v, o)` in `(d.outputs, res)`
//      - else, for each variable `v` introduced, insert `v` into `i`
// - For each constraint `c`, we replace all variables by their value in `s` if any, otherwise leave them unchanged. Let's call `c_0` the resulting constraint. We either return `c_0` or nothing based on the form of `c_0`:
//     - `~one * lin == k * v if v isn't in i`: insert `(v, lin / k)` into `s` and return nothing
//     - `q == k * v if v isn't in i`: insert `v` into `i` and return `c_0`
//     - otherwise return `c_0`

use crate::flat_absy::flat_variable::FlatVariable;
use crate::ir::folder::{fold_function, Folder};
use crate::ir::LinComb;
use crate::ir::*;
use std::collections::{HashMap, HashSet};
use zokrates_field::Field;

#[derive(Debug)]
pub struct RedefinitionOptimizer<T: Field> {
    /// Map of renamings for reassigned variables while processing the program.
    substitution: HashMap<FlatVariable, CanonicalLinComb<T>>,
    /// Set of variables that should not be substituted
    ignore: HashSet<FlatVariable>,
}

impl<T: Field> RedefinitionOptimizer<T> {
    fn new() -> Self {
        RedefinitionOptimizer {
            substitution: HashMap::new(),
            ignore: HashSet::new(),
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

                if lin.is_zero() {
                    return vec![Statement::Constraint(quad, lin)];
                }

                let (constraint, to_insert, to_ignore) = match self.ignore.contains(&lin.0[0].0)
                    || self.substitution.contains_key(&lin.0[0].0)
                {
                    true => (Some(Statement::Constraint(quad, lin)), None, None),
                    false => match lin.try_summand() {
                        // if the right side is a single variable
                        Ok((variable, coefficient)) => match quad.try_linear() {
                            // if the left side is linear
                            Ok(l) => (None, Some((variable, l / &coefficient)), None),
                            // if the left side isn't linear
                            Err(quad) => (
                                Some(Statement::Constraint(
                                    quad,
                                    LinComb::summand(coefficient, variable),
                                )),
                                None,
                                Some(variable),
                            ),
                        },
                        Err(l) => (Some(Statement::Constraint(quad, l)), None, None),
                    },
                };

                // insert into the ignored set
                if let Some(v) = to_ignore {
                    self.ignore.insert(v);
                }

                // insert into the substitution map
                if let Some((k, v)) = to_insert {
                    self.substitution.insert(k, v.into_canonical());
                };

                // decide whether the constraint should be kept
                match constraint {
                    Some(c) => vec![c],
                    _ => vec![],
                }
            }
            Statement::Directive(d) => {
                let d = self.fold_directive(d);

                // check if the inputs are constants, ie reduce to the form `coeff * ~one`
                let inputs: Vec<_> = d
                    .inputs
                    .into_iter()
                    // we need to reduce to the canonical form to interpret `a + 1 - a` as `1`
                    .map(|i| i.reduce())
                    .map(|q| {
                        match q
                            .try_linear()
                            .map(|l| l.try_constant().map_err(|l| l.into()))
                        {
                            Ok(r) => r,
                            Err(e) => Err(e),
                        }
                    })
                    .collect::<Vec<Result<T, QuadComb<T>>>>();

                match inputs.iter().all(|i| i.is_ok()) {
                    true => {
                        // unwrap inputs to their constant value
                        let inputs: Vec<_> = inputs.into_iter().map(|i| i.unwrap()).collect();
                        // run the solver
                        let outputs = Interpreter::default()
                            .execute_solver(&d.solver, &inputs)
                            .unwrap();
                        assert_eq!(outputs.len(), d.outputs.len());

                        // insert the results in the substitution
                        for (output, value) in d.outputs.into_iter().zip(outputs.into_iter()) {
                            self.substitution
                                .insert(output, LinComb::from(value).into_canonical());
                        }
                        vec![]
                    }
                    false => {
                        //reconstruct the input expressions
                        let inputs: Vec<_> = inputs
                            .into_iter()
                            .map(|i| {
                                i.map(|v| LinComb::summand(v, FlatVariable::one()).into())
                                    .unwrap_or_else(|q| q)
                            })
                            .collect();
                        // to prevent the optimiser from replacing variables introduced by directives, add them to the ignored set
                        for o in d.outputs.iter().cloned() {
                            self.ignore.insert(o);
                        }
                        vec![Statement::Directive(Directive { inputs, ..d })]
                    }
                }
            }
        }
    }

    fn fold_linear_combination(&mut self, lc: LinComb<T>) -> LinComb<T> {
        match lc
            .0
            .iter()
            .any(|(variable, _)| self.substitution.get(&variable).is_some())
        {
            true =>
            // for each summand, check if it is equal to a linear term in our substitution, otherwise keep it as is
            {
                lc.0.into_iter()
                    .map(|(variable, coefficient)| {
                        self.substitution
                            .get(&variable)
                            .map(|l| LinComb::from(l.clone()) * &coefficient)
                            .unwrap_or_else(|| LinComb::summand(coefficient, variable))
                    })
                    .fold(LinComb::zero(), |acc, x| acc + x)
            }
            false => lc,
        }
    }

    fn fold_argument(&mut self, a: FlatVariable) -> FlatVariable {
        // to prevent the optimiser from replacing user input, add it to the ignored set
        self.ignore.insert(a);
        a
    }

    fn fold_function(&mut self, fun: Function<T>) -> Function<T> {
        // to prevent the optimiser from replacing outputs, add them to the ignored set
        self.ignore.extend(fun.returns.iter().cloned());

        // to prevent the optimiser from replacing ~one, add it to the ignored set
        self.ignore.insert(FlatVariable::one());

        fold_function(self, fun)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::Bn128Field;

    #[test]
    fn remove_synonyms() {
        // def main(x):
        //    y = x
        //    z = y
        //    return z

        let x = FlatVariable::new(0);
        let y = FlatVariable::new(1);
        let z = FlatVariable::new(2);

        let f: Function<Bn128Field> = Function {
            id: "foo".to_string(),
            arguments: vec![x],
            statements: vec![Statement::definition(y, x), Statement::definition(z, y)],
            returns: vec![z],
        };

        let optimized: Function<Bn128Field> = Function {
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

        let f: Function<Bn128Field> = Function {
            id: "foo".to_string(),
            arguments: vec![x],
            statements: vec![Statement::definition(one, x)],
            returns: vec![x],
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

        let f: Function<Bn128Field> = Function {
            id: "foo".to_string(),
            arguments: vec![x],
            statements: vec![
                Statement::definition(y, x),
                Statement::definition(z, y),
                Statement::constraint(z, y),
            ],
            returns: vec![z],
        };

        let optimized: Function<Bn128Field> = Function {
            id: "foo".to_string(),
            arguments: vec![x],
            statements: vec![Statement::definition(z, x), Statement::constraint(z, x)],
            returns: vec![z],
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

        let f: Function<Bn128Field> = Function {
            id: "foo".to_string(),
            arguments: vec![x],
            statements: vec![
                Statement::definition(y, x),
                Statement::definition(t, Bn128Field::from(1)),
                Statement::definition(z, y),
                Statement::definition(w, t),
            ],
            returns: vec![z, w],
        };

        let optimized: Function<Bn128Field> = Function {
            id: "foo".to_string(),
            arguments: vec![x],
            statements: vec![
                Statement::definition(z, x),
                Statement::definition(w, Bn128Field::from(1)),
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
        //    1*x + 1*y + 2*x + 2*y + 3*x + 3*y == 6*x + 6*y // will be eliminated as a tautology
        //    return 6*x + 6*y

        let x = FlatVariable::new(0);
        let y = FlatVariable::new(1);
        let a = FlatVariable::new(2);
        let b = FlatVariable::new(3);
        let c = FlatVariable::new(4);
        let r = FlatVariable::new(5);

        let f: Function<Bn128Field> = Function {
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

        let expected: Function<Bn128Field> = Function {
            id: "foo".to_string(),
            arguments: vec![x, y],
            statements: vec![
                Statement::constraint(
                    LinComb::summand(6, x) + LinComb::summand(6, y),
                    LinComb::summand(6, x) + LinComb::summand(6, y),
                ),
                Statement::definition(
                    r,
                    LinComb::summand(1, x)
                        + LinComb::summand(1, y)
                        + LinComb::summand(2, x)
                        + LinComb::summand(2, y)
                        + LinComb::summand(3, x)
                        + LinComb::summand(3, y),
                ),
            ],
            returns: vec![r],
        };

        let mut optimizer = RedefinitionOptimizer::new();

        let optimized = optimizer.fold_function(f);

        assert_eq!(optimized, expected);
    }

    #[test]
    fn keep_existing_quadratic_variable() {
        // def main(x, y):
        //     z = x * y
        //     z = x
        //     return

        // ->

        // def main(x, y):
        //     z = x * y
        //     z = x
        //     return

        let x = FlatVariable::new(0);
        let y = FlatVariable::new(1);
        let z = FlatVariable::new(2);

        let f: Function<Bn128Field> = Function {
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

        let f: Function<Bn128Field> = Function {
            id: "foo".to_string(),
            arguments: vec![x],
            statements: vec![
                Statement::constraint(x, Bn128Field::from(1)),
                Statement::constraint(x, Bn128Field::from(2)),
            ],
            returns: vec![x],
        };

        let optimized = f.clone();

        let mut optimizer = RedefinitionOptimizer::new();
        assert_eq!(optimizer.fold_function(f), optimized);
    }
}
