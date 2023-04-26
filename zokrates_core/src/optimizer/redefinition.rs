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

use std::collections::{HashMap, HashSet};
use zokrates_ast::common::WithSpan;
use zokrates_ast::flat::Variable;
use zokrates_ast::ir::folder::{fold_statement_cases, Folder};
use zokrates_ast::ir::LinComb;
use zokrates_ast::ir::*;
use zokrates_field::Field;
use zokrates_interpreter::Interpreter;

#[derive(Debug)]
pub struct RedefinitionOptimizer<T> {
    /// Map of renamings for reassigned variables while processing the program.
    substitution: HashMap<Variable, CanonicalLinComb<T>>,
    /// Set of variables that should not be substituted
    pub ignore: HashSet<Variable>,
}

impl<T: Field> RedefinitionOptimizer<T> {
    pub fn init<'ast, I: IntoIterator<Item = Statement<'ast, T>>>(
        p: &ProgIterator<'ast, T, I>,
    ) -> Self {
        RedefinitionOptimizer {
            substitution: HashMap::new(),
            ignore: vec![Variable::one()]
                .into_iter()
                .chain(p.arguments.iter().map(|p| p.id))
                .chain(p.returns())
                .collect(),
        }
    }

    fn fold_statement_cases<'ast>(
        &mut self,
        s: Statement<'ast, T>,
        aggressive: bool,
    ) -> Vec<Statement<'ast, T>> {
        match s {
            Statement::Constraint(s) => {
                let quad = self.fold_quadratic_combination(s.quad);
                let lin = self.fold_linear_combination(s.lin);

                if lin.is_zero() {
                    return vec![Statement::constraint(quad, lin, s.error)];
                }

                let (constraint, to_insert, to_ignore) = match self.ignore.contains(&lin.value[0].0)
                    || self.substitution.contains_key(&lin.value[0].0)
                {
                    true => (Some(Statement::constraint(quad, lin, s.error)), None, None),
                    false => match lin.try_summand() {
                        // if the right side is a single variable
                        Ok((variable, coefficient)) => match quad.try_linear() {
                            // if the left side is linear
                            Ok(l) => (None, Some((variable, l / &coefficient)), None),
                            // if the left side isn't linear
                            Err(quad) => (
                                Some(Statement::constraint(
                                    quad,
                                    LinComb::summand(coefficient, variable),
                                    s.error,
                                )),
                                None,
                                Some(variable),
                            ),
                        },
                        Err(l) => (Some(Statement::constraint(quad, l, s.error)), None, None),
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
                let d = DirectiveStatement {
                    inputs: d
                        .inputs
                        .into_iter()
                        .map(|e| self.fold_quadratic_combination(e))
                        .collect(),
                    outputs: d
                        .outputs
                        .into_iter()
                        .map(|o| self.fold_variable(o))
                        .collect(),
                    ..d
                };

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
                        let outputs = Interpreter::execute_solver(&d.solver, &inputs, &[]).unwrap();
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
                                i.map(|v| LinComb::summand(v, Variable::one()).into())
                                    .unwrap_or_else(|q| q)
                            })
                            .collect();
                        if !aggressive {
                            // to prevent the optimiser from replacing variables introduced by directives, add them to the ignored set
                            for o in d.outputs.iter().cloned() {
                                self.ignore.insert(o);
                            }
                        }
                        vec![Statement::directive(d.outputs, d.solver, inputs)]
                    }
                }
            }
            s => fold_statement_cases(self, s),
        }
    }
}

impl<'ast, T: Field> Folder<'ast, T> for RedefinitionOptimizer<T> {
    fn fold_statement_cases(&mut self, s: Statement<'ast, T>) -> Vec<Statement<'ast, T>> {
        match s {
            Statement::Block(statements) => {
                #[allow(clippy::needless_collect)]
                // optimize aggressively and clean up in a second pass (we need to collect here)
                let statements: Vec<_> = statements
                    .inner
                    .into_iter()
                    .flat_map(|s| {
                        let span = s.get_span();
                        self.fold_statement_cases(s, true)
                            .into_iter()
                            .map(move |s| s.span(span))
                    })
                    .collect();

                // clean up
                let statements = statements
                    .into_iter()
                    .filter(|s| match s {
                        // we remove a directive iff it has a single output and this output is in the substitution map, meaning it was propagated
                        Statement::Directive(d) => {
                            d.outputs.len() > 1 || !self.substitution.contains_key(&d.outputs[0])
                        }
                        _ => true,
                    })
                    .collect();

                vec![Statement::block(statements)]
            }
            s => self.fold_statement_cases(s, false),
        }
    }

    fn fold_linear_combination(&mut self, lc: LinComb<T>) -> LinComb<T> {
        match lc
            .value
            .iter()
            .any(|(variable, _)| self.substitution.get(variable).is_some())
        {
            true =>
            // for each summand, check if it is equal to a linear term in our substitution, otherwise keep it as is
            {
                lc.value
                    .into_iter()
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_ast::flat::Parameter;
    use zokrates_field::Bn128Field;

    #[test]
    fn remove_synonyms() {
        // def main(x):
        //    y = x
        //    z = y
        //    return z

        let x = Parameter::public(Variable::new(0));
        let y = Variable::new(1);
        let out = Variable::public(0);

        let p: Prog<Bn128Field> = Prog {
            module_map: Default::default(),
            arguments: vec![x],
            statements: vec![
                Statement::definition(y, x.id),
                Statement::definition(out, y),
            ],
            return_count: 1,
            solvers: vec![],
        };

        let optimized: Prog<Bn128Field> = Prog {
            module_map: Default::default(),
            arguments: vec![x],
            statements: vec![Statement::definition(out, x.id)],
            return_count: 1,
            solvers: vec![],
        };

        let mut optimizer = RedefinitionOptimizer::init(&p);
        assert_eq!(optimizer.fold_program(p), optimized);
    }

    #[test]
    fn keep_one() {
        // def main(x):
        //    one = x

        let one = Variable::one();
        let x = Parameter::public(Variable::new(0));

        let p: Prog<Bn128Field> = Prog {
            module_map: Default::default(),
            arguments: vec![x],
            statements: vec![Statement::definition(one, x.id)],
            return_count: 1,
            solvers: vec![],
        };

        let optimized = p.clone();

        let mut optimizer = RedefinitionOptimizer::init(&p);
        assert_eq!(optimizer.fold_program(p), optimized);
    }

    #[test]
    fn remove_synonyms_in_condition() {
        // def main(x) -> (1):
        //    y = x
        //    z = y
        //    z == y
        //    ~out_0 = z

        // ->

        // def main(x) -> (1)
        //    x == x // will be eliminated as a tautology
        //    return x

        let x = Parameter::public(Variable::new(0));
        let y = Variable::new(1);
        let z = Variable::new(2);
        let out = Variable::public(0);

        let p: Prog<Bn128Field> = Prog {
            module_map: Default::default(),
            arguments: vec![x],
            statements: vec![
                Statement::definition(y, x.id),
                Statement::definition(z, y),
                Statement::constraint(z, y, None),
                Statement::definition(out, z),
            ],
            return_count: 1,
            solvers: vec![],
        };

        let optimized: Prog<Bn128Field> = Prog {
            module_map: Default::default(),
            arguments: vec![x],
            statements: vec![
                Statement::constraint(x.id, x.id, None),
                Statement::definition(out, x.id),
            ],
            return_count: 1,
            solvers: vec![],
        };

        let mut optimizer = RedefinitionOptimizer::init(&p);
        assert_eq!(optimizer.fold_program(p), optimized);
    }

    #[test]
    fn remove_multiple_synonyms() {
        // def main(x) -> (2):
        //    y = x
        //    t = 1
        //    z = y
        //    w = t
        //    ~out_0 = z
        //    ~out_1 = w

        // ->

        // def main(x):
        //  return x, 1

        let x = Parameter::public(Variable::new(0));
        let y = Variable::new(1);
        let z = Variable::new(2);
        let t = Variable::new(3);
        let w = Variable::new(4);
        let out_1 = Variable::public(0);
        let out_0 = Variable::public(1);

        let p: Prog<Bn128Field> = Prog {
            module_map: Default::default(),
            arguments: vec![x],
            statements: vec![
                Statement::definition(y, x.id),
                Statement::definition(t, Bn128Field::from(1)),
                Statement::definition(z, y),
                Statement::definition(w, t),
                Statement::definition(out_0, z),
                Statement::definition(out_1, w),
            ],
            return_count: 2,
            solvers: vec![],
        };

        let optimized: Prog<Bn128Field> = Prog {
            module_map: Default::default(),
            arguments: vec![x],
            statements: vec![
                Statement::definition(out_0, x.id),
                Statement::definition(out_1, Bn128Field::from(1)),
            ],
            return_count: 2,
            solvers: vec![],
        };

        let mut optimizer = RedefinitionOptimizer::init(&p);

        assert_eq!(optimizer.fold_program(p), optimized);
    }

    #[test]
    fn substitute_lincomb() {
        // def main(x, y) -> (1):
        //     a = x + y
        //     b = a + x + y
        //     c = b + x + y
        //     2*c == 6*x + 6*y
        //     ~out_0 = a + b + c

        // ->

        // def main(x, y) -> (1):
        //    1*x + 1*y + 2*x + 2*y + 3*x + 3*y == 6*x + 6*y // will be eliminated as a tautology
        //    ~out_0 = 6*x + 6*y

        let x = Parameter::public(Variable::new(0));
        let y = Parameter::public(Variable::new(1));
        let a = Variable::new(2);
        let b = Variable::new(3);
        let c = Variable::new(4);
        let r = Variable::public(0);

        let p: Prog<Bn128Field> = Prog {
            module_map: Default::default(),
            arguments: vec![x, y],
            statements: vec![
                Statement::definition(a, LinComb::from(x.id) + LinComb::from(y.id)),
                Statement::definition(
                    b,
                    LinComb::from(a) + LinComb::from(x.id) + LinComb::from(y.id),
                ),
                Statement::definition(
                    c,
                    LinComb::from(b) + LinComb::from(x.id) + LinComb::from(y.id),
                ),
                Statement::constraint(
                    LinComb::summand(2, c),
                    LinComb::summand(6, x.id) + LinComb::summand(6, y.id),
                    None,
                ),
                Statement::definition(r, LinComb::from(a) + LinComb::from(b) + LinComb::from(c)),
            ],
            return_count: 1,
            solvers: vec![],
        };

        let expected: Prog<Bn128Field> = Prog {
            module_map: Default::default(),
            arguments: vec![x, y],
            statements: vec![
                Statement::constraint(
                    LinComb::summand(6, x.id) + LinComb::summand(6, y.id),
                    LinComb::summand(6, x.id) + LinComb::summand(6, y.id),
                    None,
                ),
                Statement::definition(
                    r,
                    LinComb::summand(1, x.id)
                        + LinComb::summand(1, y.id)
                        + LinComb::summand(2, x.id)
                        + LinComb::summand(2, y.id)
                        + LinComb::summand(3, x.id)
                        + LinComb::summand(3, y.id),
                ),
            ],
            return_count: 1,
            solvers: vec![],
        };

        let mut optimizer = RedefinitionOptimizer::init(&p);

        let optimized = optimizer.fold_program(p);

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

        let x = Parameter::public(Variable::new(0));
        let y = Parameter::public(Variable::new(1));
        let z = Variable::new(2);

        let p: Prog<Bn128Field> = Prog {
            module_map: Default::default(),
            arguments: vec![x, y],
            statements: vec![
                Statement::definition(z, QuadComb::new(LinComb::from(x.id), LinComb::from(y.id))),
                Statement::definition(z, LinComb::from(x.id)),
            ],
            return_count: 0,
            solvers: vec![],
        };

        let optimized = p.clone();

        let mut optimizer = RedefinitionOptimizer::init(&p);
        assert_eq!(optimizer.fold_program(p), optimized);
    }

    #[test]
    fn keep_existing_variable() {
        // def main(x) -> (1):
        //     x == 1
        //     x == 2
        //     return x

        // ->

        // unchanged

        let x = Parameter::public(Variable::new(0));

        let p: Prog<Bn128Field> = Prog {
            module_map: Default::default(),
            arguments: vec![x],
            statements: vec![
                Statement::constraint(x.id, Bn128Field::from(1), None),
                Statement::constraint(x.id, Bn128Field::from(2), None),
            ],
            return_count: 1,
            solvers: vec![],
        };

        let optimized = p.clone();

        let mut optimizer = RedefinitionOptimizer::init(&p);
        assert_eq!(optimizer.fold_program(p), optimized);
    }
}
