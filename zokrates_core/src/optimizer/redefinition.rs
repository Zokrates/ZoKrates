//! Module containing the `RedefinitionOptimizer` to remove code of the form
// ```
// b := a
// c := b
// ```
// and replace by
// ```
// c := a
// ```

use crate::flat_absy::flat_variable::FlatVariable;
use crate::ir::folder::Folder;
use crate::ir::*;
use crate::ir::{LinComb, QuadComb};
use std::hash::Hash;

use std::collections::hash_map::{DefaultHasher, Entry, HashMap};
use zokrates_field::field::Field;

type HashValue = u64;

fn hash<T: Hash>(t: &T) -> HashValue {
    use std::hash::Hasher;
    let mut hasher = DefaultHasher::new();
    t.hash(&mut hasher);
    hasher.finish()
}

#[derive(Debug, PartialEq, Eq, Default)]
struct Map<T: Field> {
    key_to_hash: HashMap<FlatVariable, HashValue>,
    hash_to_value: HashMap<HashValue, LinComb<T>>,
}

impl<T: Field> Map<T> {
    fn new() -> Self {
        Map {
            key_to_hash: HashMap::new(),
            hash_to_value: HashMap::new(),
        }
    }

    fn drain(&mut self) {
        self.key_to_hash.drain();
        self.hash_to_value.drain();
    }

    fn get(&self, key: &FlatVariable) -> Option<&LinComb<T>> {
        self.key_to_hash
            .get(key)
            .map(|h| self.hash_to_value.get(h).unwrap())
    }

    fn insert(&mut self, key: FlatVariable, value: LinComb<T>) -> Option<LinComb<T>> {
        self.key_to_hash.entry(key).or_insert_with(|| hash(&value));
        self.hash_to_value.insert(hash(&value), value)
    }

    fn entries(
        &mut self,
        k: FlatVariable,
        h: HashValue,
    ) -> (Entry<FlatVariable, HashValue>, Entry<HashValue, LinComb<T>>) {
        (self.key_to_hash.entry(k), self.hash_to_value.entry(h))
    }
}

impl<T: Field> Extend<(FlatVariable, LinComb<T>)> for Map<T> {
    #[inline]
    fn extend<U: IntoIterator<Item = (FlatVariable, LinComb<T>)>>(&mut self, iter: U) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

#[derive(Debug)]
pub struct RedefinitionOptimizer<T: Field> {
    /// Map of renamings for reassigned variables while processing the program.
    substitution: Map<T>,
    hits: usize,
}

impl<T: Field> RedefinitionOptimizer<T> {
    pub fn new() -> RedefinitionOptimizer<T> {
        RedefinitionOptimizer {
            substitution: Map::new(),
            hits: 0,
        }
    }

    pub fn optimize(p: Prog<T>) -> Prog<T> {
        RedefinitionOptimizer::new().fold_module(p)
    }

    fn fold_statement_opt(&mut self, s: Statement<T>) -> Option<Statement<T>> {
        match s {
            // Detect constraints of the form `lincomb * ~ONE == x` where x is not in the map yet
            Statement::Constraint(quad, lin) => {
                let quad = self.fold_quadratic_combination(quad);
                let lin = self.fold_linear_combination(lin);

                match quad.try_linear() {
                    // left side must be linear
                    Ok(l) => match lin.try_summand() {
                        // right side must be a single variable
                        Ok((variable, coefficient)) => {
                            match variable == FlatVariable::one() {
                                // variable must not be ~ONE
                                false => {
                                    let l = l / &coefficient;
                                    let hash = hash(&l);
                                    match self.substitution.entries(variable, hash) {
                                        (Entry::Occupied(_), _) => Some(Statement::Constraint(
                                            QuadComb::from_linear_combinations(LinComb::one(), l),
                                            variable.into(),
                                        )),
                                        (Entry::Vacant(v), e) => {
                                            self.hits += 1;
                                            e.or_insert(l);
                                            v.insert(hash);
                                            None
                                        }
                                    }
                                }
                                true => Some(Statement::Constraint(
                                    QuadComb::from_linear_combinations(LinComb::one(), l),
                                    LinComb::summand(coefficient, variable),
                                )),
                            }
                        }
                        Err(lin) => Some(Statement::Constraint(
                            QuadComb::from_linear_combinations(LinComb::one(), l),
                            lin,
                        )),
                    },
                    Err(quad) => Some(Statement::Constraint(quad, lin)),
                }
            }
            Statement::Directive(d) => {
                let d = self.fold_directive(d);
                // to prevent the optimiser from replacing variables introduced by directives, add them to the substitution
                for o in d.outputs.iter() {
                    self.substitution.insert(o.clone(), o.clone().into());
                }
                Some(Statement::Directive(d))
            }
        }
    }
}

impl<T: Field> Folder<T> for RedefinitionOptimizer<T> {
    fn fold_linear_combination(&mut self, lc: LinComb<T>) -> LinComb<T> {
        // for each summand, check if it is equal to a linear term in our substitution, otherwise keep it as is

        let mut result = vec![];

        for (variable, coefficient) in lc.0.into_iter() {
            match self.substitution.get(&variable) {
                Some(l) => {
                    result.extend(l.0.clone().into_iter().map(|(v, c)| (v, c * &coefficient)))
                } // we only clone in the case that we found a value in the map
                None => result.push((variable, coefficient)),
            }
        }

        LinComb(result)
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

        Function {
            arguments: fun
                .arguments
                .into_iter()
                .map(|a| self.fold_argument(a))
                .collect(),
            statements: fun
                .statements
                .into_iter()
                .filter_map(|s| self.fold_statement_opt(s))
                .collect(),
            returns: fun
                .returns
                .into_iter()
                .map(|v| self.fold_variable(v))
                .collect(),
            ..fun
        }
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
