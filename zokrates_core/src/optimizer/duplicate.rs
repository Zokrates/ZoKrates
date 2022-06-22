//! Module containing the `DuplicateOptimizer` to remove duplicate constraints

use crate::optimizer::canonicalizer::Canonicalizer;
use std::collections::{hash_map::DefaultHasher, HashSet};
use zokrates_ast::ir::folder::*;
use zokrates_ast::ir::*;
use zokrates_field::Field;

type Hash = u64;

fn hash<T: Field>(s: &Statement<T>) -> Hash {
    use std::hash::Hash;
    use std::hash::Hasher;
    let mut hasher = DefaultHasher::new();
    s.hash(&mut hasher);
    hasher.finish()
}

#[derive(Debug, Default)]
pub struct DuplicateOptimizer {
    seen: HashSet<Hash>,
}

impl<T: Field> Folder<T> for DuplicateOptimizer {
    fn fold_program(&mut self, p: Prog<T>) -> Prog<T> {
        // in order to correctly identify duplicates, we need to first canonicalize the statements
        let mut canonicalizer = Canonicalizer;

        let p = Prog {
            statements: p
                .statements
                .into_iter()
                .flat_map(|s| canonicalizer.fold_statement(s))
                .collect(),
            ..p
        };

        fold_program(self, p)
    }

    fn fold_statement(&mut self, s: Statement<T>) -> Vec<Statement<T>> {
        let hashed = hash(&s);
        let result = match self.seen.get(&hashed) {
            Some(_) => vec![],
            None => vec![s],
        };

        self.seen.insert(hashed);
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_ast::flat::Variable;
    use zokrates_field::Bn128Field;

    #[test]
    fn identity() {
        let p: Prog<Bn128Field> = Prog {
            statements: vec![
                Statement::constraint(
                    QuadComb::from_linear_combinations(
                        LinComb::summand(3, Variable::new(3)),
                        LinComb::summand(3, Variable::new(3)),
                    ),
                    LinComb::one(),
                ),
                Statement::constraint(
                    QuadComb::from_linear_combinations(
                        LinComb::summand(3, Variable::new(42)),
                        LinComb::summand(3, Variable::new(3)),
                    ),
                    LinComb::zero(),
                ),
            ],
            return_count: 0,
            arguments: vec![],
        };

        let expected = p.clone();

        assert_eq!(
            DuplicateOptimizer::default().fold_program(p).collect(),
            expected
        );
    }

    #[test]
    fn remove_duplicates() {
        let constraint = Statement::constraint(
            QuadComb::from_linear_combinations(
                LinComb::summand(3, Variable::new(3)),
                LinComb::summand(3, Variable::new(3)),
            ),
            LinComb::one(),
        );

        let p: Prog<Bn128Field> = Prog {
            statements: vec![
                constraint.clone(),
                constraint.clone(),
                Statement::constraint(
                    QuadComb::from_linear_combinations(
                        LinComb::summand(3, Variable::new(42)),
                        LinComb::summand(3, Variable::new(3)),
                    ),
                    LinComb::zero(),
                ),
                constraint.clone(),
                constraint.clone(),
            ],
            return_count: 0,
            arguments: vec![],
        };

        let expected = Prog {
            statements: vec![
                constraint,
                Statement::constraint(
                    QuadComb::from_linear_combinations(
                        LinComb::summand(3, Variable::new(42)),
                        LinComb::summand(3, Variable::new(3)),
                    ),
                    LinComb::zero(),
                ),
            ],
            return_count: 0,
            arguments: vec![],
        };

        assert_eq!(
            DuplicateOptimizer::default().fold_program(p).collect(),
            expected
        );
    }
}
