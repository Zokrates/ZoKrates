//! Module containing the `DuplicateOptimizer` to remove duplicate constraints

use crate::ir::folder::Folder;
use crate::ir::*;
use std::collections::{hash_map::DefaultHasher, HashSet};
use zokrates_field::field::Field;

type Hash = u64;

fn hash<T: Field>(s: &Statement<T>) -> Hash {
    use std::hash::Hash;
    use std::hash::Hasher;
    let mut hasher = DefaultHasher::new();
    s.hash(&mut hasher);
    hasher.finish()
}

#[derive(Debug)]
pub struct DuplicateOptimizer {
    seen: HashSet<Hash>,
}

impl DuplicateOptimizer {
    fn new() -> Self {
        DuplicateOptimizer {
            seen: HashSet::new(),
        }
    }

    pub fn optimize<T: Field>(p: Prog<T>) -> Prog<T> {
        Self::new().fold_module(p)
    }
}

impl<T: Field> Folder<T> for DuplicateOptimizer {
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
    use flat_absy::FlatVariable;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn identity() {
        use num::Zero;

        let p: Prog<FieldPrime> = Prog {
            private: vec![],
            main: Function {
                id: "main".to_string(),
                statements: vec![
                    Statement::Constraint(
                        QuadComb::from_linear_combinations(
                            LinComb::summand(3, FlatVariable::new(3)),
                            LinComb::summand(3, FlatVariable::new(3)),
                        ),
                        LinComb::one(),
                    ),
                    Statement::Constraint(
                        QuadComb::from_linear_combinations(
                            LinComb::summand(3, FlatVariable::new(42)),
                            LinComb::summand(3, FlatVariable::new(3)),
                        ),
                        LinComb::zero(),
                    ),
                ],
                returns: vec![],
                arguments: vec![],
            },
        };

        let expected = p.clone();

        assert_eq!(DuplicateOptimizer::optimize(p), expected);
    }

    #[test]
    fn remove_duplicates() {
        use num::Zero;

        let constraint = Statement::Constraint(
            QuadComb::from_linear_combinations(
                LinComb::summand(3, FlatVariable::new(3)),
                LinComb::summand(3, FlatVariable::new(3)),
            ),
            LinComb::one(),
        );

        let p: Prog<FieldPrime> = Prog {
            private: vec![],
            main: Function {
                id: "main".to_string(),
                statements: vec![
                    constraint.clone(),
                    constraint.clone(),
                    Statement::Constraint(
                        QuadComb::from_linear_combinations(
                            LinComb::summand(3, FlatVariable::new(42)),
                            LinComb::summand(3, FlatVariable::new(3)),
                        ),
                        LinComb::zero(),
                    ),
                    constraint.clone(),
                    constraint.clone(),
                ],
                returns: vec![],
                arguments: vec![],
            },
        };

        let expected = Prog {
            private: vec![],
            main: Function {
                id: "main".to_string(),
                statements: vec![
                    constraint.clone(),
                    Statement::Constraint(
                        QuadComb::from_linear_combinations(
                            LinComb::summand(3, FlatVariable::new(42)),
                            LinComb::summand(3, FlatVariable::new(3)),
                        ),
                        LinComb::zero(),
                    ),
                ],
                returns: vec![],
                arguments: vec![],
            },
        };

        assert_eq!(DuplicateOptimizer::optimize(p), expected);
    }
}
