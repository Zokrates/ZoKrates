//! Module containing the `DuplicateOptimizer` to remove duplicate constraints

use crate::ir::folder::*;
use crate::ir::*;
use std::collections::{hash_map::DefaultHasher, HashSet};
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
    use crate::flat_absy::FlatVariable;
    use zokrates_field::Bn128Field;

    #[test]
    fn identity() {
        let p: Prog<Bn128Field> = Prog::new(
            vec![],
            vec![
                Statement::constraint(
                    QuadComb::from_linear_combinations(
                        LinComb::summand(3, FlatVariable::new(3)),
                        LinComb::summand(3, FlatVariable::new(3)),
                    ),
                    LinComb::one(),
                ),
                Statement::constraint(
                    QuadComb::from_linear_combinations(
                        LinComb::summand(3, FlatVariable::new(42)),
                        LinComb::summand(3, FlatVariable::new(3)),
                    ),
                    LinComb::zero(),
                ),
            ]
            .into(),
            0,
        );

        let expected = p.clone();

        assert_eq!(
            DuplicateOptimizer::default()
                .fold_program(p)
                .collect()
                .unwrap(),
            expected
        );
    }

    #[test]
    fn remove_duplicates() {
        let constraint = Statement::constraint(
            QuadComb::from_linear_combinations(
                LinComb::summand(3, FlatVariable::new(3)),
                LinComb::summand(3, FlatVariable::new(3)),
            ),
            LinComb::one(),
        );

        let p: Prog<Bn128Field> = Prog::new(
            vec![],
            vec![
                constraint.clone(),
                constraint.clone(),
                Statement::constraint(
                    QuadComb::from_linear_combinations(
                        LinComb::summand(3, FlatVariable::new(42)),
                        LinComb::summand(3, FlatVariable::new(3)),
                    ),
                    LinComb::zero(),
                ),
                constraint.clone(),
                constraint.clone(),
            ]
            .into(),
            0,
        );

        let expected = Prog::new(
            vec![],
            vec![
                constraint,
                Statement::constraint(
                    QuadComb::from_linear_combinations(
                        LinComb::summand(3, FlatVariable::new(42)),
                        LinComb::summand(3, FlatVariable::new(3)),
                    ),
                    LinComb::zero(),
                ),
            ]
            .into(),
            0,
        );

        assert_eq!(
            DuplicateOptimizer::default()
                .fold_program(p)
                .collect()
                .unwrap(),
            expected
        );
    }
}
