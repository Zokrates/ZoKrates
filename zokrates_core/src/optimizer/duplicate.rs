//! Module containing the `DuplicateOptimizer` to remove duplicate constraints

use crate::optimizer::canonicalizer::Canonicalizer;
use std::collections::HashSet;
use zokrates_ast::ir::folder::*;
use zokrates_ast::ir::*;
use zokrates_field::Field;

#[derive(Debug)]
pub struct DuplicateOptimizer<'ast, T> {
    seen: HashSet<Statement<'ast, T>>,
}

impl<'ast, T> Default for DuplicateOptimizer<'ast, T> {
    fn default() -> Self {
        Self {
            seen: HashSet::new(),
        }
    }
}

impl<'ast, T: Field> Folder<'ast, T> for DuplicateOptimizer<'ast, T> {
    fn fold_program(&mut self, p: Prog<'ast, T>) -> Prog<'ast, T> {
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

    fn fold_statement(&mut self, s: Statement<'ast, T>) -> Vec<Statement<'ast, T>> {
        match s {
            Statement::Block(s) => s
                .inner
                .into_iter()
                .flat_map(|s| self.fold_statement(s))
                .collect(),
            s if self.seen.insert(s.clone()) => vec![s],
            _ => vec![],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    use zokrates_ast::flat::Variable;
    use zokrates_field::Bn128Field;

    #[test]
    fn identity() {
        let p: Prog<Bn128Field> = Prog {
            module_map: Default::default(),
            statements: vec![
                Statement::constraint(
                    QuadComb::new(
                        LinComb::summand(3, Variable::new(3)),
                        LinComb::summand(3, Variable::new(3)),
                    ),
                    LinComb::one(),
                    None,
                ),
                Statement::constraint(
                    QuadComb::new(
                        LinComb::summand(3, Variable::new(42)),
                        LinComb::summand(3, Variable::new(3)),
                    ),
                    LinComb::zero(),
                    None,
                ),
            ],
            return_count: 0,
            arguments: vec![],
            solvers: vec![],
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
            QuadComb::new(
                LinComb::summand(3, Variable::new(3)),
                LinComb::summand(3, Variable::new(3)),
            ),
            LinComb::one(),
            None,
        );

        let p: Prog<Bn128Field> = Prog {
            module_map: Default::default(),
            statements: vec![
                constraint.clone(),
                constraint.clone(),
                Statement::constraint(
                    QuadComb::new(
                        LinComb::summand(3, Variable::new(42)),
                        LinComb::summand(3, Variable::new(3)),
                    ),
                    LinComb::zero(),
                    None,
                ),
                constraint.clone(),
                constraint.clone(),
            ],
            return_count: 0,
            arguments: vec![],
            solvers: vec![],
        };

        let expected = Prog {
            module_map: Default::default(),
            statements: vec![
                constraint,
                Statement::constraint(
                    QuadComb::new(
                        LinComb::summand(3, Variable::new(42)),
                        LinComb::summand(3, Variable::new(3)),
                    ),
                    LinComb::zero(),
                    None,
                ),
            ],
            return_count: 0,
            arguments: vec![],
            solvers: vec![],
        };

        assert_eq!(
            DuplicateOptimizer::default().fold_program(p).collect(),
            expected
        );
    }

    #[test]
    fn retains_distinct_statements_with_the_same_hash() {
        let first = Statement::constraint(
            QuadComb::new(LinComb::one(), LinComb::from(Variable::new(0))),
            LinComb::summand(
                Bn128Field::from(3_778_394_870_934_714_281u64),
                Variable::one(),
            ),
            None,
        );
        let second = Statement::constraint(
            QuadComb::new(LinComb::one(), LinComb::from(Variable::new(1))),
            LinComb::summand(
                Bn128Field::from(8_137_133_173_216_420_662u64),
                Variable::one(),
            ),
            None,
        );
        let statement_hash = |statement: &Statement<Bn128Field>| {
            let mut hasher = DefaultHasher::new();
            statement.hash(&mut hasher);
            hasher.finish()
        };
        assert_ne!(first, second);
        assert_eq!(statement_hash(&first), statement_hash(&second));

        let program = Prog {
            module_map: Default::default(),
            statements: vec![first.clone(), second.clone()],
            return_count: 0,
            arguments: vec![],
            solvers: vec![],
        };

        assert_eq!(
            DuplicateOptimizer::default()
                .fold_program(program)
                .statements,
            vec![first, second]
        );
    }
}
