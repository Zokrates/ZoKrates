use crate::ir::{Prog, Statement};
use flat_absy::{FlatParameter, FlatVariable};
use zokrates_field::field::Field;

pub struct ConstraintAnalyser;

impl ConstraintAnalyser {
    pub fn analyse<T: Field>(p: Prog<T>) -> Prog<T> {
        Self::check_unconstrained_variables(p.parameters(), &p.main.statements);
        p
    }

    fn check_unconstrained_variables<T: Field>(
        parameters: Vec<FlatParameter>,
        statements: &Vec<Statement<T>>,
    ) {
        let mut variables: Vec<FlatVariable> = parameters
            .iter()
            .filter(|fp| fp.private) // we care only about private parameters
            .map(|fp| fp.id)
            .collect();

        for s in statements {
            match s {
                Statement::Constraint(quad, _) => {
                    let quad_left: Vec<FlatVariable> = quad.left.0.iter().map(|l| l.0).collect();
                    let quad_right: Vec<FlatVariable> = quad.right.0.iter().map(|l| l.0).collect();

                    variables.retain(|e| !(quad_left.contains(e) || quad_right.contains(e)));
                }
                _ => {}
            }
        }

        // we should handle this error instead of asserting?
        assert!(
            variables.is_empty(),
            format!(
                "Unconstrained private parameters are not allowed (found {})",
                variables.len()
            )
        );
    }
}
