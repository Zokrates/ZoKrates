//! Module containing constant propagation for the flat AST
//!
//! @file propagation.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use std::collections::HashMap;
use zokrates_ast::flat::folder::*;
use zokrates_ast::flat::*;
use zokrates_field::Field;

#[derive(Default)]
struct Propagator<T> {
    constants: HashMap<Variable, T>,
}

impl<T: Field> Folder<T> for Propagator<T> {
    fn fold_statement(&mut self, s: FlatStatement<T>) -> Vec<FlatStatement<T>> {
        match s {
            FlatStatement::Definition(var, expr) => match self.fold_expression(expr) {
                FlatExpression::Number(n) => {
                    self.constants.insert(var, n);
                    vec![]
                }
                e => vec![FlatStatement::Definition(var, e)],
            },
            s => fold_statement(self, s),
        }
    }

    fn fold_expression(&mut self, e: FlatExpression<T>) -> FlatExpression<T> {
        match e {
            FlatExpression::Number(n) => FlatExpression::Number(n),
            FlatExpression::Identifier(id) => match self.constants.get(&id) {
                Some(c) => FlatExpression::Number(c.clone()),
                None => FlatExpression::Identifier(id),
            },
            FlatExpression::Add(box e1, box e2) => {
                match (self.fold_expression(e1), self.fold_expression(e2)) {
                    (FlatExpression::Number(n1), FlatExpression::Number(n2)) => {
                        FlatExpression::Number(n1 + n2)
                    }
                    (e1, e2) => FlatExpression::Add(box e1, box e2),
                }
            }
            FlatExpression::Sub(box e1, box e2) => {
                match (self.fold_expression(e1), self.fold_expression(e2)) {
                    (FlatExpression::Number(n1), FlatExpression::Number(n2)) => {
                        FlatExpression::Number(n1 - n2)
                    }
                    (e1, e2) => FlatExpression::Sub(box e1, box e2),
                }
            }
            FlatExpression::Mult(box e1, box e2) => {
                match (self.fold_expression(e1), self.fold_expression(e2)) {
                    (FlatExpression::Number(n1), FlatExpression::Number(n2)) => {
                        FlatExpression::Number(n1 * n2)
                    }
                    (e1, e2) => FlatExpression::Mult(box e1, box e2),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::Bn128Field;

    #[cfg(test)]
    mod expression {
        use super::*;

        #[cfg(test)]
        mod field {
            use super::*;

            #[test]
            fn add() {
                let mut propagator = Propagator::default();

                let e = FlatExpression::Add(
                    box FlatExpression::Number(Bn128Field::from(2)),
                    box FlatExpression::Number(Bn128Field::from(3)),
                );

                assert_eq!(
                    propagator.fold_expression(e),
                    FlatExpression::Number(Bn128Field::from(5))
                );
            }

            #[test]
            fn sub() {
                let mut propagator = Propagator::default();

                let e = FlatExpression::Sub(
                    box FlatExpression::Number(Bn128Field::from(3)),
                    box FlatExpression::Number(Bn128Field::from(2)),
                );

                assert_eq!(
                    propagator.fold_expression(e),
                    FlatExpression::Number(Bn128Field::from(1))
                );
            }

            #[test]
            fn mult() {
                let mut propagator = Propagator::default();

                let e = FlatExpression::Mult(
                    box FlatExpression::Number(Bn128Field::from(3)),
                    box FlatExpression::Number(Bn128Field::from(2)),
                );

                assert_eq!(
                    propagator.fold_expression(e),
                    FlatExpression::Number(Bn128Field::from(6))
                );
            }
        }
    }
}
