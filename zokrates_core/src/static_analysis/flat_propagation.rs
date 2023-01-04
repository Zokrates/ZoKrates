//! Module containing constant propagation for the flat AST
//!
//! @file propagation.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use std::collections::HashMap;
use std::ops::*;
use zokrates_ast::common::expressions::IdentifierOrExpression;
use zokrates_ast::common::WithSpan;
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
                    self.constants.insert(var, n.value);
                    vec![]
                }
                e => vec![FlatStatement::Definition(var, e)],
            },
            s => fold_statement(self, s),
        }
    }

    fn fold_identifier_expression(
        &mut self,
        e: zokrates_ast::common::expressions::IdentifierExpression<Variable, FlatExpression<T>>,
    ) -> IdentifierOrExpression<Variable, FlatExpression<T>, FlatExpression<T>> {
        match self.constants.get(&e.id) {
            Some(c) => IdentifierOrExpression::Expression(FlatExpression::number(c.clone())),
            None => IdentifierOrExpression::Identifier(e),
        }
    }

    fn fold_expression(&mut self, e: FlatExpression<T>) -> FlatExpression<T> {
        match e {
            FlatExpression::Number(n) => FlatExpression::Number(n),
            FlatExpression::Add(e) => match (
                self.fold_expression(*e.left),
                self.fold_expression(*e.right),
            ) {
                (FlatExpression::Number(n1), FlatExpression::Number(n2)) => {
                    FlatExpression::number(n1.value + n2.value)
                }
                (e1, e2) => FlatExpression::add(e1, e2),
            }
            .span(e.span),
            FlatExpression::Sub(e) => match (
                self.fold_expression(*e.left),
                self.fold_expression(*e.right),
            ) {
                (FlatExpression::Number(n1), FlatExpression::Number(n2)) => {
                    FlatExpression::number(n1.value - n2.value)
                }
                (e1, e2) => FlatExpression::sub(e1, e2),
            }
            .span(e.span),
            FlatExpression::Mult(e) => match (
                self.fold_expression(*e.left),
                self.fold_expression(*e.right),
            ) {
                (FlatExpression::Number(n1), FlatExpression::Number(n2)) => {
                    FlatExpression::number(n1.value * n2.value)
                }
                (e1, e2) => FlatExpression::mul(e1, e2),
            }
            .span(e.span),
            e => fold_expression(self, e),
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
