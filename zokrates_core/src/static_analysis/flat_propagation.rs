//! Module containing constant propagation for the flat AST
//!
//! @file propagation.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use crate::flat_absy::*;
use std::collections::HashMap;
use zokrates_field::Field;

pub trait Propagate<T: Field> {
    fn propagate(self) -> Self;
}

pub trait PropagateWithContext<T: Field> {
    fn propagate(self, constants: &mut HashMap<FlatVariable, T>) -> Self;
}

impl<T: Field> PropagateWithContext<T> for FlatExpression<T> {
    fn propagate(self, constants: &mut HashMap<FlatVariable, T>) -> FlatExpression<T> {
        match self {
            FlatExpression::Number(n) => FlatExpression::Number(n),
            FlatExpression::Identifier(id) => match constants.get(&id) {
                Some(c) => FlatExpression::Number(c.clone()),
                None => FlatExpression::Identifier(id),
            },
            FlatExpression::Add(box e1, box e2) => {
                match (e1.propagate(constants), e2.propagate(constants)) {
                    (FlatExpression::Number(n1), FlatExpression::Number(n2)) => {
                        FlatExpression::Number(n1 + n2)
                    }
                    (e1, e2) => FlatExpression::Add(box e1, box e2),
                }
            }
            FlatExpression::Sub(box e1, box e2) => {
                match (e1.propagate(constants), e2.propagate(constants)) {
                    (FlatExpression::Number(n1), FlatExpression::Number(n2)) => {
                        FlatExpression::Number(n1 - n2)
                    }
                    (e1, e2) => FlatExpression::Sub(box e1, box e2),
                }
            }
            FlatExpression::Mult(box e1, box e2) => {
                match (e1.propagate(constants), e2.propagate(constants)) {
                    (FlatExpression::Number(n1), FlatExpression::Number(n2)) => {
                        FlatExpression::Number(n1 * n2)
                    }
                    (e1, e2) => FlatExpression::Mult(box e1, box e2),
                }
            }
        }
    }
}

impl<T: Field> FlatStatement<T> {
    fn propagate(self, constants: &mut HashMap<FlatVariable, T>) -> Option<FlatStatement<T>> {
        match self {
            FlatStatement::Return(list) => Some(FlatStatement::Return(FlatExpressionList {
                expressions: list
                    .expressions
                    .into_iter()
                    .map(|e| e.propagate(constants))
                    .collect(),
            })),
            FlatStatement::Definition(var, expr) => match expr.propagate(constants) {
                FlatExpression::Number(n) => {
                    constants.insert(var, n);
                    None
                }
                e => Some(FlatStatement::Definition(var, e)),
            },
            FlatStatement::Condition(e1, e2) => Some(FlatStatement::Condition(
                e1.propagate(constants),
                e2.propagate(constants),
            )),
            FlatStatement::Directive(d) => Some(FlatStatement::Directive(FlatDirective {
                inputs: d
                    .inputs
                    .into_iter()
                    .map(|i| i.propagate(constants))
                    .collect(),
                ..d
            })),
        }
    }
}

impl<T: Field> Propagate<T> for FlatFunction<T> {
    fn propagate(self) -> FlatFunction<T> {
        let mut constants = HashMap::new();

        FlatFunction {
            statements: self
                .statements
                .into_iter()
                .filter_map(|s| s.propagate(&mut constants))
                .collect(),
            ..self
        }
    }
}

impl<T: Field> FlatProg<T> {
    pub fn propagate(self) -> FlatProg<T> {
        let main = self.main.propagate();

        FlatProg { main }
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
                let e = FlatExpression::Add(
                    box FlatExpression::Number(Bn128Field::from(2)),
                    box FlatExpression::Number(Bn128Field::from(3)),
                );

                assert_eq!(
                    e.propagate(&mut HashMap::new()),
                    FlatExpression::Number(Bn128Field::from(5))
                );
            }

            #[test]
            fn sub() {
                let e = FlatExpression::Sub(
                    box FlatExpression::Number(Bn128Field::from(3)),
                    box FlatExpression::Number(Bn128Field::from(2)),
                );

                assert_eq!(
                    e.propagate(&mut HashMap::new()),
                    FlatExpression::Number(Bn128Field::from(1))
                );
            }

            #[test]
            fn mult() {
                let e = FlatExpression::Mult(
                    box FlatExpression::Number(Bn128Field::from(3)),
                    box FlatExpression::Number(Bn128Field::from(2)),
                );

                assert_eq!(
                    e.propagate(&mut HashMap::new()),
                    FlatExpression::Number(Bn128Field::from(6))
                );
            }
        }
    }
}
