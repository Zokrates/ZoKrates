//! Module containing the `RedefinitionOptimizer` to optimize a flattened program.

use field::Field;
use flat_absy::flat_variable::FlatVariable;
use flat_absy::folder::{fold_parameter, fold_statement};
use flat_absy::*;
use std::collections::HashMap;

pub struct RedefinitionOptimizer {
    /// Map of renamings for reassigned variables while processing the program.
    substitution: HashMap<FlatVariable, FlatVariable>,
    /// Index of the next introduced variable while processing the program.
    next_var_idx: Counter,
}

impl RedefinitionOptimizer {
    fn new() -> RedefinitionOptimizer {
        RedefinitionOptimizer {
            substitution: HashMap::new(),
            next_var_idx: Counter { value: 0 },
        }
    }

    pub fn optimize<T: Field>(p: FlatProg<T>) -> FlatProg<T> {
        RedefinitionOptimizer::new().fold_program(p)
    }
}

pub struct Counter {
    value: usize,
}

impl Counter {
    fn increment(&mut self) -> usize {
        let index = self.value;
        self.value = self.value + 1;
        index
    }
}

impl<T: Field> Folder<T> for RedefinitionOptimizer {
    fn fold_statement(&mut self, s: FlatStatement<T>) -> Vec<FlatStatement<T>> {
        // generate substitution map
        //
        //  (b = a, c = b) => ( b -> a, c -> a )
        // The first variable to appear is used for its synonyms.
        match s {
            // Synonym definition
            // if the right side of the assignment is already being reassigned to `x`,
            // reassign the left side to `x` as well, otherwise reassign to a new variable
            FlatStatement::Definition(ref left, FlatExpression::Identifier(ref right)) => {
                // a = b
                // if
                let r = match self.substitution.get(right) {
                    Some(value) => value.clone(),
                    None => unreachable!(), // the right hand side must have been reassigned before
                };
                self.substitution.insert(left.clone(), r);
                // remove this statement
                vec![]
            }
            // Other definitions
            FlatStatement::Definition(left, _) => {
                // here the rhs is an expression we haven't seen before, so allocate a new variable
                self.substitution.insert(
                    left.clone(),
                    FlatVariable::new(self.next_var_idx.increment()),
                );
                fold_statement(self, s)
            }
            FlatStatement::Directive(d) => {
                for o in d.outputs.iter() {
                    self.substitution
                        .insert(o.clone(), FlatVariable::new(self.next_var_idx.increment()));
                }
                fold_statement(self, FlatStatement::Directive(d))
            }
            _ => fold_statement(self, s),
        }
    }

    fn fold_variable(&mut self, v: FlatVariable) -> FlatVariable {
        *self.substitution.get(&v).unwrap()
    }

    fn fold_parameter(&mut self, p: FlatParameter) -> FlatParameter {
        // each parameter is a new variable
        let optimized_variable = FlatVariable::new(self.next_var_idx.increment());
        self.substitution.insert(p.id, optimized_variable);
        fold_parameter::<T, _>(self, p)
    }

    fn fold_function(&mut self, funct: FlatFunction<T>) -> FlatFunction<T> {
        let optimized_arguments = funct
            .arguments
            .into_iter()
            .map(|a| <RedefinitionOptimizer as Folder<T>>::fold_parameter(self, a))
            .collect();
        let optimized_statements: Vec<_> = funct
            .statements
            .into_iter()
            .flat_map(|s| self.fold_statement(s))
            .collect();

        FlatFunction {
            arguments: optimized_arguments,
            statements: optimized_statements,
            ..funct
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use field::FieldPrime;
    use flat_absy::flat_parameter::FlatParameter;
    use types::{Signature, Type};

    #[test]
    fn remove_synonyms() {
        // def main(x):
        //    y = x
        //    z = y
        //    return z

        let x = FlatVariable::new(0);
        let y = FlatVariable::new(1);
        let z = FlatVariable::new(2);

        let f: FlatFunction<FieldPrime> = FlatFunction {
            id: "foo".to_string(),
            arguments: vec![FlatParameter {
                id: x,
                private: false,
            }],
            statements: vec![
                FlatStatement::Definition(y, FlatExpression::Identifier(x)),
                FlatStatement::Definition(z, FlatExpression::Identifier(y)),
                FlatStatement::Return(FlatExpressionList {
                    expressions: vec![FlatExpression::Identifier(z)],
                }),
            ],
            signature: Signature {
                inputs: vec![Type::FieldElement],
                outputs: vec![Type::FieldElement],
            },
        };

        let optimized: FlatFunction<FieldPrime> = FlatFunction {
            id: "foo".to_string(),
            arguments: vec![FlatParameter {
                id: x,
                private: false,
            }],
            statements: vec![FlatStatement::Return(FlatExpressionList {
                expressions: vec![FlatExpression::Identifier(x)],
            })],
            signature: Signature {
                inputs: vec![Type::FieldElement],
                outputs: vec![Type::FieldElement],
            },
        };

        let mut optimizer = RedefinitionOptimizer::new();
        assert_eq!(optimizer.fold_function(f), optimized);
    }

    #[test]
    fn remove_synonyms_in_condition() {
        // def main(x):
        //    y = x
        //    z = y
        //    z == y
        //    return z

        let x = FlatVariable::new(0);
        let y = FlatVariable::new(1);
        let z = FlatVariable::new(2);

        let f: FlatFunction<FieldPrime> = FlatFunction {
            id: "foo".to_string(),
            arguments: vec![FlatParameter {
                id: x,
                private: false,
            }],
            statements: vec![
                FlatStatement::Definition(y, FlatExpression::Identifier(x)),
                FlatStatement::Definition(z, FlatExpression::Identifier(y)),
                FlatStatement::Condition(
                    FlatExpression::Identifier(z),
                    FlatExpression::Identifier(y),
                ),
                FlatStatement::Return(FlatExpressionList {
                    expressions: vec![FlatExpression::Identifier(z)],
                }),
            ],
            signature: Signature {
                inputs: vec![Type::FieldElement],
                outputs: vec![Type::FieldElement],
            },
        };

        let optimized: FlatFunction<FieldPrime> = FlatFunction {
            id: "foo".to_string(),
            arguments: vec![FlatParameter {
                id: x,
                private: false,
            }],
            statements: vec![
                FlatStatement::Condition(
                    FlatExpression::Identifier(x),
                    FlatExpression::Identifier(x),
                ),
                FlatStatement::Return(FlatExpressionList {
                    expressions: vec![FlatExpression::Identifier(x)],
                }),
            ],
            signature: Signature {
                inputs: vec![Type::FieldElement],
                outputs: vec![Type::FieldElement],
            },
        };

        let mut optimizer = RedefinitionOptimizer::new();
        assert_eq!(optimizer.fold_function(f), optimized);
    }

    #[test]
    fn remove_multiple_synonyms() {
        // def main(x):
        //    y = x
        //    t = 1
        //    z = y
        //    w = t
        //    return z, w

        let x = FlatVariable::new(0);
        let y = FlatVariable::new(1);
        let z = FlatVariable::new(2);
        let t = FlatVariable::new(3);
        let w = FlatVariable::new(4);

        let f: FlatFunction<FieldPrime> = FlatFunction {
            id: "foo".to_string(),
            arguments: vec![FlatParameter {
                id: x,
                private: false,
            }],
            statements: vec![
                FlatStatement::Definition(y, FlatExpression::Identifier(x)),
                FlatStatement::Definition(t, FlatExpression::Number(FieldPrime::from(1))),
                FlatStatement::Definition(z, FlatExpression::Identifier(y)),
                FlatStatement::Definition(w, FlatExpression::Identifier(t)),
                FlatStatement::Return(FlatExpressionList {
                    expressions: vec![FlatExpression::Identifier(z), FlatExpression::Identifier(w)],
                }),
            ],
            signature: Signature {
                inputs: vec![Type::FieldElement],
                outputs: vec![Type::FieldElement, Type::FieldElement],
            },
        };

        let optimized: FlatFunction<FieldPrime> = FlatFunction {
            id: "foo".to_string(),
            arguments: vec![FlatParameter {
                id: x,
                private: false,
            }],
            statements: vec![
                FlatStatement::Definition(y, FlatExpression::Number(FieldPrime::from(1))),
                FlatStatement::Return(FlatExpressionList {
                    expressions: vec![FlatExpression::Identifier(x), FlatExpression::Identifier(y)],
                }),
            ],
            signature: Signature {
                inputs: vec![Type::FieldElement],
                outputs: vec![Type::FieldElement, Type::FieldElement],
            },
        };

        let mut optimizer = RedefinitionOptimizer::new();
        assert_eq!(optimizer.fold_function(f), optimized);
    }
}
