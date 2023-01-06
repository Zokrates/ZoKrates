use crate::common::WithSpan;
use crate::flat::{FlatDirective, FlatExpression, FlatProgIterator, FlatStatement, Variable};
use crate::ir::{Directive, LinComb, ProgIterator, QuadComb, Statement};
use std::ops::*;
use zokrates_field::Field;

impl<T: Field> QuadComb<T> {
    fn from_flat_expression<U: Into<FlatExpression<T>>>(flat_expression: U) -> QuadComb<T> {
        let flat_expression = flat_expression.into();
        match flat_expression.is_linear() {
            true => LinComb::from(flat_expression).into(),
            false => match flat_expression {
                FlatExpression::Mult(e) => QuadComb::new((*e.left).into(), (*e.right).into()),
                e => unimplemented!("{}", e),
            },
        }
    }
}

pub fn from_flat<T: Field, I: IntoIterator<Item = FlatStatement<T>>>(
    flat_prog_iterator: FlatProgIterator<T, I>,
) -> ProgIterator<T, impl IntoIterator<Item = Statement<T>>> {
    ProgIterator {
        statements: flat_prog_iterator.statements.into_iter().map(Into::into),
        arguments: flat_prog_iterator.arguments,
        return_count: flat_prog_iterator.return_count,
    }
}

impl<T: Field> From<FlatExpression<T>> for LinComb<T> {
    fn from(flat_expression: FlatExpression<T>) -> LinComb<T> {
        let span = flat_expression.get_span();

        match flat_expression {
            FlatExpression::Number(ref n) if n.value == T::from(0) => LinComb::zero(),
            FlatExpression::Number(n) => LinComb::summand(n.value, Variable::one()),
            FlatExpression::Identifier(id) => LinComb::from(id.id),
            FlatExpression::Add(e) => LinComb::from(*e.left) + LinComb::from(*e.right),
            FlatExpression::Sub(e) => LinComb::from(*e.left) - LinComb::from(*e.right),
            FlatExpression::Mult(e) => match (*e.left, *e.right) {
                (FlatExpression::Number(n1), FlatExpression::Identifier(v1))
                | (FlatExpression::Identifier(v1), FlatExpression::Number(n1)) => {
                    LinComb::summand(n1.value, v1.id)
                }
                (FlatExpression::Number(n1), FlatExpression::Number(n2)) => {
                    LinComb::summand(n1.value * n2.value, Variable::one())
                }
                (left, right) => unreachable!("{}", FlatExpression::mul(left, right).span(e.span)),
            },
        }
        .span(span)
    }
}

impl<T: Field> From<FlatStatement<T>> for Statement<T> {
    fn from(flat_statement: FlatStatement<T>) -> Statement<T> {
        match flat_statement {
            FlatStatement::Condition(s) => match s.expression {
                FlatExpression::Sub(e) => {
                    let quadratic = *e.right;
                    let linear = *e.left;
                    match quadratic {
                        FlatExpression::Mult(e) => Statement::Constraint(
                            QuadComb::new((*e.left).into(), (*e.right).into()).span(e.span),
                            LinComb::from(linear),
                            Some(s.error),
                        ),
                        e => Statement::Constraint(
                            LinComb::from(e).into(),
                            linear.into(),
                            Some(s.error),
                        ),
                    }
                }
                _ => unreachable!(),
            },
            FlatStatement::Definition(s) => match s.rhs {
                FlatExpression::Mult(e) => Statement::Constraint(
                    QuadComb::new((*e.left).into(), (*e.right).into()).span(e.span),
                    s.assignee.into(),
                    None,
                ),
                e => Statement::Constraint(LinComb::from(e).into(), s.assignee.into(), None),
            },
            FlatStatement::Directive(ds) => Statement::Directive(ds.into()),
            FlatStatement::Log(l, expressions) => Statement::Log(
                l,
                expressions
                    .into_iter()
                    .map(|(t, e)| (t, e.into_iter().map(LinComb::from).collect()))
                    .collect(),
            ),
        }
    }
}

impl<T: Field> From<FlatDirective<T>> for Directive<T> {
    fn from(ds: FlatDirective<T>) -> Directive<T> {
        Directive {
            inputs: ds
                .inputs
                .into_iter()
                .map(QuadComb::from_flat_expression)
                .collect(),
            solver: ds.solver,
            outputs: ds.outputs,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::Bn128Field;

    #[test]
    fn zero() {
        // 0
        let zero = FlatExpression::Number(Bn128Field::from(0));
        let expected: LinComb<Bn128Field> = LinComb::zero();
        assert_eq!(LinComb::from(zero), expected);
    }

    #[test]
    fn one() {
        // 1
        let one = FlatExpression::Number(Bn128Field::from(1));
        let expected: LinComb<Bn128Field> = Variable::one().into();
        assert_eq!(LinComb::from(one), expected);
    }

    #[test]
    fn forty_two() {
        // 42
        let one = FlatExpression::Number(Bn128Field::from(42));
        let expected: LinComb<Bn128Field> = LinComb::summand(42, Variable::one());
        assert_eq!(LinComb::from(one), expected);
    }

    #[test]
    fn add() {
        // x + y
        let add = FlatExpression::Add(
            box FlatExpression::Identifier(Variable::new(42)),
            box FlatExpression::Identifier(Variable::new(21)),
        );
        let expected: LinComb<Bn128Field> =
            LinComb::summand(1, Variable::new(42)) + LinComb::summand(1, Variable::new(21));
        assert_eq!(LinComb::from(add), expected);
    }

    #[test]
    fn linear_combination() {
        // 42*x + 21*y
        let add = FlatExpression::Add(
            box FlatExpression::Mult(
                box FlatExpression::Number(Bn128Field::from(42)),
                box FlatExpression::Identifier(Variable::new(42)),
            ),
            box FlatExpression::Mult(
                box FlatExpression::Number(Bn128Field::from(21)),
                box FlatExpression::Identifier(Variable::new(21)),
            ),
        );
        let expected: LinComb<Bn128Field> =
            LinComb::summand(42, Variable::new(42)) + LinComb::summand(21, Variable::new(21));
        assert_eq!(LinComb::from(add), expected);
    }

    #[test]
    fn linear_combination_inverted() {
        // x*42 + y*21
        let add = FlatExpression::Add(
            box FlatExpression::Mult(
                box FlatExpression::Identifier(Variable::new(42)),
                box FlatExpression::Number(Bn128Field::from(42)),
            ),
            box FlatExpression::Mult(
                box FlatExpression::Identifier(Variable::new(21)),
                box FlatExpression::Number(Bn128Field::from(21)),
            ),
        );
        let expected: LinComb<Bn128Field> =
            LinComb::summand(42, Variable::new(42)) + LinComb::summand(21, Variable::new(21));
        assert_eq!(LinComb::from(add), expected);
    }
}
