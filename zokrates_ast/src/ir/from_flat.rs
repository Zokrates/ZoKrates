use crate::common::statements::LogStatement;
use crate::common::WithSpan;
use crate::flat::{FlatDirective, FlatExpression, FlatProgIterator, FlatStatement, Variable};
use crate::ir::{DirectiveStatement, LinComb, ProgIterator, QuadComb, Statement};
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

pub fn from_flat<'ast, T: Field, I: IntoIterator<Item = FlatStatement<'ast, T>>>(
    flat_prog_iterator: FlatProgIterator<'ast, T, I>,
) -> ProgIterator<T, impl IntoIterator<Item = Statement<'ast, T>>> {
    ProgIterator {
        statements: flat_prog_iterator.statements.into_iter().map(Into::into),
        arguments: flat_prog_iterator.arguments,
        return_count: flat_prog_iterator.return_count,
        module_map: flat_prog_iterator.module_map,
        solvers: vec![],
    }
}

impl<T: Field> From<FlatExpression<T>> for LinComb<T> {
    fn from(flat_expression: FlatExpression<T>) -> LinComb<T> {
        let span = flat_expression.get_span();

        match flat_expression {
            FlatExpression::Value(ref n) if n.value == T::from(0) => LinComb::zero(),
            FlatExpression::Value(n) => LinComb::summand(n.value, Variable::one()),
            FlatExpression::Identifier(id) => LinComb::from(id.id),
            FlatExpression::Add(e) => LinComb::from(*e.left) + LinComb::from(*e.right),
            FlatExpression::Sub(e) => LinComb::from(*e.left) - LinComb::from(*e.right),
            FlatExpression::Mult(e) => match (*e.left, *e.right) {
                (FlatExpression::Value(n1), FlatExpression::Identifier(v1))
                | (FlatExpression::Identifier(v1), FlatExpression::Value(n1)) => {
                    LinComb::summand(n1.value, v1.id)
                }
                (FlatExpression::Value(n1), FlatExpression::Value(n2)) => {
                    LinComb::summand(n1.value * n2.value, Variable::one())
                }
                (left, right) => unreachable!("{}", FlatExpression::mul(left, right).span(e.span)),
            },
        }
        .span(span)
    }
}

impl<'ast, T: Field> From<FlatStatement<'ast, T>> for Statement<'ast, T> {
    fn from(flat_statement: FlatStatement<'ast, T>) -> Statement<'ast, T> {
        let span = flat_statement.get_span();

        match flat_statement {
            FlatStatement::Condition(s) => match s.quad {
                FlatExpression::Mult(e) => Statement::constraint(
                    QuadComb::new((*e.left).into(), (*e.right).into()).span(e.span),
                    LinComb::from(s.lin),
                    Some(s.error),
                ),
                e => Statement::constraint(LinComb::from(e), s.lin, Some(s.error)),
            },
            FlatStatement::Block(statements) => {
                Statement::block(statements.inner.into_iter().map(Statement::from).collect())
            }
            FlatStatement::Definition(s) => match s.rhs {
                FlatExpression::Mult(e) => Statement::constraint(
                    QuadComb::new((*e.left).into(), (*e.right).into()).span(e.span),
                    s.assignee,
                    None,
                ),
                e => Statement::constraint(LinComb::from(e), s.assignee, None),
            },
            FlatStatement::Directive(ds) => Statement::Directive(ds.into()),
            FlatStatement::Log(s) => Statement::Log(LogStatement::new(
                s.format_string,
                s.expressions
                    .into_iter()
                    .map(|(t, e)| (t, e.into_iter().map(LinComb::from).collect()))
                    .collect(),
            )),
        }
        .span(span)
    }
}

impl<'ast, T: Field> From<FlatDirective<'ast, T>> for DirectiveStatement<'ast, T> {
    fn from(ds: FlatDirective<T>) -> DirectiveStatement<T> {
        DirectiveStatement {
            inputs: ds
                .inputs
                .into_iter()
                .map(QuadComb::from_flat_expression)
                .collect(),
            solver: ds.solver,
            outputs: ds.outputs,
            span: ds.span,
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
        let zero = FlatExpression::value(Bn128Field::from(0));
        let expected: LinComb<Bn128Field> = LinComb::zero();
        assert_eq!(LinComb::from(zero), expected);
    }

    #[test]
    fn one() {
        // 1
        let one = FlatExpression::value(Bn128Field::from(1));
        let expected: LinComb<Bn128Field> = Variable::one().into();
        assert_eq!(LinComb::from(one), expected);
    }

    #[test]
    fn forty_two() {
        // 42
        let one = FlatExpression::value(Bn128Field::from(42));
        let expected: LinComb<Bn128Field> = LinComb::summand(42, Variable::one());
        assert_eq!(LinComb::from(one), expected);
    }

    #[test]
    fn add() {
        // x + y
        let add = FlatExpression::add(
            FlatExpression::identifier(Variable::new(42)),
            FlatExpression::identifier(Variable::new(21)),
        );
        let expected: LinComb<Bn128Field> =
            LinComb::summand(1, Variable::new(42)) + LinComb::summand(1, Variable::new(21));
        assert_eq!(LinComb::from(add), expected);
    }

    #[test]
    fn linear_combination() {
        // 42*x + 21*y
        let add = FlatExpression::add(
            FlatExpression::mul(
                FlatExpression::value(Bn128Field::from(42)),
                FlatExpression::identifier(Variable::new(42)),
            ),
            FlatExpression::mul(
                FlatExpression::value(Bn128Field::from(21)),
                FlatExpression::identifier(Variable::new(21)),
            ),
        );
        let expected: LinComb<Bn128Field> =
            LinComb::summand(42, Variable::new(42)) + LinComb::summand(21, Variable::new(21));
        assert_eq!(LinComb::from(add), expected);
    }

    #[test]
    fn linear_combination_inverted() {
        // x*42 + y*21
        let add = FlatExpression::add(
            FlatExpression::mul(
                FlatExpression::identifier(Variable::new(42)),
                FlatExpression::value(Bn128Field::from(42)),
            ),
            FlatExpression::mul(
                FlatExpression::identifier(Variable::new(21)),
                FlatExpression::value(Bn128Field::from(21)),
            ),
        );
        let expected: LinComb<Bn128Field> =
            LinComb::summand(42, Variable::new(42)) + LinComb::summand(21, Variable::new(21));
        assert_eq!(LinComb::from(add), expected);
    }
}
