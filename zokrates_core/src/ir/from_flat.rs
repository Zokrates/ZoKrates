use crate::ast::IntoStatements;
use crate::flat_absy::{
    FlatAbsy, FlatDirective, FlatExpression, FlatProgIterator, FlatStatement, FlatVariable,
};
use crate::ir::{Directive, Ir, LinComb, ProgIterator, QuadComb, Statement};
use zokrates_field::Field;

impl<T: Field> QuadComb<T> {
    fn from_flat_expression<U: Into<FlatExpression<T>>>(flat_expression: U) -> QuadComb<T> {
        let flat_expression = flat_expression.into();
        match flat_expression.is_linear() {
            true => LinComb::from(flat_expression).into(),
            false => match flat_expression {
                FlatExpression::Mult(box e1, box e2) => {
                    QuadComb::from_linear_combinations(e1.into(), e2.into())
                }
                e => unimplemented!("{}", e),
            },
        }
    }
}

pub fn from_flat<T: Field, I: IntoStatements<FlatAbsy<T>>>(
    flat_prog_iterator: FlatProgIterator<I>,
) -> ProgIterator<T, impl IntoStatements<Ir<T>>> {
    use fallible_iterator::FallibleIterator;

    ProgIterator::new(
        flat_prog_iterator.arguments,
        flat_prog_iterator
            .statements
            .into_fallible_iter()
            .map(|s| Ok(Statement::from(s))),
        flat_prog_iterator.return_count,
    )
}

impl<T: Field> From<FlatExpression<T>> for LinComb<T> {
    fn from(flat_expression: FlatExpression<T>) -> LinComb<T> {
        match flat_expression {
            FlatExpression::Number(ref n) if *n == T::from(0) => LinComb::zero(),
            FlatExpression::Number(n) => LinComb::summand(n, FlatVariable::one()),
            FlatExpression::Identifier(id) => LinComb::from(id),
            FlatExpression::Add(box e1, box e2) => LinComb::from(e1) + LinComb::from(e2),
            FlatExpression::Sub(box e1, box e2) => LinComb::from(e1) - LinComb::from(e2),
            FlatExpression::Mult(
                box FlatExpression::Number(n1),
                box FlatExpression::Identifier(v1),
            )
            | FlatExpression::Mult(
                box FlatExpression::Identifier(v1),
                box FlatExpression::Number(n1),
            ) => LinComb::summand(n1, v1),
            FlatExpression::Mult(
                box FlatExpression::Number(n1),
                box FlatExpression::Number(n2),
            ) => LinComb::summand(n1 * n2, FlatVariable::one()),
            e => unreachable!("{}", e),
        }
    }
}

impl<T: Field> From<FlatStatement<T>> for Statement<T> {
    fn from(flat_statement: FlatStatement<T>) -> Statement<T> {
        match flat_statement {
            FlatStatement::Condition(linear, quadratic, message) => match quadratic {
                FlatExpression::Mult(box lhs, box rhs) => Statement::Constraint(
                    QuadComb::from_linear_combinations(lhs.into(), rhs.into()),
                    linear.into(),
                    Some(message),
                ),
                e => Statement::Constraint(LinComb::from(e).into(), linear.into(), Some(message)),
            },
            FlatStatement::Definition(var, quadratic) => match quadratic {
                FlatExpression::Mult(box lhs, box rhs) => Statement::Constraint(
                    QuadComb::from_linear_combinations(lhs.into(), rhs.into()),
                    var.into(),
                    None,
                ),
                e => Statement::Constraint(LinComb::from(e).into(), var.into(), None),
            },
            FlatStatement::Directive(ds) => Statement::Directive(ds.into()),
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
        let expected: LinComb<Bn128Field> = FlatVariable::one().into();
        assert_eq!(LinComb::from(one), expected);
    }

    #[test]
    fn forty_two() {
        // 42
        let one = FlatExpression::Number(Bn128Field::from(42));
        let expected: LinComb<Bn128Field> = LinComb::summand(42, FlatVariable::one());
        assert_eq!(LinComb::from(one), expected);
    }

    #[test]
    fn add() {
        // x + y
        let add = FlatExpression::Add(
            box FlatExpression::Identifier(FlatVariable::new(42)),
            box FlatExpression::Identifier(FlatVariable::new(21)),
        );
        let expected: LinComb<Bn128Field> =
            LinComb::summand(1, FlatVariable::new(42)) + LinComb::summand(1, FlatVariable::new(21));
        assert_eq!(LinComb::from(add), expected);
    }

    #[test]
    fn linear_combination() {
        // 42*x + 21*y
        let add = FlatExpression::Add(
            box FlatExpression::Mult(
                box FlatExpression::Number(Bn128Field::from(42)),
                box FlatExpression::Identifier(FlatVariable::new(42)),
            ),
            box FlatExpression::Mult(
                box FlatExpression::Number(Bn128Field::from(21)),
                box FlatExpression::Identifier(FlatVariable::new(21)),
            ),
        );
        let expected: LinComb<Bn128Field> = LinComb::summand(42, FlatVariable::new(42))
            + LinComb::summand(21, FlatVariable::new(21));
        assert_eq!(LinComb::from(add), expected);
    }

    #[test]
    fn linear_combination_inverted() {
        // x*42 + y*21
        let add = FlatExpression::Add(
            box FlatExpression::Mult(
                box FlatExpression::Identifier(FlatVariable::new(42)),
                box FlatExpression::Number(Bn128Field::from(42)),
            ),
            box FlatExpression::Mult(
                box FlatExpression::Identifier(FlatVariable::new(21)),
                box FlatExpression::Number(Bn128Field::from(21)),
            ),
        );
        let expected: LinComb<Bn128Field> = LinComb::summand(42, FlatVariable::new(42))
            + LinComb::summand(21, FlatVariable::new(21));
        assert_eq!(LinComb::from(add), expected);
    }
}
