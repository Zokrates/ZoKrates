use flat_absy::{FlatExpression, FlatFunction, FlatProg, FlatStatement, FlatVariable};
use helpers;
use ir::variable::Variable;
use ir::{DirectiveStatement, Function, LinComb, Prog, QuadComb, Statement};
use num::Zero;
use zokrates_field::field::Field;

impl From<FlatVariable> for Variable {
    fn from(fv: FlatVariable) -> Variable {
        Variable::Private(fv.id())
    }
}

impl<T: Field> From<FlatFunction<T>> for Function<T> {
    fn from(flat_function: FlatFunction<T>) -> Function<T> {
        let return_expressions: Vec<FlatExpression<T>> = flat_function
            .statements
            .iter()
            .filter_map(|s| match s {
                FlatStatement::Return(el) => Some(el.expressions.clone()),
                _ => None,
            })
            .next()
            .unwrap();
        Function {
            id: flat_function.id,
            arguments: flat_function
                .arguments
                .into_iter()
                .map(|p| p.id.into())
                .collect(),
            returns: return_expressions.into_iter().map(|e| e.into()).collect(),
            statements: flat_function
                .statements
                .into_iter()
                .filter_map(|s| match s {
                    FlatStatement::Return(..) => None,
                    s => Some(s.into()),
                })
                .collect(),
        }
    }
}

impl<T: Field> From<FlatProg<T>> for Prog<T> {
    fn from(flat_prog: FlatProg<T>) -> Prog<T> {
        // get the main function as all calls have been resolved
        let main = flat_prog
            .functions
            .into_iter()
            .find(|f| f.id == "main")
            .unwrap();

        // create the new arguments list by putting public variables where needed
        let arguments: Vec<Variable> = main
            .arguments
            .iter()
            .scan(0, |state, p| {
                if p.private {
                    Some(p.id.into())
                } else {
                    let res = Variable::Public(*state);
                    *state = *state + 1;
                    Some(res)
                }
            })
            .collect();

        // redefine the removed private variables inside the circuit based on the public ones
        let public_binding_statements: Vec<Statement<T>> = main
            .arguments
            .iter()
            .scan(0, |state, p| {
                if p.private {
                    None
                } else {
                    let res = Statement::Constraint(
                        Variable::Public(*state).into(),
                        Variable::from(p.id).into(),
                    );
                    *state = *state + 1;
                    Some(res)
                }
            })
            .collect();

        // convert the main function to this IR for functions
        let main: Function<T> = main.into();

        // contrary to other functions, we need to make sure that return values are identifiers, so we define new (public) variables
        let definitions = main
            .returns
            .iter()
            .enumerate()
            .map(|(index, e)| Statement::Constraint(e.clone(), Variable::Output(index).into()));

        // update the main function with the extra definition statements and replace the return values
        let main = Function {
            returns: (0..main.returns.len())
                .map(|i| Variable::Output(i).into())
                .collect(),
            statements: public_binding_statements
                .into_iter()
                .chain(main.statements.into_iter())
                .chain(definitions)
                .collect(),
            arguments,
            ..main
        };

        let main = Function::from(main);
        Prog { main }
    }
}

impl<T: Field> From<FlatExpression<T>> for QuadComb<T> {
    fn from(flat_expression: FlatExpression<T>) -> QuadComb<T> {
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

impl<T: Field> From<FlatExpression<T>> for LinComb<T> {
    fn from(flat_expression: FlatExpression<T>) -> LinComb<T> {
        assert!(flat_expression.is_linear());
        match flat_expression {
            FlatExpression::Number(ref n) if *n == T::from(0) => LinComb::zero(),
            FlatExpression::Number(n) => LinComb::summand(n, Variable::One),
            FlatExpression::Identifier(id) => LinComb::from(Variable::from(id)),
            FlatExpression::Add(box e1, box e2) => LinComb::from(e1) + LinComb::from(e2),
            FlatExpression::Sub(box e1, box e2) => LinComb::from(e1) - LinComb::from(e2),
            FlatExpression::Mult(
                box FlatExpression::Number(n1),
                box FlatExpression::Identifier(v1),
            )
            | FlatExpression::Mult(
                box FlatExpression::Identifier(v1),
                box FlatExpression::Number(n1),
            ) => LinComb::summand(n1, v1.into()),
            e => unimplemented!("{}", e),
        }
    }
}

impl<T: Field> From<FlatStatement<T>> for Statement<T> {
    fn from(flat_statement: FlatStatement<T>) -> Statement<T> {
        match flat_statement {
            FlatStatement::Condition(linear, quadratic) => match quadratic {
                FlatExpression::Mult(box lhs, box rhs) => Statement::Constraint(
                    QuadComb::from_linear_combinations(lhs.into(), rhs.into()),
                    linear.into(),
                ),
                e => Statement::Constraint(LinComb::from(e).into(), linear.into()),
            },
            FlatStatement::Definition(var, quadratic) => match quadratic {
                FlatExpression::Mult(box lhs, box rhs) => Statement::Constraint(
                    QuadComb::from_linear_combinations(lhs.into(), rhs.into()),
                    Variable::from(var).into(),
                ),
                e => Statement::Constraint(LinComb::from(e).into(), Variable::from(var).into()),
            },
            FlatStatement::Directive(ds) => Statement::Directive(ds.into()),
            _ => panic!("return should be handled at the function level"),
        }
    }
}

impl<T: Field> From<helpers::DirectiveStatement<T>> for DirectiveStatement<T> {
    fn from(ds: helpers::DirectiveStatement<T>) -> DirectiveStatement<T> {
        DirectiveStatement {
            inputs: ds.inputs.into_iter().map(|i| i.into()).collect(),
            helper: ds.helper,
            outputs: ds.outputs.into_iter().map(|x| x.into()).collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn zero() {
        // 0
        let zero = FlatExpression::Number(FieldPrime::from(0));
        let expected: LinComb<FieldPrime> = LinComb::zero();
        assert_eq!(LinComb::from(zero), expected);
    }

    #[test]
    fn one() {
        // 1
        let one = FlatExpression::Number(FieldPrime::from(1));
        let expected: LinComb<FieldPrime> = Variable::One.into();
        assert_eq!(LinComb::from(one), expected);
    }

    #[test]
    fn forty_two() {
        // 42
        let one = FlatExpression::Number(FieldPrime::from(42));
        let expected: LinComb<FieldPrime> = LinComb::summand(42, Variable::One);
        assert_eq!(LinComb::from(one), expected);
    }

    #[test]
    fn add() {
        // x + y
        let add = FlatExpression::Add(
            box FlatExpression::Identifier(FlatVariable::new(42)),
            box FlatExpression::Identifier(FlatVariable::new(21)),
        );
        let expected: LinComb<FieldPrime> =
            LinComb::summand(1, Variable::Private(42)) + LinComb::summand(1, Variable::Private(21));
        assert_eq!(LinComb::from(add), expected);
    }

    #[test]
    fn linear_combination() {
        // 42*x + 21*y
        let add = FlatExpression::Add(
            box FlatExpression::Mult(
                box FlatExpression::Number(FieldPrime::from(42)),
                box FlatExpression::Identifier(FlatVariable::new(42)),
            ),
            box FlatExpression::Mult(
                box FlatExpression::Number(FieldPrime::from(21)),
                box FlatExpression::Identifier(FlatVariable::new(21)),
            ),
        );
        let expected: LinComb<FieldPrime> = LinComb::summand(42, Variable::Private(42))
            + LinComb::summand(21, Variable::Private(21));
        assert_eq!(LinComb::from(add), expected);
    }

    #[test]
    fn linear_combination_inverted() {
        // x*42 + y*21
        let add = FlatExpression::Add(
            box FlatExpression::Mult(
                box FlatExpression::Identifier(FlatVariable::new(42)),
                box FlatExpression::Number(FieldPrime::from(42)),
            ),
            box FlatExpression::Mult(
                box FlatExpression::Identifier(FlatVariable::new(21)),
                box FlatExpression::Number(FieldPrime::from(21)),
            ),
        );
        let expected: LinComb<FieldPrime> = LinComb::summand(42, Variable::Private(42))
            + LinComb::summand(21, Variable::Private(21));
        assert_eq!(LinComb::from(add), expected);
    }
}
