use crate::flat_absy::{
    DirectiveStatement, FlatExpression, FlatFunction, FlatProg, FlatStatement, FlatVariable,
};
use num::Zero;
use zokrates_field::field::Field;
use zokrates_ir::{Directive, Function, LinComb, Prog, QuadComb, Statement};

impl<T: Field> FlatFunction<T> {
    fn into_ir(self) -> Function<T> {
        let return_expressions: Vec<FlatExpression<T>> = self
            .statements
            .iter()
            .filter_map(|s| match s {
                FlatStatement::Return(el) => Some(el.expressions.clone()),
                _ => None,
            })
            .next()
            .unwrap();
        Function {
            id: String::from("main"),
            arguments: self.arguments.into_iter().map(|p| p.id).collect(),
            returns: return_expressions
                .iter()
                .enumerate()
                .map(|(index, _)| FlatVariable::public(index))
                .collect(),
            statements: self
                .statements
                .into_iter()
                .filter_map(|s| match s {
                    FlatStatement::Return(..) => None,
                    s => Some(s.into_ir()),
                })
                .chain(
                    return_expressions
                        .into_iter()
                        .enumerate()
                        .map(|(index, expression)| {
                            Statement::Constraint(
                                expression.into_ir_quad(),
                                FlatVariable::public(index).into(),
                            )
                        }),
                )
                .collect(),
        }
    }
}

impl<T: Field> FlatProg<T> {
    pub fn into_ir(self) -> Prog<T> {
        // get the main function
        let main = self.main;

        // get the interface of the program, ie which inputs are private and public
        let private = main.arguments.iter().map(|p| p.private).collect();

        let main = main.into_ir();

        Prog { private, main }
    }
}

impl<T: Field> FlatExpression<T> {
    fn into_ir_lin(self) -> LinComb<T> {
        match self {
            FlatExpression::Number(ref n) if *n == T::from(0) => LinComb::zero(),
            FlatExpression::Number(n) => LinComb::summand(n, FlatVariable::one()),
            FlatExpression::Identifier(id) => LinComb::from(id),
            FlatExpression::Add(box e1, box e2) => e1.into_ir_lin() + e2.into_ir_lin(),
            FlatExpression::Sub(box e1, box e2) => e1.into_ir_lin() - e2.into_ir_lin(),
            FlatExpression::Mult(
                box FlatExpression::Number(n1),
                box FlatExpression::Identifier(v1),
            )
            | FlatExpression::Mult(
                box FlatExpression::Identifier(v1),
                box FlatExpression::Number(n1),
            ) => LinComb::summand(n1, v1),
            e => unimplemented!("{}", e),
        }
    }

    fn into_ir_quad(self) -> QuadComb<T> {
        match self.is_linear() {
            true => self.into_ir_lin().into(),
            false => match self {
                FlatExpression::Mult(box e1, box e2) => {
                    QuadComb::from_linear_combinations(e1.into_ir_lin(), e2.into_ir_lin())
                }
                e => unimplemented!("{}", e),
            },
        }
    }
}

impl<T: Field> FlatStatement<T> {
    fn into_ir(self) -> Statement<T> {
        match self {
            FlatStatement::Condition(linear, quadratic) => match quadratic {
                FlatExpression::Mult(box lhs, box rhs) => Statement::Constraint(
                    QuadComb::from_linear_combinations(lhs.into_ir_lin(), rhs.into_ir_lin()),
                    linear.into_ir_lin(),
                ),
                e => Statement::Constraint(e.into_ir_lin().into(), linear.into_ir_lin()),
            },
            FlatStatement::Definition(var, quadratic) => match quadratic {
                FlatExpression::Mult(box lhs, box rhs) => Statement::Constraint(
                    QuadComb::from_linear_combinations(lhs.into_ir_lin(), rhs.into_ir_lin()),
                    var.into(),
                ),
                e => Statement::Constraint(e.into_ir_lin().into(), var.into()),
            },
            FlatStatement::Directive(ds) => Statement::Directive(ds.into_ir()),
            _ => panic!("return should be handled at the function level"),
        }
    }
}

impl<T: Field> DirectiveStatement<T> {
    fn into_ir(self) -> Directive<T> {
        Directive {
            inputs: self.inputs.into_iter().map(|i| i.into_ir_lin()).collect(),
            helper: self.helper,
            outputs: self.outputs,
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
        let expected: LinComb<FieldPrime> = FlatVariable::one().into();
        assert_eq!(LinComb::from(one), expected);
    }

    #[test]
    fn forty_two() {
        // 42
        let one = FlatExpression::Number(FieldPrime::from(42));
        let expected: LinComb<FieldPrime> = LinComb::summand(42, FlatVariable::one());
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
            LinComb::summand(1, FlatVariable::new(42)) + LinComb::summand(1, FlatVariable::new(21));
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
        let expected: LinComb<FieldPrime> = LinComb::summand(42, FlatVariable::new(42))
            + LinComb::summand(21, FlatVariable::new(21));
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
        let expected: LinComb<FieldPrime> = LinComb::summand(42, FlatVariable::new(42))
            + LinComb::summand(21, FlatVariable::new(21));
        assert_eq!(LinComb::from(add), expected);
    }
}
