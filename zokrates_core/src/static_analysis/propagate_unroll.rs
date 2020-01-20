//! Module containing iterative unrolling in order to unroll nested loops with variable bounds
//!
//! For example:
//! ```zokrates
//! for field i in 0..5 do
//! 	for field j in i..5
//! 		//
//! 	endfor
//! enfor
//! ```
//!
//! We can unroll the outer loop, but to unroll the inner one we need to propagate the value of `i` to the lower bound of the loop
//!
//! This module does exactly that:
//! - unroll the outter loop, detecting that it cannot unroll the inner one as the lower `i` bound isn't constant
//! - apply constant propagation to the program, *not visiting statements of loops whose bounds are not constant yet*
//! - unroll again, this time the 5 inner loops all have constant bounds
//!
//! In the case that a loop bound cannot be reduced to a constant, we rely on a maximum number of passes after which we conclude that a bound is not constant
//! This sets a hard limit on the number of loops with variable bounds in the program
//!
//! @file propagation.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use static_analysis::propagation::Propagator;
use static_analysis::unroll::Unroller;
use typed_absy::TypedProgram;
use zokrates_field::field::Field;

pub struct PropagatedUnroller;

const MAX_DEPTH: usize = 100;

impl PropagatedUnroller {
    pub fn unroll<'ast, T: Field>(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        let mut p = p;
        let mut count = 0;

        // unroll a first time, retrieving whether the unroll is complete
        let unrolled = Unroller::unroll(p);
        let mut complete = unrolled.1;
        p = unrolled.0;

        loop {
            // conditions to exit the loop
            if complete {
                break;
            }
            if count > MAX_DEPTH {
                panic!("Loop unrolling failed. Most likely this happened because a loop bound is not constant")
            }

            // propagate
            p = Propagator::propagate_verbose(p);

            // unroll
            let unrolled = Unroller::unroll(p);
            complete = unrolled.1;
            p = unrolled.0;

            count = count + 1;
        }

        p
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use typed_absy::types::{FunctionKey, Signature};
    use typed_absy::*;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn for_loop() {
        //	for field i in 0..2
        //		for field j in i..2
        //			field foo = i + j

        // should be unrolled to
        // i_0 = 0
        // j_0 = 0
        // foo_0 = i_0 + j_0
        // j_1 = 1
        // foo_1 = i_0 + j_1
        // i_1 = 1
        // j_2 = 1
        // foo_2 = i_1 + j_2

        let s = TypedStatement::For(
            Variable::field_element("i".into()),
            FieldElementExpression::Number(FieldPrime::from(0)),
            FieldElementExpression::Number(FieldPrime::from(2)),
            vec![TypedStatement::For(
                Variable::field_element("j".into()),
                FieldElementExpression::Identifier("i".into()),
                FieldElementExpression::Number(FieldPrime::from(2)),
                vec![
                    TypedStatement::Declaration(Variable::field_element("foo".into())),
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_element("foo".into())),
                        FieldElementExpression::Add(
                            box FieldElementExpression::Identifier("i".into()),
                            box FieldElementExpression::Identifier("j".into()),
                        )
                        .into(),
                    ),
                ],
            )],
        );

        let expected_statements = vec![
            TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::field_element(
                    Identifier::from("i").version(0),
                )),
                FieldElementExpression::Number(FieldPrime::from(0)).into(),
            ),
            TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::field_element(
                    Identifier::from("j").version(0),
                )),
                FieldElementExpression::Number(FieldPrime::from(0)).into(),
            ),
            TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::field_element(
                    Identifier::from("foo").version(0),
                )),
                FieldElementExpression::Number(FieldPrime::from(0)).into(),
            ),
            TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::field_element(
                    Identifier::from("j").version(1),
                )),
                FieldElementExpression::Number(FieldPrime::from(1)).into(),
            ),
            TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::field_element(
                    Identifier::from("foo").version(1),
                )),
                FieldElementExpression::Number(FieldPrime::from(1)).into(),
            ),
            TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::field_element(
                    Identifier::from("i").version(1),
                )),
                FieldElementExpression::Number(FieldPrime::from(1)).into(),
            ),
            TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::field_element(
                    Identifier::from("j").version(2),
                )),
                FieldElementExpression::Number(FieldPrime::from(1)).into(),
            ),
            TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::field_element(
                    Identifier::from("foo").version(2),
                )),
                FieldElementExpression::Number(FieldPrime::from(2)).into(),
            ),
        ];

        let p = TypedProgram {
            modules: vec![(
                "main".to_string(),
                TypedModule {
                    functions: vec![(
                        FunctionKey::with_id("main"),
                        TypedFunctionSymbol::Here(TypedFunction {
                            arguments: vec![],
                            signature: Signature::new(),
                            statements: vec![s],
                        }),
                    )]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
            main: "main".to_string(),
        };

        let statements = match PropagatedUnroller::unroll(p).modules["main"].functions
            [&FunctionKey::with_id("main")]
            .clone()
        {
            TypedFunctionSymbol::Here(f) => f.statements,
            _ => unreachable!(),
        };

        assert_eq!(statements, expected_statements);
    }

}
