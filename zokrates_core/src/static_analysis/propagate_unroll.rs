//! Module containing iterative unrolling in order to unroll nested loops with variable bounds
//!
//! For example:
//! ```zokrates
//! for field i in 0..5 do
//! 	for field j in i..5 do
//! 		//
//! 	endfor
//! endfor
//! ```
//!
//! We can unroll the outer loop, but to unroll the inner one we need to propagate the value of `i` to the lower bound of the loop
//!
//! This module does exactly that:
//! - unroll the outter loop, detecting that it cannot unroll the inner one as the lower `i` bound isn't constant
//! - apply constant propagation to the program, *not visiting statements of loops whose bounds are not constant yet*
//! - unroll again, this time the 5 inner loops all have constant bounds
//!
//! In the case that a loop bound cannot be reduced to a constant, we detect it by noticing that the unroll does
//! not make progress anymore.

use static_analysis::propagation::Propagator;
use static_analysis::unroll::{Output, Unroller};
use typed_absy::TypedProgram;
use zokrates_field::field::Field;

pub struct PropagatedUnroller;

impl PropagatedUnroller {
    pub fn unroll<'ast, T: Field>(
        p: TypedProgram<'ast, T>,
    ) -> Result<TypedProgram<'ast, T>, &'static str> {
        let mut blocked_at = None;

        // unroll a first time, retrieving whether the unroll is complete
        let mut unrolled = Unroller::unroll(p);

        loop {
            // conditions to exit the loop
            unrolled = match unrolled {
                Output::Complete(p) => return Ok(p),
                Output::Incomplete(next, index) => {
                    if Some(index) == blocked_at {
                        return Err("Loop unrolling failed. This happened because a loop bound is not constant");
                    } else {
                        // update the index where we blocked
                        blocked_at = Some(index);

                        // propagate
                        let propagated = Propagator::propagate_verbose(next);

                        // unroll
                        Unroller::unroll(propagated)
                    }
                }
            };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use typed_absy::types::{FunctionKey, Signature};
    use typed_absy::*;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn detect_non_constant_bound() {
        let loops = vec![TypedStatement::For(
            Variable::field_element("i".into()),
            FieldElementExpression::Identifier("i".into()),
            FieldElementExpression::Number(FieldPrime::from(2)),
            vec![],
        )];

        let statements = loops;

        let p = TypedProgram {
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![(
                        FunctionKey::with_id("main"),
                        TypedFunctionSymbol::Here(TypedFunction {
                            arguments: vec![],
                            signature: Signature::new(),
                            statements,
                        }),
                    )]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
            main: "main".into(),
        };

        assert!(PropagatedUnroller::unroll(p).is_err());
    }

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
        // foo_2 = i_1 + j_1

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
                FieldElementExpression::Add(
                    box FieldElementExpression::Identifier(Identifier::from("i").version(0)),
                    box FieldElementExpression::Identifier(Identifier::from("j").version(0)),
                )
                .into(),
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
                FieldElementExpression::Add(
                    box FieldElementExpression::Identifier(Identifier::from("i").version(0)),
                    box FieldElementExpression::Identifier(Identifier::from("j").version(1)),
                )
                .into(),
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
                FieldElementExpression::Add(
                    box FieldElementExpression::Identifier(Identifier::from("i").version(1)),
                    box FieldElementExpression::Identifier(Identifier::from("j").version(2)),
                )
                .into(),
            ),
        ];

        let p = TypedProgram {
            modules: vec![(
                "main".into(),
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
            main: "main".into(),
        };

        let statements = match PropagatedUnroller::unroll(p).unwrap().modules
            [std::path::Path::new("main")]
        .functions[&FunctionKey::with_id("main")]
            .clone()
        {
            TypedFunctionSymbol::Here(f) => f.statements,
            _ => unreachable!(),
        };

        assert_eq!(statements, expected_statements);
    }
}
