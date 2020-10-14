//! Module containing iterative unrolling in order to unroll nested loops with variable bounds
//!
//! For example:
//! ```zokrates
//! for u32 i in 0..5 do
//! 	for u32 j in i..5 do
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

use static_analysis::inline::Inliner;
use static_analysis::propagation::Propagator;
use static_analysis::unroll::Unroller;
use typed_absy::TypedProgram;
use zokrates_field::Field;

pub enum Output<'ast, T: Field> {
    Complete(TypedProgram<'ast, T>),
    Blocked(TypedProgram<'ast, T>, Blocked, bool),
}

#[derive(Debug, PartialEq, Clone)]
pub enum Blocked {
    Unroll,
    Inline,
}

pub struct PropagatedUnroller;

impl PropagatedUnroller {
    pub fn unroll<'ast, T: Field>(
        p: TypedProgram<'ast, T>,
    ) -> Result<TypedProgram<'ast, T>, &'static str> {
        loop {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use typed_absy::types::{DeclarationFunctionKey, DeclarationSignature};
    use typed_absy::*;
    use zokrates_field::Bn128Field;

    #[test]
    fn for_loop() {
        //	for u32 i in 0..2
        //		for u32 j in i..2
        //			u32 foo = i + j

        // should be unrolled to
        // i_0 = 0
        // j_0 = 0
        // foo_0 = i_0 + j_0
        // j_1 = 1
        // foo_1 = i_0 + j_1
        // i_1 = 1
        // j_2 = 1
        // foo_2 = i_1 + j_1

        let s: TypedStatement<Bn128Field> = TypedStatement::For(
            Variable::uint("i", UBitwidth::B32),
            0u32.into(),
            2u32.into(),
            vec![TypedStatement::For(
                Variable::uint("j", UBitwidth::B32),
                UExpressionInner::Identifier("i".into()).annotate(UBitwidth::B32),
                2u32.into(),
                vec![
                    TypedStatement::Declaration(Variable::uint("foo", UBitwidth::B32)),
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::uint("foo", UBitwidth::B32)),
                        UExpressionInner::Add(
                            box UExpressionInner::Identifier("i".into()).annotate(UBitwidth::B32),
                            box UExpressionInner::Identifier("j".into()).annotate(UBitwidth::B32),
                        )
                        .annotate(UBitwidth::B32)
                        .into(),
                    ),
                ],
            )],
        );

        let expected_statements = vec![
            TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::uint(
                    Identifier::from("i").version(0),
                    UBitwidth::B32,
                )),
                UExpression::from(0u32).into(),
            ),
            TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::uint(
                    Identifier::from("j").version(0),
                    UBitwidth::B32,
                )),
                UExpression::from(0u32).into(),
            ),
            TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::uint(
                    Identifier::from("foo").version(0),
                    UBitwidth::B32,
                )),
                UExpression::add(
                    UExpressionInner::Identifier(Identifier::from("i").version(0))
                        .annotate(UBitwidth::B32),
                    UExpressionInner::Identifier(Identifier::from("j").version(0))
                        .annotate(UBitwidth::B32),
                )
                .into(),
            ),
            TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::uint(
                    Identifier::from("j").version(1),
                    UBitwidth::B32,
                )),
                UExpression::from(1u32).into(),
            ),
            TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::uint(
                    Identifier::from("foo").version(1),
                    UBitwidth::B32,
                )),
                UExpression::add(
                    UExpressionInner::Identifier(Identifier::from("i").version(0))
                        .annotate(UBitwidth::B32),
                    UExpressionInner::Identifier(Identifier::from("j").version(1))
                        .annotate(UBitwidth::B32),
                )
                .into(),
            ),
            TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::uint(
                    Identifier::from("i").version(1),
                    UBitwidth::B32,
                )),
                UExpression::from(1u32).into(),
            ),
            TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::uint(
                    Identifier::from("j").version(2),
                    UBitwidth::B32,
                )),
                UExpression::from(1u32).into(),
            ),
            TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::uint(
                    Identifier::from("foo").version(2),
                    UBitwidth::B32,
                )),
                UExpression::add(
                    UExpressionInner::Identifier(Identifier::from("i").version(1))
                        .annotate(UBitwidth::B32),
                    UExpressionInner::Identifier(Identifier::from("j").version(2))
                        .annotate(UBitwidth::B32),
                )
                .into(),
            ),
        ];

        let p = TypedProgram {
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![(
                        DeclarationFunctionKey::with_id("main"),
                        TypedFunctionSymbol::Here(TypedFunction {
                            arguments: vec![],
                            signature: DeclarationSignature::new(),
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
        .functions[&DeclarationFunctionKey::with_id("main")]
            .clone()
        {
            TypedFunctionSymbol::Here(f) => f.statements,
            _ => unreachable!(),
        };

        assert_eq!(statements, expected_statements);
    }
}
