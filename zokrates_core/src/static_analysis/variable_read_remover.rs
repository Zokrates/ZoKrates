//! Module containing removal of variable access to complex types
//!
//! For example:
//! ```zokrates
//! a[index]
//! ```
//!
//! Would become
//! ```zokrates
//! if(index == 0, a[0], if(index == 1, a[1], ...))
//! ```

use crate::typed_absy::{folder::*, *};
use zokrates_field::Field;

pub struct VariableReadRemover<'ast, T: Field> {
    statements: Vec<TypedStatement<'ast, T>>,
}

impl<'ast, T: Field> VariableReadRemover<'ast, T> {
    fn new() -> Self {
        Self { statements: vec![] }
    }

    pub fn apply(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        Self::new().fold_program(p)
    }

    fn select<E: Expr<'ast, T> + Select<'ast, T> + IfElse<'ast, T>>(
        &mut self,
        e: SelectExpression<'ast, T, E>,
    ) -> E::Inner {
        let a = *e.array;
        let i = *e.index;

        match i.into_inner() {
            UExpressionInner::Value(i) => {
                E::select(a, UExpressionInner::Value(i).annotate(UBitwidth::B32)).into_inner()
            }
            i => {
                let size = match a.get_type().clone() {
                    Type::Array(array_ty) => match array_ty.size.into_inner() {
                        UExpressionInner::Value(size) => size as u32,
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                };

                self.statements.push(TypedStatement::Assertion(
                    (0..size)
                        .map(|index| {
                            BooleanExpression::UintEq(
                                box i.clone().annotate(UBitwidth::B32),
                                box index.into(),
                            )
                        })
                        .fold(None, |acc, e| match acc {
                            Some(acc) => Some(BooleanExpression::Or(box acc, box e)),
                            None => Some(e),
                        })
                        .unwrap(),
                ));

                (0..size)
                    .map(|i| {
                        E::select(
                            a.clone(),
                            UExpressionInner::Value(i.into()).annotate(UBitwidth::B32),
                        )
                    })
                    .enumerate()
                    .rev()
                    .fold(None, |acc, (index, res)| match acc {
                        Some(acc) => Some(E::if_else(
                            BooleanExpression::UintEq(
                                box i.clone().annotate(UBitwidth::B32),
                                box (index as u32).into(),
                            ),
                            res,
                            acc,
                        )),
                        None => Some(res),
                    })
                    .unwrap()
                    .into_inner()
            }
        }
    }
}

impl<'ast, T: Field> Folder<'ast, T> for VariableReadRemover<'ast, T> {
    fn fold_select_expression<
        E: Expr<'ast, T> + Select<'ast, T> + IfElse<'ast, T> + From<TypedExpression<'ast, T>>,
    >(
        &mut self,
        _: &E::Ty,
        e: SelectExpression<'ast, T, E>,
    ) -> ThisOrUncle<SelectExpression<'ast, T, E>, E::Inner> {
        ThisOrUncle::Uncle(self.select(e))
    }

    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        let s = fold_statement(self, s);
        self.statements.drain(..).chain(s).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::Bn128Field;

    #[test]
    fn select() {
        // b = a[i]

        // ->

        // i <= 1 == true
        // b = if i == 0 then a[0] else if i == 1 then a[1] else 0

        let access: TypedStatement<Bn128Field> = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_element("b")),
            FieldElementExpression::select(
                ArrayExpressionInner::Identifier("a".into()).annotate(Type::FieldElement, 2u32),
                UExpressionInner::Identifier("i".into()).annotate(UBitwidth::B32),
            )
            .into(),
        );

        assert_eq!(
            VariableReadRemover::new().fold_statement(access),
            vec![
                TypedStatement::Assertion(BooleanExpression::Or(
                    box BooleanExpression::UintEq(
                        box UExpressionInner::Identifier("i".into()).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(0).annotate(UBitwidth::B32)
                    ),
                    box BooleanExpression::UintEq(
                        box UExpressionInner::Identifier("i".into()).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(1).annotate(UBitwidth::B32)
                    )
                )),
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("b")),
                    FieldElementExpression::if_else(
                        BooleanExpression::UintEq(
                            box UExpressionInner::Identifier("i".into()).annotate(UBitwidth::B32),
                            box UExpressionInner::Value(0).annotate(UBitwidth::B32)
                        ),
                        FieldElementExpression::select(
                            ArrayExpressionInner::Identifier("a".into())
                                .annotate(Type::FieldElement, 2u32),
                            0u32,
                        ),
                        FieldElementExpression::select(
                            ArrayExpressionInner::Identifier("a".into())
                                .annotate(Type::FieldElement, 2u32),
                            1u32,
                        )
                    )
                    .into()
                )
            ]
        );
    }
}
