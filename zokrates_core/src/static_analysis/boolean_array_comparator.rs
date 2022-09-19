use zokrates_ast::typed::{
    folder::*, ArrayExpressionInner, ArrayValue, BooleanExpression, ConditionalExpression,
    ConditionalKind, EqExpression, FieldElementExpression, SelectExpression, Type, TypedExpression,
    TypedProgram, UExpressionInner,
};
use zokrates_field::Field;

#[derive(Default)]
pub struct BooleanArrayComparator;

impl BooleanArrayComparator {
    pub fn simplify<T: Field>(p: TypedProgram<T>) -> TypedProgram<T> {
        Self::default().fold_program(p)
    }
}

impl<'ast, T: Field> Folder<'ast, T> for BooleanArrayComparator {
    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> BooleanExpression<'ast, T> {
        match e {
            BooleanExpression::ArrayEq(e) => match e.left.inner_type() {
                Type::Boolean => {
                    let len = e.left.size();
                    let len = match len.as_inner() {
                        UExpressionInner::Value(v) => *v as usize,
                        _ => unreachable!("array size should be known"),
                    };

                    let chunk_size = T::get_required_bits() as usize - 1;

                    let left_elements: Vec<_> = (0..len)
                        .map(|i| {
                            BooleanExpression::Select(SelectExpression::new(
                                *e.left.clone(),
                                (i as u32).into(),
                            ))
                        })
                        .collect();
                    let right_elements: Vec<_> = (0..len)
                        .map(|i| {
                            BooleanExpression::Select(SelectExpression::new(
                                *e.right.clone(),
                                (i as u32).into(),
                            ))
                        })
                        .collect();

                    let process = |elements: &[BooleanExpression<'ast, T>]| {
                        elements
                            .chunks(chunk_size)
                            .map(|chunk| {
                                TypedExpression::from(
                                    chunk
                                        .iter()
                                        .rev()
                                        .enumerate()
                                        .rev()
                                        .map(|(index, c)| {
                                            FieldElementExpression::Conditional(
                                                ConditionalExpression::new(
                                                    c.clone(),
                                                    FieldElementExpression::Pow(
                                                        box FieldElementExpression::Number(
                                                            T::from(2),
                                                        ),
                                                        box (index as u32).into(),
                                                    ),
                                                    T::zero().into(),
                                                    ConditionalKind::Ternary,
                                                ),
                                            )
                                        })
                                        .fold(None, |acc, e| match acc {
                                            Some(acc) => {
                                                Some(FieldElementExpression::Add(box acc, box e))
                                            }
                                            None => Some(e),
                                        })
                                        .unwrap_or_else(|| {
                                            FieldElementExpression::Number(T::zero())
                                        }),
                                )
                                .into()
                            })
                            .collect()
                    };

                    let left: Vec<_> = process(&left_elements);

                    let right: Vec<_> = process(&right_elements);

                    let chunk_count = left.len();

                    BooleanExpression::ArrayEq(EqExpression::new(
                        ArrayExpressionInner::Value(ArrayValue(left))
                            .annotate(Type::FieldElement, chunk_count as u32),
                        ArrayExpressionInner::Value(ArrayValue(right))
                            .annotate(Type::FieldElement, chunk_count as u32),
                    ))
                }
                _ => fold_boolean_expression(self, BooleanExpression::ArrayEq(e)),
            },
            e => fold_boolean_expression(self, e),
        }
    }
}

#[cfg(test)]
mod tests {
    use num::Zero;
    use zokrates_ast::typed::{
        ArrayExpressionInner, ArrayValue, BooleanExpression, ConditionalExpression,
        ConditionalKind, EqExpression, FieldElementExpression, SelectExpression, Type,
        TypedExpression, UBitwidth, UExpressionInner,
    };
    use zokrates_field::DummyCurveField;

    use super::*;

    #[test]
    fn simplify_short_array_eq() {
        // x == y // type bool[2]
        // should become
        // [x[0] ? 2**1 : 0 + x[1] ? 2**0 : 0] == [y[0] ? 2**1 : 0 + y[1] ? 2**0 : 0]
        // a single field is sufficient, as the prime we're working with is 3 bits long, so we can pack up to 2 bits

        let e: BooleanExpression<DummyCurveField> = BooleanExpression::ArrayEq(EqExpression::new(
            ArrayExpressionInner::Identifier("x".into()).annotate(Type::Boolean, 2u32),
            ArrayExpressionInner::Identifier("y".into()).annotate(Type::Boolean, 2u32),
        ));

        let expected = BooleanExpression::ArrayEq(EqExpression::new(
            ArrayExpressionInner::Value(ArrayValue(vec![TypedExpression::from(
                FieldElementExpression::Add(
                    box FieldElementExpression::Conditional(ConditionalExpression::new(
                        BooleanExpression::Select(SelectExpression::new(
                            ArrayExpressionInner::Identifier("x".into())
                                .annotate(Type::Boolean, 2u32),
                            UExpressionInner::Value(0).annotate(UBitwidth::B32),
                        )),
                        FieldElementExpression::Pow(
                            box FieldElementExpression::Number(DummyCurveField::from(2)),
                            box UExpressionInner::Value(1).annotate(UBitwidth::B32),
                        ),
                        FieldElementExpression::Number(DummyCurveField::zero()),
                        ConditionalKind::Ternary,
                    )),
                    box FieldElementExpression::Conditional(ConditionalExpression::new(
                        BooleanExpression::Select(SelectExpression::new(
                            ArrayExpressionInner::Identifier("x".into())
                                .annotate(Type::Boolean, 2u32),
                            UExpressionInner::Value(1).annotate(UBitwidth::B32),
                        )),
                        FieldElementExpression::Pow(
                            box FieldElementExpression::Number(DummyCurveField::from(2)),
                            box UExpressionInner::Value(0).annotate(UBitwidth::B32),
                        ),
                        FieldElementExpression::Number(DummyCurveField::zero()),
                        ConditionalKind::Ternary,
                    )),
                ),
            )
            .into()]))
            .annotate(Type::FieldElement, 1u32),
            ArrayExpressionInner::Value(ArrayValue(vec![TypedExpression::from(
                FieldElementExpression::Add(
                    box FieldElementExpression::Conditional(ConditionalExpression::new(
                        BooleanExpression::Select(SelectExpression::new(
                            ArrayExpressionInner::Identifier("y".into())
                                .annotate(Type::Boolean, 2u32),
                            UExpressionInner::Value(0).annotate(UBitwidth::B32),
                        )),
                        FieldElementExpression::Pow(
                            box FieldElementExpression::Number(DummyCurveField::from(2)),
                            box UExpressionInner::Value(1).annotate(UBitwidth::B32),
                        ),
                        FieldElementExpression::Number(DummyCurveField::zero()),
                        ConditionalKind::Ternary,
                    )),
                    box FieldElementExpression::Conditional(ConditionalExpression::new(
                        BooleanExpression::Select(SelectExpression::new(
                            ArrayExpressionInner::Identifier("y".into())
                                .annotate(Type::Boolean, 2u32),
                            UExpressionInner::Value(1).annotate(UBitwidth::B32),
                        )),
                        FieldElementExpression::Pow(
                            box FieldElementExpression::Number(DummyCurveField::from(2)),
                            box UExpressionInner::Value(0).annotate(UBitwidth::B32),
                        ),
                        FieldElementExpression::Number(DummyCurveField::zero()),
                        ConditionalKind::Ternary,
                    )),
                ),
            )
            .into()]))
            .annotate(Type::FieldElement, 1u32),
        ));

        let res = BooleanArrayComparator::default().fold_boolean_expression(e);

        assert_eq!(res, expected);
    }

    #[test]
    fn simplify_long_array_eq() {
        // x == y // type bool[3]
        // should become
        // [x[0] ? 2**2 : 0 + x[1] ? 2**1 : 0, x[2] ? 2**0 : 0] == [y[0] ? 2**2 : 0 + y[1] ? 2**1 : 0 y[2] ? 2**0 : 0]

        let e: BooleanExpression<DummyCurveField> = BooleanExpression::ArrayEq(EqExpression::new(
            ArrayExpressionInner::Identifier("x".into()).annotate(Type::Boolean, 3u32),
            ArrayExpressionInner::Identifier("y".into()).annotate(Type::Boolean, 3u32),
        ));

        let expected = BooleanExpression::ArrayEq(EqExpression::new(
            ArrayExpressionInner::Value(ArrayValue(vec![
                TypedExpression::from(FieldElementExpression::Add(
                    box FieldElementExpression::Conditional(ConditionalExpression::new(
                        BooleanExpression::Select(SelectExpression::new(
                            ArrayExpressionInner::Identifier("x".into())
                                .annotate(Type::Boolean, 3u32),
                            UExpressionInner::Value(0).annotate(UBitwidth::B32),
                        )),
                        FieldElementExpression::Pow(
                            box FieldElementExpression::Number(DummyCurveField::from(2)),
                            box UExpressionInner::Value(1).annotate(UBitwidth::B32),
                        ),
                        FieldElementExpression::Number(DummyCurveField::zero()),
                        ConditionalKind::Ternary,
                    )),
                    box FieldElementExpression::Conditional(ConditionalExpression::new(
                        BooleanExpression::Select(SelectExpression::new(
                            ArrayExpressionInner::Identifier("x".into())
                                .annotate(Type::Boolean, 3u32),
                            UExpressionInner::Value(1).annotate(UBitwidth::B32),
                        )),
                        FieldElementExpression::Pow(
                            box FieldElementExpression::Number(DummyCurveField::from(2)),
                            box UExpressionInner::Value(0).annotate(UBitwidth::B32),
                        ),
                        FieldElementExpression::Number(DummyCurveField::zero()),
                        ConditionalKind::Ternary,
                    )),
                ))
                .into(),
                TypedExpression::from(FieldElementExpression::Conditional(
                    ConditionalExpression::new(
                        BooleanExpression::Select(SelectExpression::new(
                            ArrayExpressionInner::Identifier("x".into())
                                .annotate(Type::Boolean, 3u32),
                            UExpressionInner::Value(2).annotate(UBitwidth::B32),
                        )),
                        FieldElementExpression::Pow(
                            box FieldElementExpression::Number(DummyCurveField::from(2)),
                            box UExpressionInner::Value(0).annotate(UBitwidth::B32),
                        ),
                        FieldElementExpression::Number(DummyCurveField::zero()),
                        ConditionalKind::Ternary,
                    ),
                ))
                .into(),
            ]))
            .annotate(Type::FieldElement, 2u32),
            ArrayExpressionInner::Value(ArrayValue(vec![
                TypedExpression::from(FieldElementExpression::Add(
                    box FieldElementExpression::Conditional(ConditionalExpression::new(
                        BooleanExpression::Select(SelectExpression::new(
                            ArrayExpressionInner::Identifier("y".into())
                                .annotate(Type::Boolean, 3u32),
                            UExpressionInner::Value(0).annotate(UBitwidth::B32),
                        )),
                        FieldElementExpression::Pow(
                            box FieldElementExpression::Number(DummyCurveField::from(2)),
                            box UExpressionInner::Value(1).annotate(UBitwidth::B32),
                        ),
                        FieldElementExpression::Number(DummyCurveField::zero()),
                        ConditionalKind::Ternary,
                    )),
                    box FieldElementExpression::Conditional(ConditionalExpression::new(
                        BooleanExpression::Select(SelectExpression::new(
                            ArrayExpressionInner::Identifier("y".into())
                                .annotate(Type::Boolean, 3u32),
                            UExpressionInner::Value(1).annotate(UBitwidth::B32),
                        )),
                        FieldElementExpression::Pow(
                            box FieldElementExpression::Number(DummyCurveField::from(2)),
                            box UExpressionInner::Value(0).annotate(UBitwidth::B32),
                        ),
                        FieldElementExpression::Number(DummyCurveField::zero()),
                        ConditionalKind::Ternary,
                    )),
                ))
                .into(),
                TypedExpression::from(FieldElementExpression::Conditional(
                    ConditionalExpression::new(
                        BooleanExpression::Select(SelectExpression::new(
                            ArrayExpressionInner::Identifier("y".into())
                                .annotate(Type::Boolean, 3u32),
                            UExpressionInner::Value(2).annotate(UBitwidth::B32),
                        )),
                        FieldElementExpression::Pow(
                            box FieldElementExpression::Number(DummyCurveField::from(2)),
                            box UExpressionInner::Value(0).annotate(UBitwidth::B32),
                        ),
                        FieldElementExpression::Number(DummyCurveField::zero()),
                        ConditionalKind::Ternary,
                    ),
                ))
                .into(),
            ]))
            .annotate(Type::FieldElement, 2u32),
        ));

        let res = BooleanArrayComparator::default().fold_boolean_expression(e);

        assert_eq!(res, expected);
    }
}
