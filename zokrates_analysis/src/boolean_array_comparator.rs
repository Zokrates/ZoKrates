use zokrates_ast::{
    common::WithSpan,
    typed::{
        folder::*, ArrayExpression, ArrayType, BooleanExpression, Conditional, ConditionalKind,
        Expr, FieldElementExpression, Select, Type, TypedExpression, TypedProgram, UExpression,
        UExpressionInner,
    },
};

use zokrates_field::Field;

fn sum_rec<T: std::ops::Add<Output = T> + Clone>(a: &[T], default: &T) -> T {
    match a.len() {
        0 => default.clone(),
        1 => a[0].clone(),
        n => sum_rec(&a[..n / 2], default) + sum_rec(&a[n / 2..], default),
    }
}

#[derive(Default)]
pub struct BooleanArrayComparator;

impl BooleanArrayComparator {
    pub fn simplify<T: Field>(p: TypedProgram<T>) -> TypedProgram<T> {
        Self::default().fold_program(p)
    }
}

impl<'ast, T: Field> Folder<'ast, T> for BooleanArrayComparator {
    fn fold_boolean_expression_cases(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> BooleanExpression<'ast, T> {
        match e {
            BooleanExpression::ArrayEq(e) => match *e.left.inner_type() {
                Type::Boolean => {
                    let span = e.get_span();

                    let len = e.left.size();
                    let len = match len.as_inner() {
                        UExpressionInner::Value(v) => v.value as usize,
                        _ => unreachable!("array size should be known"),
                    };

                    let chunk_size = T::get_required_bits() - 1;

                    let left_elements: Vec<_> = (0..len)
                        .map(|i| BooleanExpression::select(*e.left.clone(), i as u32).span(span))
                        .collect();
                    let right_elements: Vec<_> = (0..len)
                        .map(|i| BooleanExpression::select(*e.right.clone(), i as u32).span(span))
                        .collect();

                    let process = |elements: &[BooleanExpression<'ast, T>]| {
                        elements
                            .chunks(chunk_size)
                            .map(|chunk| {
                                TypedExpression::from(sum_rec(
                                    &chunk
                                        .iter()
                                        .rev()
                                        .enumerate()
                                        .rev()
                                        .map(|(index, c)| {
                                            FieldElementExpression::conditional(
                                                c.clone().span(span),
                                                FieldElementExpression::pow(
                                                    FieldElementExpression::value(T::from(2))
                                                        .span(span),
                                                    UExpression::from(index as u32).span(span),
                                                ),
                                                FieldElementExpression::from(T::zero()).span(span),
                                                ConditionalKind::Ternary,
                                            )
                                            .span(span)
                                        })
                                        .collect::<Vec<_>>(),
                                    &FieldElementExpression::value(T::from(0)).span(span),
                                ))
                                .span(span)
                                .into()
                            })
                            .collect()
                    };

                    let left: Vec<_> = process(&left_elements);

                    let right: Vec<_> = process(&right_elements);

                    let chunk_count = left.len();

                    BooleanExpression::array_eq(
                        ArrayExpression::value(left)
                            .annotate(ArrayType::new(Type::FieldElement, chunk_count as u32))
                            .span(span),
                        ArrayExpression::value(right)
                            .annotate(ArrayType::new(Type::FieldElement, chunk_count as u32))
                            .span(span),
                    )
                }
                _ => fold_boolean_expression_cases(self, BooleanExpression::ArrayEq(e)),
            },
            e => fold_boolean_expression_cases(self, e),
        }
    }
}

#[cfg(test)]
mod tests {
    use zokrates_ast::{
        common::expressions::BinaryExpression,
        typed::{BooleanExpression, Type},
    };
    use zokrates_field::DummyCurveField;

    use zokrates_ast::typed::utils::{a, a_id, conditional, f, select, u_32};

    use super::*;

    #[test]
    fn simplify_short_array_eq() {
        // x == y // type bool[2]
        // should become
        // [x[0] ? 2**1 : 0 + x[1] ? 2**0 : 0] == [y[0] ? 2**1 : 0 + y[1] ? 2**0 : 0]
        // a single field is sufficient, as the prime we're working with is 3 bits long, so we can pack up to 2 bits

        let x = a_id("x").annotate(ArrayType::new(Type::Boolean, 2u32));
        let y = a_id("y").annotate(ArrayType::new(Type::Boolean, 2u32));

        let e: BooleanExpression<DummyCurveField> =
            BooleanExpression::ArrayEq(BinaryExpression::new(x.clone(), y.clone()));

        let expected = BooleanExpression::ArrayEq(BinaryExpression::new(
            a([
                conditional(select(x.clone(), 0u32), f(2).pow(u_32(1)), f(0))
                    + conditional(select(x.clone(), 1u32), f(2).pow(u_32(0)), f(0)),
            ]),
            a([
                conditional(select(y.clone(), 0u32), f(2).pow(u_32(1)), f(0))
                    + conditional(select(y.clone(), 1u32), f(2).pow(u_32(0)), f(0)),
            ]),
        ));

        let res = BooleanArrayComparator::default().fold_boolean_expression(e);

        assert_eq!(res, expected);
    }

    #[test]
    fn simplify_long_array_eq() {
        // x == y // type bool[3]
        // should become
        // [x[0] ? 2**2 : 0 + x[1] ? 2**1 : 0, x[2] ? 2**0 : 0] == [y[0] ? 2**2 : 0 + y[1] ? 2**1 : 0 y[2] ? 2**0 : 0]

        let x = a_id("x").annotate(ArrayType::new(Type::Boolean, 3u32));
        let y = a_id("y").annotate(ArrayType::new(Type::Boolean, 3u32));

        let e: BooleanExpression<DummyCurveField> =
            BooleanExpression::ArrayEq(BinaryExpression::new(x.clone(), y.clone()));

        let expected = BooleanExpression::ArrayEq(BinaryExpression::new(
            a([
                conditional(select(x.clone(), 0u32), f(2).pow(u_32(1)), f(0))
                    + conditional(select(x.clone(), 1u32), f(2).pow(u_32(0)), f(0)),
                conditional(select(x.clone(), 2u32), f(2).pow(u_32(0)), f(0)),
            ]),
            a([
                conditional(select(y.clone(), 0u32), f(2).pow(u_32(1)), f(0))
                    + conditional(select(y.clone(), 1u32), f(2).pow(u_32(0)), f(0)),
                conditional(select(y.clone(), 2u32), f(2).pow(u_32(0)), f(0)),
            ]),
        ));

        let res = BooleanArrayComparator::default().fold_boolean_expression(e);

        assert_eq!(res, expected);
    }
}
