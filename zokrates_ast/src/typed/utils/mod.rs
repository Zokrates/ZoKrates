use super::{
    ArrayExpression, ArrayExpressionInner, BooleanExpression, Conditional, ConditionalKind,
    FieldElementExpression, Identifier, Select, UBitwidth, UExpression, UExpressionInner,
};

pub fn f<'ast, T, U: TryInto<T>>(v: U) -> FieldElementExpression<'ast, T> {
    FieldElementExpression::Number(v.try_into().map_err(|_| ()).unwrap())
}

pub fn a_id<'ast, T, I: TryInto<Identifier<'ast>>>(v: I) -> ArrayExpressionInner<'ast, T> {
    ArrayExpressionInner::Identifier(v.try_into().map_err(|_| ()).unwrap())
}

pub fn u_32<'ast, T, U: TryInto<u32>>(v: U) -> UExpression<'ast, T> {
    UExpressionInner::Value(v.try_into().map_err(|_| ()).unwrap() as u128).annotate(UBitwidth::B32)
}

pub fn conditional<'ast, T, E: Conditional<'ast, T>>(
    condition: BooleanExpression<'ast, T>,
    consequence: E,
    alternative: E,
) -> E {
    E::conditional(
        condition,
        consequence,
        alternative,
        ConditionalKind::Ternary,
    )
}

pub fn select<
    'ast,
    T,
    E: Select<'ast, T>,
    A: TryInto<ArrayExpression<'ast, T>>,
    I: TryInto<UExpression<'ast, T>>,
>(
    array: A,
    index: I,
) -> E {
    E::select(
        array.try_into().map_err(|_| ()).unwrap(),
        index.try_into().map_err(|_| ()).unwrap(),
    )
}
