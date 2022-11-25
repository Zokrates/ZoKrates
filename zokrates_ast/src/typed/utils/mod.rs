use super::{
    identifier::IdTrait, ArrayExpression, ArrayExpressionInner, ArrayValue, BooleanExpression,
    Conditional, ConditionalKind, Expr, FieldElementExpression, Id, Identifier, Select, Typed,
    TypedExpression, TypedExpressionOrSpread, UBitwidth, UExpression, UExpressionInner,
};

use zokrates_field::Field;

pub fn f<I, T, U: TryInto<T>>(v: U) -> FieldElementExpression<I, T> {
    FieldElementExpression::Number(v.try_into().map_err(|_| ()).unwrap())
}

pub fn a_id<I: IdTrait, T: Field, J: TryInto<Identifier<I>>>(v: J) -> ArrayExpressionInner<I, T> {
    ArrayExpression::identifier(v.try_into().map_err(|_| ()).unwrap())
}

pub fn a<I, T, E: Typed<I, T> + Expr<I, T> + Into<TypedExpression<I, T>>, const N: usize>(
    values: [E; N],
) -> ArrayExpression<I, T> {
    let ty = values[0].get_type();
    ArrayExpressionInner::Value(ArrayValue(
        values
            .into_iter()
            .map(|e| TypedExpressionOrSpread::Expression(e.into()))
            .collect(),
    ))
    .annotate(ty, N as u32)
}

pub fn u_32<I, T, U: TryInto<u32>>(v: U) -> UExpression<I, T> {
    UExpressionInner::Value(v.try_into().map_err(|_| ()).unwrap() as u128).annotate(UBitwidth::B32)
}

pub fn conditional<I, T, E: Conditional<I, T>>(
    condition: BooleanExpression<I, T>,
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
    I,
    T,
    E: Select<I, T>,
    A: TryInto<ArrayExpression<I, T>>,
    J: TryInto<UExpression<I, T>>,
>(
    array: A,
    index: J,
) -> E {
    E::select(
        array.try_into().map_err(|_| ()).unwrap(),
        index.try_into().map_err(|_| ()).unwrap(),
    )
}
