use super::{
    ArrayExpression, ArrayExpressionInner, BooleanExpression, Conditional, ConditionalKind, Expr,
    FieldElementExpression, GArrayType, Id, Identifier, Select, Typed, TypedExpression,
    TypedExpressionOrSpread, UBitwidth, UExpression, ValueExpression,
};

use zokrates_field::Field;

pub fn f<'ast, T, U: TryInto<T>>(v: U) -> FieldElementExpression<'ast, T> {
    FieldElementExpression::Value(ValueExpression::new(v.try_into().map_err(|_| ()).unwrap()))
}

pub fn a_id<'ast, T: Field, I: TryInto<Identifier<'ast>>>(v: I) -> ArrayExpressionInner<'ast, T> {
    ArrayExpression::identifier(v.try_into().map_err(|_| ()).unwrap())
}

pub fn a<
    'ast,
    T: Field,
    E: Typed<'ast, T> + Expr<'ast, T> + Into<TypedExpression<'ast, T>>,
    const N: usize,
>(
    values: [E; N],
) -> ArrayExpression<'ast, T> {
    let ty = values[0].get_type();

    let array_ty = GArrayType::new(ty, N as u32);
    ArrayExpression::value(
        values
            .into_iter()
            .map(|e| TypedExpressionOrSpread::Expression(e.into()))
            .collect(),
    )
    .annotate(array_ty)
}

pub fn u_32<'ast, T: Field, U: TryInto<u32>>(v: U) -> UExpression<'ast, T> {
    UExpression::value(v.try_into().map_err(|_| ()).unwrap() as u128).annotate(UBitwidth::B32)
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
