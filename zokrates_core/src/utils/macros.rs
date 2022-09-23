use std::path::PathBuf;

use zokrates_ast::typed::{
    types::GStructMember, ArrayExpression, ArrayExpressionInner, ArrayValue, Block,
    BooleanExpression, Conditional, ConditionalKind, CoreIdentifier, DeclarationFunctionKey,
    DeclarationType, DefinitionRhs, Element, Expr, FieldElementExpression, FunctionCall, GVariable,
    Identifier, Member, MemberId, Select, ShadowedIdentifier, StructExpression,
    StructExpressionInner, StructType, TupleExpression, TupleExpressionInner, TupleType, Type,
    Typed, TypedAssignee, TypedExpression, TypedExpressionOrSpread, TypedStatement, UExpression,
    Variable,
};

pub fn f<'ast, T, U: TryInto<T>>(v: U) -> FieldElementExpression<'ast, T> {
    FieldElementExpression::Number(v.try_into().map_err(|_| ()).unwrap())
}

pub fn f_id<'ast, T, I: TryInto<Identifier<'ast>>>(v: I) -> FieldElementExpression<'ast, T> {
    zokrates_ast::typed::FieldElementExpression::Identifier(v.try_into().map_err(|_| ()).unwrap())
}

pub fn a_id<'ast, T, I: TryInto<Identifier<'ast>>>(v: I) -> ArrayExpressionInner<'ast, T> {
    zokrates_ast::typed::ArrayExpressionInner::Identifier(v.try_into().map_err(|_| ()).unwrap())
}

pub fn id<'ast>(id: &'ast str) -> Identifier<'ast> {
    let mut limbs = id.split("_");
    let name = limbs.next().unwrap();
    let shadow = limbs.next().map(|n| n.parse().unwrap()).unwrap();
    let version = limbs.next().map(|n| n.parse().unwrap()).unwrap_or(0);
    Identifier {
        version,
        id: CoreIdentifier::Source(ShadowedIdentifier { shadow, id: name }),
    }
}

fn parse_type<'ast, T>(s: &'ast str) -> Type<'ast, T> {
    match s {
        "field" => Type::FieldElement,
        "bool" => Type::Boolean,
        _ => unimplemented!(),
    }
}

fn parse_expression<'ast, T>(s: &'ast str, ty: &Type<'ast, T>) -> TypedExpression<'ast, T> {
    let id = id(s);
    match ty {
        Type::FieldElement => f_id(id).into(),
        _ => unimplemented!(),
    }
}

pub fn stat<'ast, T: Clone>(s: &'ast str) -> TypedStatement<'ast, T> {
    let mut is_mutable = false;
    let mut s = s.split(" ");
    let mut next = s.next().unwrap();
    if next == "mut" {
        is_mutable = true;
        next = s.next().unwrap();
    }
    let ty = parse_type(next);
    let id = CoreIdentifier::try_from(s.next().unwrap())
        .map_err(|_| ())
        .unwrap();
    assert_eq!(s.next().unwrap(), "=");
    let e = parse_expression(s.next().unwrap(), &ty);
    TypedStatement::Definition(Variable::new(id, ty, is_mutable).into(), e.into())
}

pub fn f_v<'ast, S: Clone, U: TryInto<Identifier<'ast>>>(v: U) -> GVariable<'ast, S> {
    GVariable::field_element(v.try_into().map_err(|_| ()).unwrap())
}

pub fn b<'ast, T>(v: bool) -> BooleanExpression<'ast, T> {
    BooleanExpression::Value(v)
}

pub fn b_id<'ast, T, U: TryInto<Identifier<'ast>>>(v: U) -> BooleanExpression<'ast, T> {
    zokrates_ast::typed::BooleanExpression::Identifier(v.try_into().map_err(|_| ()).unwrap())
}

pub fn b_v<'ast, T: Clone, U: TryInto<Identifier<'ast>>>(v: U) -> Variable<'ast, T> {
    Variable::boolean(v.try_into().map_err(|_| ()).unwrap())
}

pub fn u_64<'ast, T, U: TryInto<u64>>(v: U) -> UExpression<'ast, T> {
    zokrates_ast::typed::UExpressionInner::Value(v.try_into().map_err(|_| ()).unwrap() as u128)
        .annotate(zokrates_ast::typed::UBitwidth::B64)
}

pub fn u_64_id<'ast, T>(v: &'ast str) -> UExpression<'ast, T> {
    zokrates_ast::typed::UExpressionInner::Identifier(v.into())
        .annotate(zokrates_ast::typed::UBitwidth::B32)
}

pub fn u_32<'ast, T, U: TryInto<u32>>(v: U) -> UExpression<'ast, T> {
    zokrates_ast::typed::UExpressionInner::Value(v.try_into().map_err(|_| ()).unwrap() as u128)
        .annotate(zokrates_ast::typed::UBitwidth::B32)
}

pub fn u_32_id<'ast, T>(v: &'ast str) -> UExpression<'ast, T> {
    zokrates_ast::typed::UExpressionInner::Identifier(v.into())
        .annotate(zokrates_ast::typed::UBitwidth::B32)
}

pub fn u_16<'ast, T, U: TryInto<u16>>(v: U) -> UExpression<'ast, T> {
    zokrates_ast::typed::UExpressionInner::Value(v.try_into().map_err(|_| ()).unwrap() as u128)
        .annotate(zokrates_ast::typed::UBitwidth::B32)
}

pub fn u_16_id<'ast, T>(v: &'ast str) -> UExpression<'ast, T> {
    zokrates_ast::typed::UExpressionInner::Identifier(v.into())
        .annotate(zokrates_ast::typed::UBitwidth::B16)
}

pub fn u_8<'ast, T, U: TryInto<u8>>(v: U) -> UExpression<'ast, T> {
    zokrates_ast::typed::UExpressionInner::Value(v.try_into().map_err(|_| ()).unwrap() as u128)
        .annotate(zokrates_ast::typed::UBitwidth::B8)
}

pub fn u_8_id<'ast, T>(v: &'ast str) -> UExpression<'ast, T> {
    zokrates_ast::typed::UExpressionInner::Identifier(v.into())
        .annotate(zokrates_ast::typed::UBitwidth::B8)
}

pub fn conditional<'ast, T, E: Conditional<'ast, T>, B: TryInto<BooleanExpression<'ast, T>>>(
    condition: B,
    consequence: E,
    alternative: E,
) -> E {
    E::conditional(
        condition.try_into().map_err(|_| ()).unwrap(),
        consequence,
        alternative,
        ConditionalKind::Ternary,
    )
}

pub fn block<'ast, T, E: Block<'ast, T>, const N: usize>(
    statements: [TypedStatement<'ast, T>; N],
    value: E,
) -> E {
    E::block(statements.into(), value)
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

pub fn member<
    'ast,
    T,
    E: Member<'ast, T>,
    S: TryInto<StructExpression<'ast, T>>,
    I: TryInto<MemberId>,
>(
    struc: S,
    id: I,
) -> E {
    E::member(
        struc.try_into().map_err(|_| ()).unwrap(),
        id.try_into().map_err(|_| ()).unwrap(),
    )
}

pub fn call<'ast, T, E: Expr<'ast, T> + FunctionCall<'ast, T>, const N: usize, const M: usize>(
    key: DeclarationFunctionKey<'ast, T>,
    generics: [Option<UExpression<'ast, T>>; N],
    arguments: [TypedExpression<'ast, T>; M],
) -> E::Inner {
    E::function_call(
        key,
        generics.into_iter().collect(),
        arguments.into_iter().collect(),
    )
}

pub fn element<
    'ast,
    T,
    E: Element<'ast, T>,
    U: TryInto<TupleExpression<'ast, T>>,
    I: TryInto<u32>,
>(
    tuple: U,
    index: I,
) -> E {
    E::element(
        tuple.try_into().map_err(|_| ()).unwrap(),
        index.try_into().map_err(|_| ()).unwrap(),
    )
}

// pub fn equals<'ast, T, E: Equals<'ast, T>>(left: E, right: E) -> BooleanExpression<'ast, T> {
//     left.equals(right)
// }

// pub fn define_no_inference<
//     'ast,
//     T,
//     A: TryInto<TypedAssignee<'ast, T>>,
//     E: TryInto<TypedExpression<'ast, T>>,
// >(
//     a: A,
//     e: E,
// ) -> TypedStatement<'ast, T> {
//     TypedStatement::Definition(
//         a.try_into().map_err(|_| ()).unwrap(),
//         DefinitionRhs::Expression(e.try_into().map_err(|_| ()).unwrap()),
//     )
// }

// pub fn define<
//     'ast,
//     T: Clone,
//     A: TryInto<Identifier<'ast>>,
//     E: Typed<'ast, T> + Expr<'ast, T> + TryInto<TypedExpression<'ast, T>>,
// >(
//     a: A,
//     e: E,
// ) -> TypedStatement<'ast, T> {
//     let ty = e.get_type().clone();

//     TypedStatement::Definition(
//         Variable::new(a.try_into().map_err(|_| ()).unwrap(), ty, false).into(),
//         DefinitionRhs::Expression(e.try_into().map_err(|_| ()).unwrap()),
//     )
// }

// pub fn pop_call<'ast, T>() -> TypedStatement<'ast, T> {
//     TypedStatement::PopCallLog
// }

// pub fn push_call<'ast, T>() -> TypedStatement<'ast, T> {
//     TypedStatement::PushCallLog
// }

// pub fn ret<'ast, T, E: Typed<'ast, T> + Expr<'ast, T> + TryInto<TypedExpression<'ast, T>>>(
//     e: E,
// ) -> TypedStatement<'ast, T> {
//     TypedStatement::Return(e.try_into().map_err(|_| ()).unwrap())
// }

pub fn condition_id<'ast>(i: usize) -> CoreIdentifier<'ast> {
    CoreIdentifier::Condition(i)
}

pub fn a<
    'ast,
    T,
    E: Typed<'ast, T> + Expr<'ast, T> + Into<TypedExpression<'ast, T>>,
    const N: usize,
>(
    values: [E; N],
) -> ArrayExpression<'ast, T> {
    let ty = values[0].get_type();
    ArrayExpressionInner::Value(ArrayValue(
        values
            .into_iter()
            .map(|e| TypedExpressionOrSpread::Expression(e.into()))
            .collect(),
    ))
    .annotate(ty, N as u32)
}

pub fn s<'ast, T: Clone, M: TryInto<String>, I: TryInto<MemberId>, const N: usize>(
    name: M,
    members: [(I, TypedExpression<'ast, T>); N],
) -> StructExpression<'ast, T> {
    let members: Vec<_> = members
        .into_iter()
        .map(|(id, e)| (id.try_into().map_err(|_| ()).unwrap(), e))
        .collect();

    let ty = StructType::new(
        PathBuf::default(),
        name.try_into().map_err(|_| ()).unwrap(),
        vec![],
        members
            .iter()
            .map(|(id, e)| GStructMember::new(id.clone(), e.get_type().clone()))
            .collect(),
    );

    StructExpressionInner::Value(members.into_iter().map(|(_, e)| e).collect()).annotate(ty)
}

pub fn t<'ast, T: Clone, const N: usize>(
    elements: [TypedExpression<'ast, T>; N],
) -> TupleExpression<'ast, T> {
    let ty = TupleType::new(elements.iter().map(|e| e.get_type().clone()).collect());

    TupleExpressionInner::Value(elements.into_iter().collect()).annotate(ty)
}
