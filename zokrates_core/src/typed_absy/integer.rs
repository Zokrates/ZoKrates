use crate::typed_absy::types::{ArrayType, Type};
use crate::typed_absy::UBitwidth;
use crate::typed_absy::{
    ArrayExpression, ArrayExpressionInner, BooleanExpression, FieldElementExpression, IfElse,
    Select, StructExpression, Typed, TypedExpression, TypedExpressionOrSpread, TypedSpread,
    UExpression, UExpressionInner,
};
use num_bigint::BigUint;
use std::convert::TryFrom;
use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Not, Rem, Sub};
use zokrates_field::Field;

type TypedExpressionPair<'ast, T> = (TypedExpression<'ast, T>, TypedExpression<'ast, T>);

impl<'ast, T: Field> TypedExpressionOrSpread<'ast, T> {
    pub fn align_to_type(e: Self, ty: Type<'ast, T>) -> Result<Self, (Self, Type<'ast, T>)> {
        match e {
            TypedExpressionOrSpread::Expression(e) => TypedExpression::align_to_type(e, ty)
                .map(|e| e.into())
                .map_err(|(e, t)| (e.into(), t)),
            TypedExpressionOrSpread::Spread(s) => {
                ArrayExpression::try_from_int(s.array, ty.clone())
                    .map(|e| TypedExpressionOrSpread::Spread(TypedSpread { array: e }))
                    .map_err(|e| (e.into(), ty))
            }
        }
    }
}

impl<'ast, T: Field> TypedExpression<'ast, T> {
    // return two TypedExpression, replacing IntExpression by FieldElement or Uint to try to align the two types if possible.
    // Post condition is that (lhs, rhs) cannot be made equal by further removing IntExpressions
    pub fn align_without_integers(
        lhs: Self,
        rhs: Self,
    ) -> Result<TypedExpressionPair<'ast, T>, TypedExpressionPair<'ast, T>> {
        use self::TypedExpression::*;

        match (lhs, rhs) {
            (Int(lhs), FieldElement(rhs)) => Ok((
                FieldElementExpression::try_from_int(lhs)
                    .map_err(|lhs| (lhs.into(), rhs.clone().into()))?
                    .into(),
                FieldElement(rhs),
            )),
            (FieldElement(lhs), Int(rhs)) => Ok((
                FieldElement(lhs.clone()),
                FieldElementExpression::try_from_int(rhs)
                    .map_err(|rhs| (lhs.into(), rhs.into()))?
                    .into(),
            )),
            (Int(lhs), Uint(rhs)) => Ok((
                UExpression::try_from_int(lhs, rhs.bitwidth())
                    .map_err(|lhs| (lhs.into(), rhs.clone().into()))?
                    .into(),
                Uint(rhs),
            )),
            (Uint(lhs), Int(rhs)) => {
                let bitwidth = lhs.bitwidth();
                Ok((
                    Uint(lhs.clone()),
                    UExpression::try_from_int(rhs, bitwidth)
                        .map_err(|rhs| (lhs.into(), rhs.into()))?
                        .into(),
                ))
            }
            (Array(lhs), Array(rhs)) => {
                fn get_common_type<'a, T: Field>(
                    t: Type<'a, T>,
                    u: Type<'a, T>,
                ) -> Result<Type<'a, T>, ()> {
                    match (t, u) {
                        (Type::Int, Type::Int) => Err(()),
                        (Type::Int, u) => Ok(u),
                        (t, Type::Int) => Ok(t),
                        (Type::Array(t), Type::Array(u)) => Ok(Type::Array(ArrayType::new(
                            get_common_type(*t.ty, *u.ty)?,
                            t.size,
                        ))),
                        (t, _) => Ok(t),
                    }
                }

                let common_type =
                    get_common_type(lhs.inner_type().clone(), rhs.inner_type().clone())
                        .map_err(|_| (lhs.clone().into(), rhs.clone().into()))?;

                Ok((
                    ArrayExpression::try_from_int(lhs.clone(), common_type.clone())
                        .map_err(|lhs| (lhs.clone(), rhs.clone().into()))?
                        .into(),
                    ArrayExpression::try_from_int(rhs, common_type)
                        .map_err(|rhs| (lhs.clone().into(), rhs.clone()))?
                        .into(),
                ))
            }
            (Struct(lhs), Struct(rhs)) => {
                if lhs.get_type() == rhs.get_type() {
                    Ok((Struct(lhs), Struct(rhs)))
                } else {
                    Err((Struct(lhs), Struct(rhs)))
                }
            }
            (Uint(lhs), Uint(rhs)) => Ok((lhs.into(), rhs.into())),
            (Boolean(lhs), Boolean(rhs)) => Ok((lhs.into(), rhs.into())),
            (FieldElement(lhs), FieldElement(rhs)) => Ok((lhs.into(), rhs.into())),
            (Int(lhs), Int(rhs)) => Ok((lhs.into(), rhs.into())),
            (lhs, rhs) => Err((lhs, rhs)),
        }
    }

    pub fn align_to_type(e: Self, ty: Type<'ast, T>) -> Result<Self, (Self, Type<'ast, T>)> {
        match ty.clone() {
            Type::FieldElement => {
                FieldElementExpression::try_from_typed(e).map(TypedExpression::from)
            }
            Type::Boolean => BooleanExpression::try_from_typed(e).map(TypedExpression::from),
            Type::Uint(bitwidth) => {
                UExpression::try_from_typed(e, bitwidth).map(TypedExpression::from)
            }
            Type::Array(array_ty) => {
                ArrayExpression::try_from_typed(e, *array_ty.ty).map(TypedExpression::from)
            }
            Type::Struct(struct_ty) => {
                StructExpression::try_from_typed(e, struct_ty).map(TypedExpression::from)
            }
            Type::Int => Err(e),
        }
        .map_err(|e| (e, ty))
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum IntExpression<'ast, T> {
    Value(BigUint),
    Pos(Box<IntExpression<'ast, T>>),
    Neg(Box<IntExpression<'ast, T>>),
    Add(Box<IntExpression<'ast, T>>, Box<IntExpression<'ast, T>>),
    Sub(Box<IntExpression<'ast, T>>, Box<IntExpression<'ast, T>>),
    Mult(Box<IntExpression<'ast, T>>, Box<IntExpression<'ast, T>>),
    Div(Box<IntExpression<'ast, T>>, Box<IntExpression<'ast, T>>),
    Rem(Box<IntExpression<'ast, T>>, Box<IntExpression<'ast, T>>),
    Pow(Box<IntExpression<'ast, T>>, Box<IntExpression<'ast, T>>),
    IfElse(
        Box<BooleanExpression<'ast, T>>,
        Box<IntExpression<'ast, T>>,
        Box<IntExpression<'ast, T>>,
    ),
    Select(Box<ArrayExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    Xor(Box<IntExpression<'ast, T>>, Box<IntExpression<'ast, T>>),
    And(Box<IntExpression<'ast, T>>, Box<IntExpression<'ast, T>>),
    Or(Box<IntExpression<'ast, T>>, Box<IntExpression<'ast, T>>),
    Not(Box<IntExpression<'ast, T>>),
    LeftShift(Box<IntExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    RightShift(Box<IntExpression<'ast, T>>, Box<UExpression<'ast, T>>),
}

impl<'ast, T> Add for IntExpression<'ast, T> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        IntExpression::Add(box self, box other)
    }
}

impl<'ast, T> Sub for IntExpression<'ast, T> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        IntExpression::Sub(box self, box other)
    }
}

impl<'ast, T> Mul for IntExpression<'ast, T> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        IntExpression::Mult(box self, box other)
    }
}

impl<'ast, T> Div for IntExpression<'ast, T> {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        IntExpression::Div(box self, box other)
    }
}

impl<'ast, T> Rem for IntExpression<'ast, T> {
    type Output = Self;

    fn rem(self, other: Self) -> Self {
        IntExpression::Rem(box self, box other)
    }
}

impl<'ast, T> Not for IntExpression<'ast, T> {
    type Output = Self;

    fn not(self) -> Self {
        IntExpression::Not(box self)
    }
}

impl<'ast, T> Neg for IntExpression<'ast, T> {
    type Output = Self;

    fn neg(self) -> Self {
        IntExpression::Neg(box self)
    }
}

impl<'ast, T> IntExpression<'ast, T> {
    pub fn pow(self, other: Self) -> Self {
        IntExpression::Pow(box self, box other)
    }

    pub fn and(self, other: Self) -> Self {
        IntExpression::And(box self, box other)
    }

    pub fn xor(self, other: Self) -> Self {
        IntExpression::Xor(box self, box other)
    }

    pub fn or(self, other: Self) -> Self {
        IntExpression::Or(box self, box other)
    }

    pub fn left_shift(self, by: UExpression<'ast, T>) -> Self {
        IntExpression::LeftShift(box self, box by)
    }

    pub fn right_shift(self, by: UExpression<'ast, T>) -> Self {
        IntExpression::RightShift(box self, box by)
    }

    pub fn pos(self) -> Self {
        IntExpression::Pos(box self)
    }
}

impl<'ast, T: fmt::Display> fmt::Display for IntExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            IntExpression::Value(ref v) => write!(f, "{}", v),
            IntExpression::Pos(ref e) => write!(f, "(+{})", e),
            IntExpression::Neg(ref e) => write!(f, "(-{})", e),
            IntExpression::Div(ref lhs, ref rhs) => write!(f, "({} / {})", lhs, rhs),
            IntExpression::Rem(ref lhs, ref rhs) => write!(f, "({} % {})", lhs, rhs),
            IntExpression::Pow(ref lhs, ref rhs) => write!(f, "({} ** {})", lhs, rhs),
            IntExpression::Select(ref id, ref index) => write!(f, "{}[{}]", id, index),
            IntExpression::Add(ref lhs, ref rhs) => write!(f, "({} + {})", lhs, rhs),
            IntExpression::And(ref lhs, ref rhs) => write!(f, "({} & {})", lhs, rhs),
            IntExpression::Or(ref lhs, ref rhs) => write!(f, "({} | {})", lhs, rhs),
            IntExpression::Xor(ref lhs, ref rhs) => write!(f, "({} ^ {})", lhs, rhs),
            IntExpression::Sub(ref lhs, ref rhs) => write!(f, "({} - {})", lhs, rhs),
            IntExpression::Mult(ref lhs, ref rhs) => write!(f, "({} * {})", lhs, rhs),
            IntExpression::RightShift(ref e, ref by) => write!(f, "({} >> {})", e, by),
            IntExpression::LeftShift(ref e, ref by) => write!(f, "({} << {})", e, by),
            IntExpression::Not(ref e) => write!(f, "!{}", e),
            IntExpression::IfElse(ref condition, ref consequent, ref alternative) => write!(
                f,
                "if {} then {} else {} fi",
                condition, consequent, alternative
            ),
        }
    }
}

impl<'ast, T: Field> BooleanExpression<'ast, T> {
    pub fn try_from_typed(e: TypedExpression<'ast, T>) -> Result<Self, TypedExpression<'ast, T>> {
        match e {
            TypedExpression::Boolean(e) => Ok(e),
            e => Err(e),
        }
    }
}

impl<'ast, T: Field> FieldElementExpression<'ast, T> {
    pub fn try_from_typed(e: TypedExpression<'ast, T>) -> Result<Self, TypedExpression<'ast, T>> {
        match e {
            TypedExpression::FieldElement(e) => Ok(e),
            TypedExpression::Int(e) => {
                Self::try_from_int(e.clone()).map_err(|_| TypedExpression::Int(e))
            }
            e => Err(e),
        }
    }

    pub fn try_from_int(i: IntExpression<'ast, T>) -> Result<Self, IntExpression<'ast, T>> {
        match i {
            IntExpression::Value(i) => Ok(Self::Number(T::try_from(i.clone()).map_err(|_| i)?)),
            IntExpression::Add(box e1, box e2) => Ok(Self::Add(
                box Self::try_from_int(e1)?,
                box Self::try_from_int(e2)?,
            )),
            IntExpression::Sub(box e1, box e2) => Ok(Self::Sub(
                box Self::try_from_int(e1)?,
                box Self::try_from_int(e2)?,
            )),
            IntExpression::Mult(box e1, box e2) => Ok(Self::Mult(
                box Self::try_from_int(e1)?,
                box Self::try_from_int(e2)?,
            )),
            IntExpression::Pow(box e1, box e2) => Ok(Self::Pow(
                box Self::try_from_int(e1)?,
                box UExpression::try_from_int(e2, UBitwidth::B32)?,
            )),
            IntExpression::Div(box e1, box e2) => Ok(Self::Div(
                box Self::try_from_int(e1)?,
                box Self::try_from_int(e2)?,
            )),
            IntExpression::Pos(box e) => Ok(Self::Pos(box Self::try_from_int(e)?)),
            IntExpression::Neg(box e) => Ok(Self::Neg(box Self::try_from_int(e)?)),
            IntExpression::IfElse(box condition, box consequence, box alternative) => {
                Ok(Self::IfElse(
                    box condition,
                    box Self::try_from_int(consequence)?,
                    box Self::try_from_int(alternative)?,
                ))
            }
            IntExpression::Select(box array, box index) => {
                let size = array.size();

                match array.into_inner() {
                    ArrayExpressionInner::Value(values) => {
                        let values = values
                            .into_iter()
                            .map(|v| {
                                TypedExpressionOrSpread::align_to_type(v, Type::FieldElement)
                                    .map_err(|(e, _)| match e {
                                        TypedExpressionOrSpread::Expression(e) => {
                                            IntExpression::try_from(e).unwrap()
                                        }
                                        TypedExpressionOrSpread::Spread(a) => {
                                            IntExpression::select(a.array, 0u32)
                                        }
                                    })
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                        Ok(FieldElementExpression::select(
                            ArrayExpressionInner::Value(values.into())
                                .annotate(Type::FieldElement, size),
                            index,
                        ))
                    }
                    _ => unreachable!(),
                }
            }
            i => Err(i),
        }
    }
}

impl<'ast, T: Field> UExpression<'ast, T> {
    pub fn try_from_typed(
        e: TypedExpression<'ast, T>,
        bitwidth: UBitwidth,
    ) -> Result<Self, TypedExpression<'ast, T>> {
        match e {
            TypedExpression::Uint(e) => match e.bitwidth == bitwidth {
                true => Ok(e),
                _ => Err(TypedExpression::Uint(e)),
            },
            TypedExpression::Int(e) => {
                Self::try_from_int(e.clone(), bitwidth).map_err(|_| TypedExpression::Int(e))
            }
            e => Err(e),
        }
    }

    pub fn try_from_int(
        i: IntExpression<'ast, T>,
        bitwidth: UBitwidth,
    ) -> Result<Self, IntExpression<'ast, T>> {
        use self::IntExpression::*;

        match i {
            Value(i) => {
                if i <= BigUint::from(2u128.pow(bitwidth.to_usize() as u32) - 1) {
                    Ok(UExpressionInner::Value(
                        u128::from_str_radix(&i.to_str_radix(16), 16).unwrap(),
                    )
                    .annotate(bitwidth))
                } else {
                    Err(Value(i))
                }
            }
            Add(box e1, box e2) => {
                Ok(Self::try_from_int(e1, bitwidth)? + Self::try_from_int(e2, bitwidth)?)
            }
            Pos(box e) => Ok(Self::pos(Self::try_from_int(e, bitwidth)?)),
            Neg(box e) => Ok(Self::neg(Self::try_from_int(e, bitwidth)?)),
            Sub(box e1, box e2) => {
                Ok(Self::try_from_int(e1, bitwidth)? - Self::try_from_int(e2, bitwidth)?)
            }
            Mult(box e1, box e2) => {
                Ok(Self::try_from_int(e1, bitwidth)? * Self::try_from_int(e2, bitwidth)?)
            }
            Div(box e1, box e2) => {
                Ok(Self::try_from_int(e1, bitwidth)? / Self::try_from_int(e2, bitwidth)?)
            }
            Rem(box e1, box e2) => {
                Ok(Self::try_from_int(e1, bitwidth)? % Self::try_from_int(e2, bitwidth)?)
            }
            And(box e1, box e2) => Ok(UExpression::and(
                Self::try_from_int(e1, bitwidth)?,
                Self::try_from_int(e2, bitwidth)?,
            )),
            Or(box e1, box e2) => Ok(UExpression::or(
                Self::try_from_int(e1, bitwidth)?,
                Self::try_from_int(e2, bitwidth)?,
            )),
            Not(box e) => Ok(!Self::try_from_int(e, bitwidth)?),
            Xor(box e1, box e2) => Ok(UExpression::xor(
                Self::try_from_int(e1, bitwidth)?,
                Self::try_from_int(e2, bitwidth)?,
            )),
            RightShift(box e1, box e2) => Ok(UExpression::right_shift(
                Self::try_from_int(e1, bitwidth)?,
                e2,
            )),
            LeftShift(box e1, box e2) => Ok(UExpression::left_shift(
                Self::try_from_int(e1, bitwidth)?,
                e2,
            )),
            IfElse(box condition, box consequence, box alternative) => Ok(UExpression::if_else(
                condition,
                Self::try_from_int(consequence, bitwidth)?,
                Self::try_from_int(alternative, bitwidth)?,
            )),
            Select(box array, box index) => {
                let size = array.size();
                match array.into_inner() {
                    ArrayExpressionInner::Value(values) => {
                        let values = values
                            .into_iter()
                            .map(|v| {
                                TypedExpressionOrSpread::align_to_type(v, Type::Uint(bitwidth))
                                    .map_err(|(e, _)| match e {
                                        TypedExpressionOrSpread::Expression(e) => {
                                            IntExpression::try_from(e).unwrap()
                                        }
                                        TypedExpressionOrSpread::Spread(a) => {
                                            IntExpression::select(a.array, 0u32)
                                        }
                                    })
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                        Ok(UExpression::select(
                            ArrayExpressionInner::Value(values.into())
                                .annotate(Type::Uint(bitwidth), size),
                            index,
                        ))
                    }
                    _ => unreachable!(),
                }
            }
            i => Err(i),
        }
    }
}

impl<'ast, T: Field> ArrayExpression<'ast, T> {
    pub fn try_from_typed(
        e: TypedExpression<'ast, T>,
        target_inner_ty: Type<'ast, T>,
    ) -> Result<Self, TypedExpression<'ast, T>> {
        match e {
            TypedExpression::Array(e) => Self::try_from_int(e.clone(), target_inner_ty)
                .map_err(|_| TypedExpression::Array(e)),
            e => Err(e),
        }
    }

    // precondition: `array` is only made of inline arrays unless it does not contain the Integer type
    pub fn try_from_int(
        array: Self,
        target_inner_ty: Type<'ast, T>,
    ) -> Result<Self, TypedExpression<'ast, T>> {
        let array_ty = array.get_array_type();

        // elements must fit in the target type
        match array.into_inner() {
            ArrayExpressionInner::Value(inline_array) => {
                let res = match target_inner_ty.clone() {
                    Type::Int => Ok(inline_array),
                    t => {
                        // try to convert all elements to the target type
                        inline_array
                            .into_iter()
                            .map(|v| {
                                TypedExpressionOrSpread::align_to_type(v, t.clone()).map_err(
                                    |(e, _)| match e {
                                        TypedExpressionOrSpread::Expression(e) => e,
                                        TypedExpressionOrSpread::Spread(a) => {
                                            TypedExpression::select(a.array, 0u32)
                                        }
                                    },
                                )
                            })
                            .collect::<Result<Vec<_>, _>>()
                            .map(|v| v.into())
                    }
                }?;

                let inner_ty = res.0[0].get_type().0;

                Ok(ArrayExpressionInner::Value(res).annotate(inner_ty, array_ty.size))
            }
            ArrayExpressionInner::Repeat(box e, box count) => {
                match target_inner_ty.clone() {
                    Type::Int => Ok(ArrayExpressionInner::Repeat(box e, box count)
                        .annotate(Type::Int, array_ty.size)),
                    // try to convert the repeated element to the target type
                    t => TypedExpression::align_to_type(e, t)
                        .map(|e| {
                            ArrayExpressionInner::Repeat(box e, box count)
                                .annotate(target_inner_ty, array_ty.size)
                        })
                        .map_err(|(e, _)| e),
                }
            }
            a => {
                if array_ty.ty.weak_eq(&target_inner_ty) {
                    Ok(a.annotate(*array_ty.ty, array_ty.size))
                } else {
                    Err(a.annotate(*array_ty.ty, array_ty.size).into())
                }
            }
        }
    }
}

impl<'ast, T> From<BigUint> for IntExpression<'ast, T> {
    fn from(v: BigUint) -> Self {
        IntExpression::Value(v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::Bn128Field;

    #[test]
    fn field_from_int() {
        let n: IntExpression<Bn128Field> = BigUint::from(42usize).into();
        let n_a: ArrayExpression<Bn128Field> =
            ArrayExpressionInner::Value(vec![n.clone().into()].into()).annotate(Type::Int, 1u32);
        let t: FieldElementExpression<Bn128Field> = Bn128Field::from(42).into();
        let t_a: ArrayExpression<Bn128Field> =
            ArrayExpressionInner::Value(vec![t.clone().into()].into())
                .annotate(Type::FieldElement, 1u32);
        let i: UExpression<Bn128Field> = 42u32.into();
        let c: BooleanExpression<Bn128Field> = true.into();

        let expressions = vec![
            n.clone(),
            n.clone() + n.clone(),
            n.clone() - n.clone(),
            n.clone() * n.clone(),
            IntExpression::pow(n.clone(), n.clone()),
            n.clone() / n.clone(),
            IntExpression::if_else(c.clone(), n.clone(), n.clone()),
            IntExpression::select(n_a.clone(), i.clone()),
        ];

        let expected = vec![
            t.clone(),
            t.clone() + t.clone(),
            t.clone() - t.clone(),
            t.clone() * t.clone(),
            FieldElementExpression::pow(t.clone(), i.clone()),
            t.clone() / t.clone(),
            FieldElementExpression::if_else(c.clone(), t.clone(), t.clone()),
            FieldElementExpression::select(t_a.clone(), i.clone()),
        ];

        assert_eq!(
            expressions
                .into_iter()
                .map(|e| FieldElementExpression::try_from_int(e).unwrap())
                .collect::<Vec<_>>(),
            expected
        );

        let should_error = vec![
            BigUint::parse_bytes(b"99999999999999999999999999999999999999999999999999999999999999999999999999999999999", 10).unwrap().into(),
            IntExpression::xor(n.clone(), n.clone()),
            IntExpression::or(n.clone(), n.clone()),
            IntExpression::and(n.clone(), n.clone()),
            IntExpression::left_shift(n.clone(), i.clone()),
            IntExpression::right_shift(n.clone(), i.clone()),
            IntExpression::not(n.clone()),
        ];

        for e in should_error
            .into_iter()
            .map(FieldElementExpression::try_from_int)
        {
            assert!(e.is_err());
        }
    }

    #[test]
    fn uint_from_int() {
        let n: IntExpression<Bn128Field> = BigUint::from(42usize).into();
        let n_a: ArrayExpression<Bn128Field> =
            ArrayExpressionInner::Value(vec![n.clone().into()].into()).annotate(Type::Int, 1u32);
        let t: UExpression<Bn128Field> = 42u32.into();
        let t_a: ArrayExpression<Bn128Field> =
            ArrayExpressionInner::Value(vec![t.clone().into()].into())
                .annotate(Type::Uint(UBitwidth::B32), 1u32);
        let i: UExpression<Bn128Field> = 0u32.into();
        let c: BooleanExpression<Bn128Field> = true.into();

        let expressions = vec![
            n.clone(),
            n.clone() + n.clone(),
            IntExpression::xor(n.clone(), n.clone()),
            IntExpression::or(n.clone(), n.clone()),
            IntExpression::and(n.clone(), n.clone()),
            n.clone() - n.clone(),
            n.clone() * n.clone(),
            n.clone() / n.clone(),
            n.clone() % n.clone(),
            IntExpression::left_shift(n.clone(), i.clone()),
            IntExpression::right_shift(n.clone(), i.clone()),
            !n.clone(),
            IntExpression::if_else(c.clone(), n.clone(), n.clone()),
            IntExpression::select(n_a.clone(), i.clone()),
        ];

        let expected = vec![
            t.clone(),
            t.clone() + t.clone(),
            UExpression::xor(t.clone(), t.clone()),
            UExpression::or(t.clone(), t.clone()),
            UExpression::and(t.clone(), t.clone()),
            t.clone() - t.clone(),
            t.clone() * t.clone(),
            t.clone() / t.clone(),
            t.clone() % t.clone(),
            UExpression::left_shift(t.clone(), i.clone()),
            UExpression::right_shift(t.clone(), i.clone()),
            !t.clone(),
            UExpression::if_else(c.clone(), t.clone(), t.clone()),
            UExpression::select(t_a.clone(), i.clone()),
        ];

        for (r, e) in expressions
            .into_iter()
            .map(|e| UExpression::try_from_int(e, UBitwidth::B32).unwrap())
            .zip(expected)
        {
            assert_eq!(r, e);
        }

        let should_error = vec![
            BigUint::parse_bytes(b"99999999999999999999999999999999999999999999999999999999999999999999999999999999999", 10).unwrap().into(),
            IntExpression::pow(n.clone(), n.clone()),
        ];

        for e in should_error
            .into_iter()
            .map(|e| UExpression::try_from_int(e, UBitwidth::B32))
        {
            assert!(e.is_err());
        }
    }
}
