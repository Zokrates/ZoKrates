use crate::typed_absy::types::{ArrayType, Type};
use crate::typed_absy::UBitwidth;
use crate::typed_absy::{
    ArrayExpression, ArrayExpressionInner, BooleanExpression, FieldElementExpression, IfElse,
    Select, StructExpression, Typed, TypedExpression, UExpression, UExpressionInner,
};
use num_bigint::BigUint;
use std::convert::TryFrom;
use std::fmt;
use zokrates_field::Field;

impl<'ast, T: Field> TypedExpression<'ast, T> {
    // return two TypedExpression, replacing IntExpression by FieldElement or Uint to try to align the two types if possible.
    // Post condition is that (lhs, rhs) cannot be made equal by further removing IntExpressions
    pub fn align_without_integers(
        lhs: Self,
        rhs: Self,
    ) -> Result<
        (TypedExpression<'ast, T>, TypedExpression<'ast, T>),
        (TypedExpression<'ast, T>, TypedExpression<'ast, T>),
    > {
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
                if lhs.get_type() == rhs.get_type() {
                    Ok((Array(lhs), Array(rhs)))
                } else {
                    Err((Array(lhs), Array(rhs)))
                }
            }
            (Struct(lhs), Struct(rhs)) => {
                if lhs.get_type() == rhs.get_type() {
                    Ok((Struct(lhs).into(), Struct(rhs).into()))
                } else {
                    Err((Struct(lhs).into(), Struct(rhs).into()))
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
                ArrayExpression::try_from_typed(e, array_ty).map(TypedExpression::from)
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
    Add(Box<IntExpression<'ast, T>>, Box<IntExpression<'ast, T>>),
    Sub(Box<IntExpression<'ast, T>>, Box<IntExpression<'ast, T>>),
    Mult(Box<IntExpression<'ast, T>>, Box<IntExpression<'ast, T>>),
    Div(Box<IntExpression<'ast, T>>, Box<IntExpression<'ast, T>>),
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
    LeftShift(
        Box<IntExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    RightShift(
        Box<IntExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
}

impl<'ast, T> IntExpression<'ast, T> {
    pub fn add(self, other: Self) -> Self {
        IntExpression::Add(box self, box other)
    }

    pub fn sub(self, other: Self) -> Self {
        IntExpression::Sub(box self, box other)
    }

    pub fn mult(self, other: Self) -> Self {
        IntExpression::Mult(box self, box other)
    }

    pub fn div(self, other: Self) -> Self {
        IntExpression::Div(box self, box other)
    }

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

    pub fn left_shift(self, by: FieldElementExpression<'ast, T>) -> Self {
        IntExpression::LeftShift(box self, box by)
    }

    pub fn right_shift(self, by: FieldElementExpression<'ast, T>) -> Self {
        IntExpression::RightShift(box self, box by)
    }

    pub fn not(self) -> Self {
        IntExpression::Not(box self)
    }
}

impl<'ast, T: fmt::Display> fmt::Display for IntExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            IntExpression::Value(ref v) => write!(f, "{}", v),
            IntExpression::Div(ref lhs, ref rhs) => write!(f, "({} / {})", lhs, rhs),
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
            IntExpression::IfElse(box condition, box consequence, box alternative) => {
                Ok(Self::IfElse(
                    box condition,
                    box Self::try_from_int(consequence)?,
                    box Self::try_from_int(alternative)?,
                ))
            }
            IntExpression::Select(box array, box index) => match array.as_inner() {
                ArrayExpressionInner::Value(values) => {
                    let values = values
                        .into_iter()
                        .map(|v| {
                            FieldElementExpression::try_from_int(
                                IntExpression::try_from(v.clone()).unwrap(),
                            )
                            .map(TypedExpression::from)
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(FieldElementExpression::select(
                        ArrayExpressionInner::Value(values)
                            .annotate(Type::FieldElement, array.size),
                        index,
                    ))
                }
                _ => unreachable!(),
            },
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
            Add(box e1, box e2) => Ok(UExpression::add(
                Self::try_from_int(e1, bitwidth)?,
                Self::try_from_int(e2, bitwidth)?,
            )),
            Sub(box e1, box e2) => Ok(UExpression::sub(
                Self::try_from_int(e1, bitwidth)?,
                Self::try_from_int(e2, bitwidth)?,
            )),
            Mult(box e1, box e2) => Ok(UExpression::mult(
                Self::try_from_int(e1, bitwidth)?,
                Self::try_from_int(e2, bitwidth)?,
            )),
            And(box e1, box e2) => Ok(UExpression::and(
                Self::try_from_int(e1, bitwidth)?,
                Self::try_from_int(e2, bitwidth)?,
            )),
            Or(box e1, box e2) => Ok(UExpression::or(
                Self::try_from_int(e1, bitwidth)?,
                Self::try_from_int(e2, bitwidth)?,
            )),
            Not(box e) => Ok(UExpression::not(Self::try_from_int(e, bitwidth)?)),
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
            Select(box array, box index) => match array.as_inner() {
                ArrayExpressionInner::Value(values) => {
                    let values = values
                        .into_iter()
                        .map(|v| {
                            UExpression::try_from_int(
                                IntExpression::try_from(v.clone()).unwrap(),
                                bitwidth,
                            )
                            .map(TypedExpression::from)
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(UExpression::select(
                        ArrayExpressionInner::Value(values)
                            .annotate(Type::Uint(bitwidth), array.size),
                        index,
                    ))
                }
                _ => unreachable!(),
            },
            i => Err(i),
        }
    }
}

impl<'ast, T: Field> ArrayExpression<'ast, T> {
    pub fn try_from_typed(
        e: TypedExpression<'ast, T>,
        target_array_ty: ArrayType<'ast, T>,
    ) -> Result<Self, TypedExpression<'ast, T>> {
        match e {
            TypedExpression::Array(e) => Self::try_from_int(e.clone(), target_array_ty)
                .map_err(|_| TypedExpression::Array(e)),
            e => Err(e),
        }
    }

    // precondition: `array` is only made of inline arrays
    pub fn try_from_int(
        array: Self,
        target_array_ty: ArrayType<'ast, T>,
    ) -> Result<Self, TypedExpression<'ast, T>> {
        let array_ty = array.get_array_type();

        if array_ty.weak_eq(&target_array_ty) {
            return Ok(array);
        }

        // elements must fit in the target type
        let converted = match array.into_inner() {
            ArrayExpressionInner::Value(inline_array) => {
                match *target_array_ty.ty {
                    Type::Int => Ok(inline_array),
                    Type::FieldElement => {
                        // try to convert all elements to field
                        inline_array
                            .into_iter()
                            .map(|e| {
                                FieldElementExpression::try_from_typed(e).map(TypedExpression::from)
                            })
                            .collect::<Result<Vec<TypedExpression<'ast, T>>, _>>()
                            .map_err(TypedExpression::from)
                    }
                    Type::Uint(bitwidth) => {
                        // try to convert all elements to uint
                        inline_array
                            .into_iter()
                            .map(|e| {
                                UExpression::try_from_typed(e, bitwidth).map(TypedExpression::from)
                            })
                            .collect::<Result<Vec<TypedExpression<'ast, T>>, _>>()
                            .map_err(TypedExpression::from)
                    }
                    Type::Array(ref inner_array_ty) => {
                        // try to convert all elements to array
                        inline_array
                            .into_iter()
                            .map(|e| {
                                ArrayExpression::try_from_typed(e, inner_array_ty.clone())
                                    .map(TypedExpression::from)
                            })
                            .collect::<Result<Vec<TypedExpression<'ast, T>>, _>>()
                            .map_err(TypedExpression::from)
                    }
                    Type::Struct(ref struct_ty) => {
                        // try to convert all elements to struct
                        inline_array
                            .into_iter()
                            .map(|e| {
                                StructExpression::try_from_typed(e, struct_ty.clone())
                                    .map(TypedExpression::from)
                            })
                            .collect::<Result<Vec<TypedExpression<'ast, T>>, _>>()
                            .map_err(TypedExpression::from)
                    }
                    Type::Boolean => {
                        // try to convert all elements to boolean
                        inline_array
                            .into_iter()
                            .map(|e| {
                                BooleanExpression::try_from_typed(e).map(TypedExpression::from)
                            })
                            .collect::<Result<Vec<TypedExpression<'ast, T>>, _>>()
                            .map_err(TypedExpression::from)
                    }
                }
            }
            _ => unreachable!(),
        }?;

        Ok(ArrayExpressionInner::Value(converted).annotate(*target_array_ty.ty, array_ty.size))
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
            ArrayExpressionInner::Value(vec![n.clone().into()]).annotate(Type::Int, 1u32);
        let t: FieldElementExpression<Bn128Field> = Bn128Field::from(42).into();
        let t_a: ArrayExpression<Bn128Field> =
            ArrayExpressionInner::Value(vec![t.clone().into()]).annotate(Type::FieldElement, 1u32);
        let i: UExpression<Bn128Field> = 42u32.into();
        let s: FieldElementExpression<Bn128Field> = Bn128Field::from(0).into();
        let c: BooleanExpression<Bn128Field> = true.into();

        let expressions = vec![
            n.clone(),
            IntExpression::add(n.clone(), n.clone()),
            IntExpression::sub(n.clone(), n.clone()),
            IntExpression::mult(n.clone(), n.clone()),
            IntExpression::pow(n.clone(), n.clone()),
            IntExpression::div(n.clone(), n.clone()),
            IntExpression::if_else(c.clone(), n.clone(), n.clone()),
            IntExpression::select(n_a.clone(), i.clone()),
        ];

        let expected = vec![
            t.clone(),
            FieldElementExpression::add(t.clone(), t.clone()),
            FieldElementExpression::sub(t.clone(), t.clone()),
            FieldElementExpression::mult(t.clone(), t.clone()),
            FieldElementExpression::pow(t.clone(), i.clone()),
            FieldElementExpression::div(t.clone(), t.clone()),
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
            IntExpression::left_shift(n.clone(), s.clone()),
            IntExpression::right_shift(n.clone(), s.clone()),
            IntExpression::not(n.clone()),
        ];

        for e in should_error
            .into_iter()
            .map(|e| FieldElementExpression::try_from_int(e))
        {
            assert!(e.is_err());
        }
    }

    #[test]
    fn uint_from_int() {
        let n: IntExpression<Bn128Field> = BigUint::from(42usize).into();
        let n_a: ArrayExpression<Bn128Field> =
            ArrayExpressionInner::Value(vec![n.clone().into()]).annotate(Type::Int, 1u32);
        let t: UExpression<Bn128Field> = 42u32.into();
        let t_a: ArrayExpression<Bn128Field> = ArrayExpressionInner::Value(vec![t.clone().into()])
            .annotate(Type::Uint(UBitwidth::B32), 1u32);
        let i: UExpression<Bn128Field> = 0u32.into();
        let s: FieldElementExpression<Bn128Field> = Bn128Field::from(0).into();
        let c: BooleanExpression<Bn128Field> = true.into();

        let expressions = vec![
            n.clone(),
            IntExpression::add(n.clone(), n.clone()),
            IntExpression::xor(n.clone(), n.clone()),
            IntExpression::or(n.clone(), n.clone()),
            IntExpression::and(n.clone(), n.clone()),
            IntExpression::sub(n.clone(), n.clone()),
            IntExpression::mult(n.clone(), n.clone()),
            IntExpression::left_shift(n.clone(), s.clone()),
            IntExpression::right_shift(n.clone(), s.clone()),
            IntExpression::not(n.clone()),
            IntExpression::if_else(c.clone(), n.clone(), n.clone()),
            IntExpression::select(n_a.clone(), i.clone()),
        ];

        let expected = vec![
            t.clone(),
            UExpression::add(t.clone(), t.clone()),
            UExpression::xor(t.clone(), t.clone()),
            UExpression::or(t.clone(), t.clone()),
            UExpression::and(t.clone(), t.clone()),
            UExpression::sub(t.clone(), t.clone()),
            UExpression::mult(t.clone(), t.clone()),
            UExpression::left_shift(t.clone(), s.clone()),
            UExpression::right_shift(t.clone(), s.clone()),
            UExpression::not(t.clone()),
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
            IntExpression::div(n.clone(), n.clone()),
        ];

        for e in should_error
            .into_iter()
            .map(|e| UExpression::try_from_int(e, UBitwidth::B32))
        {
            assert!(e.is_err());
        }
    }
}
