use crate::typed::types::{
    ArrayType, DeclarationArrayType, DeclarationConstant, DeclarationStructMember,
    DeclarationStructType, DeclarationTupleType, DeclarationType, GArrayType, GStructType,
    GTupleType, GType, GenericIdentifier, StructType, TupleType, Type,
};
use crate::typed::UBitwidth;
use crate::typed::{
    ArrayExpression, ArrayExpressionInner, BooleanExpression, Conditional, ConditionalExpression,
    Expr, FieldElementExpression, Select, SelectExpression, StructExpression,
    StructExpressionInner, TupleExpression, TupleExpressionInner, Typed, TypedExpression,
    TypedExpressionOrSpread, TypedSpread, UExpression,
};

use crate::common::{operators::*, WithSpan};

use num_bigint::BigUint;
use std::convert::TryFrom;
use std::fmt;
use std::ops::*;
use zokrates_field::Field;

use crate::common::expressions::*;

use super::{ArrayValueExpression, RepeatExpression};

type TypedExpressionPair<'ast, T> = (TypedExpression<'ast, T>, TypedExpression<'ast, T>);

impl<'ast, T: Field> TypedExpressionOrSpread<'ast, T> {
    pub fn align_to_type<S: PartialEq<UExpression<'ast, T>>>(
        e: Self,
        ty: &GArrayType<S>,
    ) -> Result<Self, (Self, &GArrayType<S>)> {
        match e {
            TypedExpressionOrSpread::Expression(e) => TypedExpression::align_to_type(e, &ty.ty)
                .map(|e| e.into())
                .map_err(|(e, _)| (e.into(), ty)),
            TypedExpressionOrSpread::Spread(s) => ArrayExpression::try_from_int(s.array, ty)
                .map(|e| TypedExpressionOrSpread::Spread(TypedSpread { array: e }))
                .map_err(|e| (e.into(), ty)),
        }
    }
}

trait IntegerInference: Sized {
    type Pattern;

    fn get_common_pattern(self, other: Self) -> Result<Self::Pattern, (Self, Self)>;
}

impl<'ast, T: Clone> IntegerInference for Type<'ast, T> {
    type Pattern = DeclarationType<'ast, T>;

    fn get_common_pattern(self, other: Self) -> Result<Self::Pattern, (Self, Self)> {
        match (self, other) {
            (Type::Boolean, Type::Boolean) => Ok(DeclarationType::Boolean),
            (Type::Int, Type::Int) => Err((Type::Int, Type::Int)),
            (Type::Int, Type::FieldElement) => Ok(DeclarationType::FieldElement),
            (Type::Int, Type::Uint(bitwidth)) => Ok(DeclarationType::Uint(bitwidth)),
            (Type::FieldElement, Type::Int) => Ok(DeclarationType::FieldElement),
            (Type::Uint(bitwidth), Type::Int) => Ok(DeclarationType::Uint(bitwidth)),
            (Type::FieldElement, Type::FieldElement) => Ok(DeclarationType::FieldElement),
            (Type::Uint(b0), Type::Uint(b1)) => {
                if b0 == b1 {
                    Ok(DeclarationType::Uint(b0))
                } else {
                    Err((Type::Uint(b0), Type::Uint(b1)))
                }
            }
            (Type::Array(t), Type::Array(u)) => Ok(DeclarationType::Array(
                t.get_common_pattern(u)
                    .map_err(|(t, u)| (Type::Array(t), Type::Array(u)))?,
            )),
            (Type::Struct(t), Type::Struct(u)) => Ok(DeclarationType::Struct(
                t.get_common_pattern(u)
                    .map_err(|(t, u)| (Type::Struct(t), Type::Struct(u)))?,
            )),
            (Type::Tuple(t), Type::Tuple(u)) => Ok(DeclarationType::Tuple(
                t.get_common_pattern(u)
                    .map_err(|(t, u)| (Type::Tuple(t), Type::Tuple(u)))?,
            )),
            (t, u) => Err((t, u)),
        }
    }
}

impl<'ast, T: Clone> IntegerInference for ArrayType<'ast, T> {
    type Pattern = DeclarationArrayType<'ast, T>;

    fn get_common_pattern(self, other: Self) -> Result<Self::Pattern, (Self, Self)> {
        let s0 = self.size;
        let s1 = other.size;

        Ok(DeclarationArrayType::new(
            self.ty
                .get_common_pattern(*other.ty)
                .map_err(|(t, u)| (ArrayType::new(t, *s0), ArrayType::new(u, *s1)))?,
            DeclarationConstant::Generic(GenericIdentifier::with_name("DUMMY")), // sizes are not checked at this stage, therefore we insert a dummy generic variable which will be equal to all possible sizes
        ))
    }
}

impl<'ast, T: Clone> IntegerInference for StructType<'ast, T> {
    type Pattern = DeclarationStructType<'ast, T>;

    fn get_common_pattern(self, other: Self) -> Result<Self::Pattern, (Self, Self)> {
        Ok(DeclarationStructType {
            members: self
                .members
                .into_iter()
                .zip(other.members.into_iter())
                .map(|(m_t, m_u)| match m_t.ty.get_common_pattern(*m_u.ty) {
                    Ok(ty) => DeclarationStructMember {
                        ty: Box::new(ty),
                        id: m_t.id,
                    },
                    Err(..) => unreachable!(
                        "struct instances of the same struct should always have a common type"
                    ),
                })
                .collect::<Vec<_>>(),
            canonical_location: self.canonical_location,
            location: self.location,
            generics: self
                .generics
                .into_iter()
                .map(|g| {
                    g.map(|_| DeclarationConstant::Generic(GenericIdentifier::with_name("DUMMY")))
                })
                .collect(),
        })
    }
}

impl<'ast, T: Clone> IntegerInference for TupleType<'ast, T> {
    type Pattern = DeclarationTupleType<'ast, T>;

    fn get_common_pattern(self, other: Self) -> Result<Self::Pattern, (Self, Self)> {
        Ok(DeclarationTupleType {
            elements: self
                .elements
                .iter()
                .zip(other.elements.iter())
                .map(|(t, u)| t.clone().get_common_pattern(u.clone()))
                .collect::<Result<Vec<_>, _>>()
                .map_err(|_| (self, other))?,
        })
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
                UExpression::try_from_int(lhs, &rhs.bitwidth())
                    .map_err(|lhs| (lhs.into(), rhs.clone().into()))?
                    .into(),
                Uint(rhs),
            )),
            (Uint(lhs), Int(rhs)) => {
                let bitwidth = lhs.bitwidth();
                Ok((
                    Uint(lhs.clone()),
                    UExpression::try_from_int(rhs, &bitwidth)
                        .map_err(|rhs| (lhs.into(), rhs.into()))?
                        .into(),
                ))
            }
            (Array(lhs), Array(rhs)) => {
                let common_type = lhs
                    .get_type()
                    .get_common_pattern(rhs.get_type())
                    .map_err(|_| (lhs.clone().into(), rhs.clone().into()))?;

                let common_type = match common_type {
                    DeclarationType::Array(ty) => ty,
                    _ => unreachable!(),
                };

                Ok((
                    ArrayExpression::try_from_int(lhs.clone(), &common_type)
                        .map_err(|lhs| (lhs.clone(), rhs.clone().into()))?
                        .into(),
                    ArrayExpression::try_from_int(rhs, &common_type)
                        .map_err(|rhs| (lhs.clone().into(), rhs.clone()))?
                        .into(),
                ))
            }
            (Struct(lhs), Struct(rhs)) => {
                let common_type = lhs
                    .get_type()
                    .get_common_pattern(rhs.get_type())
                    .map_err(|_| (lhs.clone().into(), rhs.clone().into()))?;

                let common_type = match common_type {
                    DeclarationType::Struct(ty) => ty,
                    _ => unreachable!(),
                };

                Ok((
                    StructExpression::try_from_int(lhs.clone(), &common_type)
                        .map_err(|lhs| (lhs.clone(), rhs.clone().into()))?
                        .into(),
                    StructExpression::try_from_int(rhs, &common_type)
                        .map_err(|rhs| (lhs.clone().into(), rhs.clone()))?
                        .into(),
                ))
            }
            (Tuple(lhs), Tuple(rhs)) => {
                let common_type = lhs
                    .get_type()
                    .get_common_pattern(rhs.get_type())
                    .map_err(|_| (lhs.clone().into(), rhs.clone().into()))?;

                let common_type = match common_type {
                    DeclarationType::Tuple(ty) => ty,
                    _ => unreachable!(),
                };

                Ok((
                    TupleExpression::try_from_int(lhs.clone(), &common_type)
                        .map_err(|lhs| (lhs.clone(), rhs.clone().into()))?
                        .into(),
                    TupleExpression::try_from_int(rhs, &common_type)
                        .map_err(|rhs| (lhs.clone().into(), rhs.clone()))?
                        .into(),
                ))
            }
            (Uint(lhs), Uint(rhs)) => Ok((lhs.into(), rhs.into())),
            (Boolean(lhs), Boolean(rhs)) => Ok((lhs.into(), rhs.into())),
            (FieldElement(lhs), FieldElement(rhs)) => Ok((lhs.into(), rhs.into())),
            (Int(lhs), Int(rhs)) => Ok((lhs.into(), rhs.into())),
            (lhs, rhs) => Err((lhs, rhs)),
        }
    }

    pub fn align_to_type<S: PartialEq<UExpression<'ast, T>>>(
        e: Self,
        ty: &GType<S>,
    ) -> Result<Self, (Self, &GType<S>)> {
        match ty {
            GType::FieldElement => {
                FieldElementExpression::try_from_typed(e).map(TypedExpression::from)
            }
            GType::Boolean => BooleanExpression::try_from_typed(e).map(TypedExpression::from),
            GType::Uint(bitwidth) => {
                UExpression::try_from_typed(e, bitwidth).map(TypedExpression::from)
            }
            GType::Array(array_ty) => {
                ArrayExpression::try_from_typed(e, array_ty).map(TypedExpression::from)
            }
            GType::Struct(struct_ty) => {
                StructExpression::try_from_typed(e, struct_ty).map(TypedExpression::from)
            }
            GType::Tuple(tuple_ty) => {
                TupleExpression::try_from_typed(e, tuple_ty).map(TypedExpression::from)
            }
            GType::Int => Err(e),
        }
        .map_err(|e| (e, ty))
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum IntExpression<'ast, T> {
    Value(IntValueExpression),
    Pos(UnaryExpression<OpPos, IntExpression<'ast, T>, IntExpression<'ast, T>>),
    Neg(UnaryExpression<OpNeg, IntExpression<'ast, T>, IntExpression<'ast, T>>),
    Not(UnaryExpression<OpNot, IntExpression<'ast, T>, IntExpression<'ast, T>>),
    Add(
        BinaryExpression<
            OpAdd,
            IntExpression<'ast, T>,
            IntExpression<'ast, T>,
            IntExpression<'ast, T>,
        >,
    ),
    Sub(
        BinaryExpression<
            OpSub,
            IntExpression<'ast, T>,
            IntExpression<'ast, T>,
            IntExpression<'ast, T>,
        >,
    ),
    Mult(
        BinaryExpression<
            OpMul,
            IntExpression<'ast, T>,
            IntExpression<'ast, T>,
            IntExpression<'ast, T>,
        >,
    ),
    Div(
        BinaryExpression<
            OpDiv,
            IntExpression<'ast, T>,
            IntExpression<'ast, T>,
            IntExpression<'ast, T>,
        >,
    ),
    Rem(
        BinaryExpression<
            OpRem,
            IntExpression<'ast, T>,
            IntExpression<'ast, T>,
            IntExpression<'ast, T>,
        >,
    ),
    Pow(
        BinaryExpression<
            OpPow,
            IntExpression<'ast, T>,
            IntExpression<'ast, T>,
            IntExpression<'ast, T>,
        >,
    ),
    Xor(
        BinaryExpression<
            OpXor,
            IntExpression<'ast, T>,
            IntExpression<'ast, T>,
            IntExpression<'ast, T>,
        >,
    ),
    And(
        BinaryExpression<
            OpAnd,
            IntExpression<'ast, T>,
            IntExpression<'ast, T>,
            IntExpression<'ast, T>,
        >,
    ),
    Or(
        BinaryExpression<
            OpOr,
            IntExpression<'ast, T>,
            IntExpression<'ast, T>,
            IntExpression<'ast, T>,
        >,
    ),
    LeftShift(
        BinaryExpression<
            OpLsh,
            IntExpression<'ast, T>,
            UExpression<'ast, T>,
            IntExpression<'ast, T>,
        >,
    ),
    RightShift(
        BinaryExpression<
            OpRsh,
            IntExpression<'ast, T>,
            UExpression<'ast, T>,
            IntExpression<'ast, T>,
        >,
    ),
    Conditional(ConditionalExpression<'ast, T, IntExpression<'ast, T>>),
    Select(SelectExpression<'ast, T, IntExpression<'ast, T>>),
}

impl<'ast, T> Add for IntExpression<'ast, T> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        IntExpression::Add(BinaryExpression::new(self, other))
    }
}

impl<'ast, T> Sub for IntExpression<'ast, T> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        IntExpression::Sub(BinaryExpression::new(self, other))
    }
}

impl<'ast, T> Mul for IntExpression<'ast, T> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        IntExpression::Mult(BinaryExpression::new(self, other))
    }
}

impl<'ast, T> Div for IntExpression<'ast, T> {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        IntExpression::Div(BinaryExpression::new(self, other))
    }
}

impl<'ast, T> Rem for IntExpression<'ast, T> {
    type Output = Self;

    fn rem(self, other: Self) -> Self {
        IntExpression::Rem(BinaryExpression::new(self, other))
    }
}

impl<'ast, T> Not for IntExpression<'ast, T> {
    type Output = Self;

    fn not(self) -> Self {
        IntExpression::Not(UnaryExpression::new(self))
    }
}

impl<'ast, T> Neg for IntExpression<'ast, T> {
    type Output = Self;

    fn neg(self) -> Self {
        IntExpression::Neg(UnaryExpression::new(self))
    }
}

impl<'ast, T> IntExpression<'ast, T> {
    pub fn pow(self, other: Self) -> Self {
        IntExpression::Pow(BinaryExpression::new(self, other))
    }

    pub fn and(self, other: Self) -> Self {
        IntExpression::And(BinaryExpression::new(self, other))
    }

    pub fn xor(self, other: Self) -> Self {
        IntExpression::Xor(BinaryExpression::new(self, other))
    }

    pub fn or(self, other: Self) -> Self {
        IntExpression::Or(BinaryExpression::new(self, other))
    }

    pub fn left_shift(self, by: UExpression<'ast, T>) -> Self {
        IntExpression::LeftShift(BinaryExpression::new(self, by))
    }

    pub fn right_shift(self, by: UExpression<'ast, T>) -> Self {
        IntExpression::RightShift(BinaryExpression::new(self, by))
    }

    pub fn pos(self) -> Self {
        IntExpression::Pos(UnaryExpression::new(self))
    }
}

impl<'ast, T: fmt::Display> fmt::Display for IntExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            IntExpression::Value(ref v) => write!(f, "{}", v),
            IntExpression::Pos(ref e) => write!(f, "{}", e),
            IntExpression::Neg(ref e) => write!(f, "{}", e),
            IntExpression::Div(ref e) => write!(f, "{}", e),
            IntExpression::Rem(ref e) => write!(f, "{}", e),
            IntExpression::Pow(ref e) => write!(f, "{}", e),
            IntExpression::Select(ref select) => write!(f, "{}", select),
            IntExpression::Add(ref e) => write!(f, "{}", e),
            IntExpression::And(ref e) => write!(f, "{}", e),
            IntExpression::Or(ref e) => write!(f, "{}", e),
            IntExpression::Xor(ref e) => write!(f, "{}", e),
            IntExpression::Sub(ref e) => write!(f, "{}", e),
            IntExpression::Mult(ref e) => write!(f, "{}", e),
            IntExpression::RightShift(ref e) => write!(f, "{}", e),
            IntExpression::LeftShift(ref e) => write!(f, "{}", e),
            IntExpression::Not(ref e) => write!(f, "{}", e),
            IntExpression::Conditional(ref c) => write!(f, "{}", c),
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
        let span = i.get_span();

        match i {
            IntExpression::Value(i) => Ok(Self::Value(ValueExpression::new(
                T::try_from(i.value.clone()).map_err(|_| IntExpression::Value(i))?,
            ))),
            IntExpression::Add(e) => Ok(Self::add(
                Self::try_from_int(*e.left)?,
                Self::try_from_int(*e.right)?,
            )),
            IntExpression::Sub(e) => Ok(Self::sub(
                Self::try_from_int(*e.left)?,
                Self::try_from_int(*e.right)?,
            )),
            IntExpression::Mult(e) => Ok(Self::mul(
                Self::try_from_int(*e.left)?,
                Self::try_from_int(*e.right)?,
            )),
            IntExpression::Pow(e) => Ok(Self::pow(
                Self::try_from_int(*e.left)?,
                UExpression::try_from_int(*e.right, &UBitwidth::B32)?,
            )),
            IntExpression::Div(e) => Ok(Self::div(
                Self::try_from_int(*e.left)?,
                Self::try_from_int(*e.right)?,
            )),
            IntExpression::And(e) => Ok(Self::bitand(
                Self::try_from_int(*e.left)?,
                Self::try_from_int(*e.right)?,
            )),
            IntExpression::Or(e) => Ok(Self::bitor(
                Self::try_from_int(*e.left)?,
                Self::try_from_int(*e.right)?,
            )),
            IntExpression::Xor(e) => Ok(Self::bitxor(
                Self::try_from_int(*e.left)?,
                Self::try_from_int(*e.right)?,
            )),
            IntExpression::LeftShift(e) => {
                Ok(Self::left_shift(Self::try_from_int(*e.left)?, *e.right))
            }
            IntExpression::RightShift(e) => {
                Ok(Self::right_shift(Self::try_from_int(*e.left)?, *e.right))
            }
            IntExpression::Pos(e) => Ok(Self::pos(Self::try_from_int(*e.inner)?)),
            IntExpression::Neg(e) => Ok(Self::neg(Self::try_from_int(*e.inner)?)),
            IntExpression::Conditional(c) => Ok(Self::Conditional(ConditionalExpression::new(
                *c.condition,
                Self::try_from_int(*c.consequence)?,
                Self::try_from_int(*c.alternative)?,
                c.kind,
            ))),
            IntExpression::Select(select) => {
                let array = *select.array;
                let index = *select.index;

                let size = array.size();

                match array.into_inner() {
                    ArrayExpressionInner::Value(values) => {
                        let values = values
                            .value
                            .into_iter()
                            .map(|v| {
                                TypedExpressionOrSpread::align_to_type(
                                    v,
                                    &DeclarationArrayType::new(
                                        DeclarationType::FieldElement,
                                        DeclarationConstant::from(0u32),
                                    ),
                                )
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
                            ArrayExpression::value(values)
                                .annotate(ArrayType::new(Type::FieldElement, size)),
                            index,
                        ))
                    }
                    _ => unreachable!(),
                }
            }
            i => Err(i),
        }
        .map(|e| e.span(span))
    }
}

impl<'ast, T: Field> UExpression<'ast, T> {
    pub fn try_from_typed(
        e: TypedExpression<'ast, T>,
        bitwidth: &UBitwidth,
    ) -> Result<Self, TypedExpression<'ast, T>> {
        match e {
            TypedExpression::Uint(e) => match e.bitwidth == *bitwidth {
                true => Ok(e),
                _ => Err(TypedExpression::Uint(e)),
            },
            TypedExpression::Int(e) => {
                Self::try_from_int(e, bitwidth).map_err(TypedExpression::Int)
            }
            e => Err(e),
        }
    }

    pub fn try_from_int(
        i: IntExpression<'ast, T>,
        bitwidth: &UBitwidth,
    ) -> Result<Self, IntExpression<'ast, T>> {
        use self::IntExpression::*;

        let span = i.get_span();

        match i {
            Value(i) => {
                if i.value <= BigUint::from(2u128.pow(bitwidth.to_usize() as u32) - 1) {
                    Ok(UExpression::value(
                        u128::from_str_radix(&i.value.to_str_radix(16), 16).unwrap(),
                    )
                    .annotate(*bitwidth))
                } else {
                    Err(Value(i))
                }
            }
            Add(e) => Ok(
                Self::try_from_int(*e.left, bitwidth)? + Self::try_from_int(*e.right, bitwidth)?
            ),
            Pos(e) => Ok(Self::pos(Self::try_from_int(*e.inner, bitwidth)?)),
            Neg(e) => Ok(Self::neg(Self::try_from_int(*e.inner, bitwidth)?)),
            Sub(e) => Ok(
                Self::try_from_int(*e.left, bitwidth)? - Self::try_from_int(*e.right, bitwidth)?
            ),
            Mult(e) => Ok(
                Self::try_from_int(*e.left, bitwidth)? * Self::try_from_int(*e.right, bitwidth)?
            ),
            Div(e) => Ok(
                Self::try_from_int(*e.left, bitwidth)? / Self::try_from_int(*e.right, bitwidth)?
            ),
            Rem(e) => Ok(
                Self::try_from_int(*e.left, bitwidth)? % Self::try_from_int(*e.right, bitwidth)?
            ),
            And(e) => Ok(UExpression::and(
                Self::try_from_int(*e.left, bitwidth)?,
                Self::try_from_int(*e.right, bitwidth)?,
            )),
            Or(e) => Ok(UExpression::or(
                Self::try_from_int(*e.left, bitwidth)?,
                Self::try_from_int(*e.right, bitwidth)?,
            )),
            Not(e) => Ok(!Self::try_from_int(*e.inner, bitwidth)?),
            Xor(e) => Ok(UExpression::xor(
                Self::try_from_int(*e.left, bitwidth)?,
                Self::try_from_int(*e.right, bitwidth)?,
            )),
            RightShift(e) => Ok(UExpression::right_shift(
                Self::try_from_int(*e.left, bitwidth)?,
                *e.right,
            )),
            LeftShift(e) => Ok(UExpression::left_shift(
                Self::try_from_int(*e.left, bitwidth)?,
                *e.right,
            )),
            Conditional(c) => Ok(UExpression::conditional(
                *c.condition,
                Self::try_from_int(*c.consequence, bitwidth)?,
                Self::try_from_int(*c.alternative, bitwidth)?,
                c.kind,
            )),
            Select(select) => {
                let array = *select.array;
                let index = *select.index;

                let size = array.size();
                match array.into_inner() {
                    ArrayExpressionInner::Value(values) => {
                        let values = values
                            .value
                            .into_iter()
                            .map(|v| {
                                TypedExpressionOrSpread::align_to_type(
                                    v,
                                    &DeclarationArrayType::new(
                                        DeclarationType::Uint(*bitwidth),
                                        DeclarationConstant::from(0u32),
                                    ),
                                )
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
                            ArrayExpression::value(values)
                                .annotate(ArrayType::new(Type::Uint(*bitwidth), size)),
                            index,
                        ))
                    }
                    _ => unreachable!(),
                }
            }
            i => Err(i),
        }
        .map(|e| e.span(span))
    }
}

impl<'ast, T: Field> ArrayExpression<'ast, T> {
    pub fn try_from_typed<S: PartialEq<UExpression<'ast, T>>>(
        e: TypedExpression<'ast, T>,
        target_array_ty: &GArrayType<S>,
    ) -> Result<Self, TypedExpression<'ast, T>> {
        match e {
            TypedExpression::Array(e) => Self::try_from_int(e, target_array_ty),
            e => Err(e),
        }
    }

    // precondition: `array` is only made of inline arrays and repeat constructs unless it does not contain the Integer type
    pub fn try_from_int<S: PartialEq<UExpression<'ast, T>>>(
        array: Self,
        target_array_ty: &GArrayType<S>,
    ) -> Result<Self, TypedExpression<'ast, T>> {
        let span = array.get_span();

        let array_ty = array.ty().clone();

        // elements must fit in the target type
        match array.into_inner() {
            ArrayExpressionInner::Value(inline_array) => {
                let res = match &*target_array_ty.ty {
                    GType::Int => Ok(inline_array),
                    _ => {
                        // try to convert all elements to the target type
                        inline_array
                            .value
                            .into_iter()
                            .map(|v| {
                                TypedExpressionOrSpread::align_to_type(v, target_array_ty).map_err(
                                    |(e, _)| match e {
                                        TypedExpressionOrSpread::Expression(e) => e,
                                        TypedExpressionOrSpread::Spread(a) => {
                                            TypedExpression::select(a.array, 0u32)
                                        }
                                    },
                                )
                            })
                            .collect::<Result<Vec<_>, _>>()
                            .map(ArrayValueExpression::new)
                    }
                }?;

                let inner_ty = res.value[0].get_type().0;

                let array_ty = ArrayType::new(inner_ty, *array_ty.size);

                Ok(ArrayExpressionInner::Value(res).annotate(array_ty))
            }
            ArrayExpressionInner::Repeat(r) => {
                match &*target_array_ty.ty {
                    GType::Int => {
                        let array_ty = ArrayType::new(Type::Int, *array_ty.size);

                        Ok(ArrayExpressionInner::Repeat(r).annotate(array_ty))
                    }
                    // try to align the repeated element to the target type
                    t => TypedExpression::align_to_type(*r.e, t)
                        .map(|e| {
                            let ty = e.get_type().clone();

                            ArrayExpressionInner::Repeat(RepeatExpression::new(e, *r.count))
                                .annotate(ArrayType::new(ty, *array_ty.size))
                        })
                        .map_err(|(e, _)| e),
                }
            }
            a => {
                if *target_array_ty.ty == *array_ty.ty {
                    Ok(a.annotate(array_ty))
                } else {
                    Err(a.annotate(array_ty).into())
                }
            }
        }
        .map(|e| e.span(span))
    }
}

impl<'ast, T: Field> StructExpression<'ast, T> {
    pub fn try_from_int<S: PartialEq<UExpression<'ast, T>>>(
        struc: Self,
        target_struct_ty: &GStructType<S>,
    ) -> Result<Self, TypedExpression<'ast, T>> {
        let span = struc.get_span();

        let struct_ty = struc.ty().clone();

        if struct_ty.members.len() != target_struct_ty.members.len() {
            return Err(struc.into());
        }

        match struc.into_inner() {
            StructExpressionInner::Value(inline_struct) => inline_struct
                .into_iter()
                .zip(target_struct_ty.members.iter())
                .map(|(value, target_member)| {
                    TypedExpression::align_to_type(value, &*target_member.ty)
                })
                .collect::<Result<Vec<_>, _>>()
                .map(|v| StructExpression::value(v).annotate(struct_ty.clone()))
                .map_err(|(v, _)| v),
            s => {
                if struct_ty
                    .members
                    .iter()
                    .zip(target_struct_ty.members.iter())
                    .all(|(m, target_m)| *target_m.ty == *m.ty)
                {
                    Ok(s.annotate(struct_ty))
                } else {
                    Err(s.annotate(struct_ty).into())
                }
            }
        }
        .map(|e| e.span(span))
    }

    pub fn try_from_typed<S: PartialEq<UExpression<'ast, T>>>(
        e: TypedExpression<'ast, T>,
        target_struct_ty: &GStructType<S>,
    ) -> Result<Self, TypedExpression<'ast, T>> {
        match e {
            TypedExpression::Struct(e) => Self::try_from_int(e, target_struct_ty),
            e => Err(e),
        }
    }
}

impl<'ast, T: Field> TupleExpression<'ast, T> {
    pub fn try_from_int<S: PartialEq<UExpression<'ast, T>>>(
        tuple: Self,
        target_tuple_ty: &GTupleType<S>,
    ) -> Result<Self, TypedExpression<'ast, T>> {
        let span = tuple.get_span();

        let tuple_ty = tuple.ty().clone();

        if tuple_ty.elements.len() != target_tuple_ty.elements.len() {
            return Err(tuple.into());
        }

        match tuple.into_inner() {
            TupleExpressionInner::Value(inline_tuple) => inline_tuple
                .into_iter()
                .zip(target_tuple_ty.elements.iter())
                .map(|(value, target_ty)| TypedExpression::align_to_type(value, target_ty))
                .collect::<Result<Vec<_>, _>>()
                .map(|v| {
                    let ty = TupleType::new(v.iter().map(|e| e.get_type()).collect());
                    TupleExpression::value(v).annotate(ty)
                })
                .map_err(|(v, _)| v),
            s => {
                if tuple_ty
                    .elements
                    .iter()
                    .zip(target_tuple_ty.elements.iter())
                    .all(|(t, target_t)| *target_t == *t)
                {
                    Ok(s.annotate(tuple_ty))
                } else {
                    Err(s.annotate(tuple_ty).into())
                }
            }
        }
        .map(|e| e.span(span))
    }

    pub fn try_from_typed<S: PartialEq<UExpression<'ast, T>>>(
        e: TypedExpression<'ast, T>,
        target_tuple_ty: &GTupleType<S>,
    ) -> Result<Self, TypedExpression<'ast, T>> {
        match e {
            TypedExpression::Tuple(e) => Self::try_from_int(e, target_tuple_ty),
            e => Err(e),
        }
    }
}

impl<'ast, T: Field> From<BigUint> for IntExpression<'ast, T> {
    fn from(v: BigUint) -> Self {
        IntExpression::value(v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typed::ConditionalKind;
    use zokrates_field::Bn128Field;

    #[test]
    fn field_from_int() {
        let n: IntExpression<Bn128Field> = BigUint::from(42usize).into();
        let n_a: ArrayExpression<Bn128Field> =
            ArrayExpressionInner::Value(ValueExpression::new(vec![n.clone().into()]))
                .annotate(ArrayType::new(Type::Int, 1u32));
        let t: FieldElementExpression<Bn128Field> = Bn128Field::from(42).into();
        let t_a: ArrayExpression<Bn128Field> =
            ArrayExpressionInner::Value(ValueExpression::new(vec![t.clone().into()]))
                .annotate(ArrayType::new(Type::FieldElement, 1u32));

        let i: UExpression<Bn128Field> = 42u32.into();
        let c: BooleanExpression<Bn128Field> = true.into();

        let expressions = vec![
            n.clone(),
            n.clone() + n.clone(),
            n.clone() - n.clone(),
            n.clone() * n.clone(),
            IntExpression::pow(n.clone(), n.clone()),
            n.clone() / n.clone(),
            IntExpression::conditional(c.clone(), n.clone(), n.clone(), ConditionalKind::IfElse),
            IntExpression::select(n_a.clone(), i.clone()),
        ];

        let expected = vec![
            t.clone(),
            t.clone() + t.clone(),
            t.clone() - t.clone(),
            t.clone() * t.clone(),
            FieldElementExpression::pow(t.clone(), i.clone()),
            t.clone() / t.clone(),
            FieldElementExpression::conditional(
                c.clone(),
                t.clone(),
                t.clone(),
                ConditionalKind::IfElse,
            ),
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
            ArrayExpressionInner::Value(ValueExpression::new(vec![n.clone().into()]))
                .annotate(ArrayType::new(Type::Int, 1u32));
        let t: UExpression<Bn128Field> = 42u32.into();
        let t_a: ArrayExpression<Bn128Field> =
            ArrayExpressionInner::Value(ValueExpression::new(vec![t.clone().into()]))
                .annotate(ArrayType::new(Type::Uint(UBitwidth::B32), 1u32));
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
            IntExpression::conditional(c.clone(), n.clone(), n.clone(), ConditionalKind::IfElse),
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
            UExpression::conditional(c.clone(), t.clone(), t.clone(), ConditionalKind::IfElse),
            UExpression::select(t_a.clone(), i.clone()),
        ];

        for (r, e) in expressions
            .into_iter()
            .map(|e| UExpression::try_from_int(e, &UBitwidth::B32).unwrap())
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
            .map(|e| UExpression::try_from_int(e, &UBitwidth::B32))
        {
            assert!(e.is_err());
        }
    }
}
