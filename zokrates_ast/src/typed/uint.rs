use crate::typed::*;
use crate::{common::expressions::UValueExpression, typed::types::UBitwidth};
use std::ops::{Add, Div, Mul, Neg, Not, Rem, Sub};
use zokrates_field::Field;

type Bitwidth = usize;

impl<'ast, T> Add for UExpression<'ast, T> {
    type Output = Self;

    fn add(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);

        // we apply a basic simplification here which enables more precise comparison of array sizes during semantic checking
        // this could be done by the caller by calling propagation, but it is deemed simple enough to be done here
        match (self.as_inner(), other.as_inner()) {
            (UExpressionInner::Value(v), _) if v.value == 0 => other,
            (_, UExpressionInner::Value(v)) if v.value == 0 => self,
            _ => UExpressionInner::Add(BinaryExpression::new(self, other)).annotate(bitwidth),
        }
    }
}

impl<'ast, T> Sub for UExpression<'ast, T> {
    type Output = Self;

    fn sub(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Sub(BinaryExpression::new(self, other)).annotate(bitwidth)
    }
}

impl<'ast, T> Mul for UExpression<'ast, T> {
    type Output = Self;

    fn mul(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Mult(BinaryExpression::new(self, other)).annotate(bitwidth)
    }
}

impl<'ast, T> Div for UExpression<'ast, T> {
    type Output = Self;

    fn div(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Div(BinaryExpression::new(self, other)).annotate(bitwidth)
    }
}

impl<'ast, T> Rem for UExpression<'ast, T> {
    type Output = Self;

    fn rem(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Rem(BinaryExpression::new(self, other)).annotate(bitwidth)
    }
}

impl<'ast, T> Not for UExpression<'ast, T> {
    type Output = Self;

    fn not(self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        UExpressionInner::Not(UnaryExpression::new(self)).annotate(bitwidth)
    }
}

impl<'ast, T> Neg for UExpression<'ast, T> {
    type Output = Self;

    fn neg(self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        UExpressionInner::Neg(UnaryExpression::new(self)).annotate(bitwidth)
    }
}

impl<'ast, T: Field> UExpression<'ast, T> {
    pub fn xor(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Xor(BinaryExpression::new(self, other)).annotate(bitwidth)
    }

    pub fn or(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Or(BinaryExpression::new(self, other)).annotate(bitwidth)
    }

    pub fn and(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::And(BinaryExpression::new(self, other)).annotate(bitwidth)
    }

    pub fn pos(self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        UExpressionInner::Pos(UnaryExpression::new(self)).annotate(bitwidth)
    }

    pub fn left_shift(self, by: UExpression<'ast, T>) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(by.bitwidth, UBitwidth::B32);
        UExpressionInner::LeftShift(BinaryExpression::new(self, by)).annotate(bitwidth)
    }

    pub fn right_shift(self, by: UExpression<'ast, T>) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(by.bitwidth, UBitwidth::B32);
        UExpressionInner::RightShift(BinaryExpression::new(self, by)).annotate(bitwidth)
    }

    pub fn floor_sub(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::FloorSub(BinaryExpression::new(self, other)).annotate(bitwidth)
    }
}

impl<'ast, T> From<u128> for UExpressionInner<'ast, T> {
    fn from(e: u128) -> Self {
        UExpressionInner::Value(ValueExpression::new(e))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct UMetadata {
    pub bitwidth: Option<Bitwidth>,
    pub should_reduce: Option<bool>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct UExpression<'ast, T> {
    pub bitwidth: UBitwidth,
    pub metadata: Option<UMetadata>,
    pub inner: UExpressionInner<'ast, T>,
}

impl<'ast, T> From<u16> for UExpression<'ast, T> {
    fn from(u: u16) -> Self {
        UExpressionInner::Value(ValueExpression::new(u as u128)).annotate(UBitwidth::B16)
    }
}

impl<'ast, T> From<u8> for UExpression<'ast, T> {
    fn from(u: u8) -> Self {
        UExpressionInner::Value(ValueExpression::new(u as u128)).annotate(UBitwidth::B8)
    }
}

impl<'ast, T> PartialEq<u32> for UExpression<'ast, T> {
    fn eq(&self, other: &u32) -> bool {
        match self.as_inner() {
            UExpressionInner::Value(v) => v.value == *other as u128,
            _ => true,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum UExpressionInner<'ast, T> {
    Block(BlockExpression<'ast, T, UExpression<'ast, T>>),
    Identifier(IdentifierExpression<'ast, UExpression<'ast, T>>),
    Value(UValueExpression),
    Add(BinaryExpression<OpAdd, UExpression<'ast, T>, UExpression<'ast, T>, UExpression<'ast, T>>),
    Sub(BinaryExpression<OpSub, UExpression<'ast, T>, UExpression<'ast, T>, UExpression<'ast, T>>),
    FloorSub(
        BinaryExpression<
            OpFloorSub,
            UExpression<'ast, T>,
            UExpression<'ast, T>,
            UExpression<'ast, T>,
        >,
    ),
    Mult(BinaryExpression<OpMul, UExpression<'ast, T>, UExpression<'ast, T>, UExpression<'ast, T>>),
    Div(BinaryExpression<OpDiv, UExpression<'ast, T>, UExpression<'ast, T>, UExpression<'ast, T>>),
    Rem(BinaryExpression<OpRem, UExpression<'ast, T>, UExpression<'ast, T>, UExpression<'ast, T>>),
    Xor(BinaryExpression<OpXor, UExpression<'ast, T>, UExpression<'ast, T>, UExpression<'ast, T>>),
    And(BinaryExpression<OpAnd, UExpression<'ast, T>, UExpression<'ast, T>, UExpression<'ast, T>>),
    Or(BinaryExpression<OpOr, UExpression<'ast, T>, UExpression<'ast, T>, UExpression<'ast, T>>),
    Not(UnaryExpression<OpNot, UExpression<'ast, T>, UExpression<'ast, T>>),
    Neg(UnaryExpression<OpNeg, UExpression<'ast, T>, UExpression<'ast, T>>),
    Pos(UnaryExpression<OpPos, UExpression<'ast, T>, UExpression<'ast, T>>),
    FunctionCall(FunctionCallExpression<'ast, T, UExpression<'ast, T>>),
    LeftShift(
        BinaryExpression<OpLsh, UExpression<'ast, T>, UExpression<'ast, T>, UExpression<'ast, T>>,
    ),
    RightShift(
        BinaryExpression<OpRsh, UExpression<'ast, T>, UExpression<'ast, T>, UExpression<'ast, T>>,
    ),
    Conditional(ConditionalExpression<'ast, T, UExpression<'ast, T>>),
    Member(MemberExpression<'ast, T, UExpression<'ast, T>>),
    Select(SelectExpression<'ast, T, UExpression<'ast, T>>),
    Element(ElementExpression<'ast, T, UExpression<'ast, T>>),
}

impl<'ast, T> UExpressionInner<'ast, T> {
    pub fn annotate<W: Into<UBitwidth>>(self, bitwidth: W) -> UExpression<'ast, T> {
        UExpression {
            metadata: None,
            bitwidth: bitwidth.into(),
            inner: self,
        }
    }
}

impl<'ast, T> UExpression<'ast, T> {
    pub fn metadata(self, metadata: UMetadata) -> UExpression<'ast, T> {
        UExpression {
            metadata: Some(metadata),
            ..self
        }
    }
}

pub fn bitwidth(a: u128) -> Bitwidth {
    (128 - a.leading_zeros()) as Bitwidth
}

impl<'ast, T> UExpression<'ast, T> {
    pub fn bitwidth(&self) -> UBitwidth {
        self.bitwidth
    }

    pub fn as_inner(&self) -> &UExpressionInner<'ast, T> {
        &self.inner
    }

    pub fn into_inner(self) -> UExpressionInner<'ast, T> {
        self.inner
    }
}
