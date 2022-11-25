use crate::typed::types::UBitwidth;
use crate::typed::*;
use std::ops::{Add, Div, Mul, Neg, Not, Rem, Sub};
use zokrates_field::Field;

type Bitwidth = usize;

impl<I, T> Add for UExpression<I, T> {
    type Output = Self;

    fn add(self, other: Self) -> UExpression<I, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);

        match (self.as_inner(), other.as_inner()) {
            (UExpressionInner::Value(0), _) => other,
            (_, UExpressionInner::Value(0)) => self,
            _ => UExpressionInner::Add(box self, box other).annotate(bitwidth),
        }
    }
}

impl<I, T> Sub for UExpression<I, T> {
    type Output = Self;

    fn sub(self, other: Self) -> UExpression<I, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Sub(box self, box other).annotate(bitwidth)
    }
}

impl<I, T> Mul for UExpression<I, T> {
    type Output = Self;

    fn mul(self, other: Self) -> UExpression<I, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Mult(box self, box other).annotate(bitwidth)
    }
}

impl<I, T> Div for UExpression<I, T> {
    type Output = Self;

    fn div(self, other: Self) -> UExpression<I, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Div(box self, box other).annotate(bitwidth)
    }
}

impl<I, T> Rem for UExpression<I, T> {
    type Output = Self;

    fn rem(self, other: Self) -> UExpression<I, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Rem(box self, box other).annotate(bitwidth)
    }
}

impl<I, T> Not for UExpression<I, T> {
    type Output = Self;

    fn not(self) -> UExpression<I, T> {
        let bitwidth = self.bitwidth;
        UExpressionInner::Not(box self).annotate(bitwidth)
    }
}

impl<I, T> Neg for UExpression<I, T> {
    type Output = Self;

    fn neg(self) -> UExpression<I, T> {
        let bitwidth = self.bitwidth;
        UExpressionInner::Neg(box self).annotate(bitwidth)
    }
}

impl<I, T: Field> UExpression<I, T> {
    pub fn xor(self, other: Self) -> UExpression<I, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Xor(box self, box other).annotate(bitwidth)
    }

    pub fn or(self, other: Self) -> UExpression<I, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Or(box self, box other).annotate(bitwidth)
    }

    pub fn and(self, other: Self) -> UExpression<I, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::And(box self, box other).annotate(bitwidth)
    }

    pub fn pos(self) -> UExpression<I, T> {
        let bitwidth = self.bitwidth;
        UExpressionInner::Pos(box self).annotate(bitwidth)
    }

    pub fn left_shift(self, by: UExpression<I, T>) -> UExpression<I, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(by.bitwidth, UBitwidth::B32);
        UExpressionInner::LeftShift(box self, box by).annotate(bitwidth)
    }

    pub fn right_shift(self, by: UExpression<I, T>) -> UExpression<I, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(by.bitwidth, UBitwidth::B32);
        UExpressionInner::RightShift(box self, box by).annotate(bitwidth)
    }

    pub fn floor_sub(self, other: Self) -> UExpression<I, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::FloorSub(box self, box other).annotate(bitwidth)
    }
}

impl<I, T: Field> From<u128> for UExpressionInner<I, T> {
    fn from(e: u128) -> Self {
        UExpressionInner::Value(e)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct UMetadata {
    pub bitwidth: Option<Bitwidth>,
    pub should_reduce: Option<bool>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct UExpression<I, T> {
    pub bitwidth: UBitwidth,
    pub metadata: Option<UMetadata>,
    pub inner: UExpressionInner<I, T>,
}

impl<I, T> From<u16> for UExpression<I, T> {
    fn from(u: u16) -> Self {
        UExpressionInner::Value(u as u128).annotate(UBitwidth::B16)
    }
}

impl<I, T> From<u8> for UExpression<I, T> {
    fn from(u: u8) -> Self {
        UExpressionInner::Value(u as u128).annotate(UBitwidth::B8)
    }
}

impl<I, T> PartialEq<u32> for UExpression<I, T> {
    fn eq(&self, other: &u32) -> bool {
        match self.as_inner() {
            UExpressionInner::Value(v) => *v == *other as u128,
            _ => true,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum UExpressionInner<I, T> {
    Block(BlockExpression<I, T, UExpression<I, T>>),
    Identifier(IdentifierExpression<I, UExpression<I, T>>),
    Value(u128),
    Add(Box<UExpression<I, T>>, Box<UExpression<I, T>>),
    Sub(Box<UExpression<I, T>>, Box<UExpression<I, T>>),
    FloorSub(Box<UExpression<I, T>>, Box<UExpression<I, T>>),
    Mult(Box<UExpression<I, T>>, Box<UExpression<I, T>>),
    Div(Box<UExpression<I, T>>, Box<UExpression<I, T>>),
    Rem(Box<UExpression<I, T>>, Box<UExpression<I, T>>),
    Xor(Box<UExpression<I, T>>, Box<UExpression<I, T>>),
    And(Box<UExpression<I, T>>, Box<UExpression<I, T>>),
    Or(Box<UExpression<I, T>>, Box<UExpression<I, T>>),
    Not(Box<UExpression<I, T>>),
    Neg(Box<UExpression<I, T>>),
    Pos(Box<UExpression<I, T>>),
    FunctionCall(FunctionCallExpression<I, T, UExpression<I, T>>),
    LeftShift(Box<UExpression<I, T>>, Box<UExpression<I, T>>),
    RightShift(Box<UExpression<I, T>>, Box<UExpression<I, T>>),
    Conditional(ConditionalExpression<I, T, UExpression<I, T>>),
    Member(MemberExpression<I, T, UExpression<I, T>>),
    Select(SelectExpression<I, T, UExpression<I, T>>),
    Element(ElementExpression<I, T, UExpression<I, T>>),
}

impl<I, T> UExpressionInner<I, T> {
    pub fn annotate<W: Into<UBitwidth>>(self, bitwidth: W) -> UExpression<I, T> {
        UExpression {
            metadata: None,
            bitwidth: bitwidth.into(),
            inner: self,
        }
    }
}

impl<I, T> UExpression<I, T> {
    pub fn metadata(self, metadata: UMetadata) -> UExpression<I, T> {
        UExpression {
            metadata: Some(metadata),
            ..self
        }
    }
}

pub fn bitwidth(a: u128) -> Bitwidth {
    (128 - a.leading_zeros()) as Bitwidth
}

impl<I, T> UExpression<I, T> {
    pub fn bitwidth(&self) -> UBitwidth {
        self.bitwidth
    }

    pub fn as_inner(&self) -> &UExpressionInner<I, T> {
        &self.inner
    }

    pub fn into_inner(self) -> UExpressionInner<I, T> {
        self.inner
    }
}
