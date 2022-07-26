use crate::typed::types::UBitwidth;
use crate::typed::*;
use std::ops::{Add, Div, Mul, Neg, Not, Rem, Sub};
use zokrates_field::Field;

type Bitwidth = usize;

impl<'ast, T> Add for UExpression<'ast, T> {
    type Output = Self;

    fn add(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);

        match (self.as_inner(), other.as_inner()) {
            (UExpressionInner::Value(0), _) => other,
            (_, UExpressionInner::Value(0)) => self,
            _ => UExpressionInner::Add(box self, box other).annotate(bitwidth),
        }
    }
}

impl<'ast, T> Sub for UExpression<'ast, T> {
    type Output = Self;

    fn sub(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Sub(box self, box other).annotate(bitwidth)
    }
}

impl<'ast, T> Mul for UExpression<'ast, T> {
    type Output = Self;

    fn mul(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Mult(box self, box other).annotate(bitwidth)
    }
}

impl<'ast, T> Div for UExpression<'ast, T> {
    type Output = Self;

    fn div(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Div(box self, box other).annotate(bitwidth)
    }
}

impl<'ast, T> Rem for UExpression<'ast, T> {
    type Output = Self;

    fn rem(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Rem(box self, box other).annotate(bitwidth)
    }
}

impl<'ast, T> Not for UExpression<'ast, T> {
    type Output = Self;

    fn not(self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        UExpressionInner::Not(box self).annotate(bitwidth)
    }
}

impl<'ast, T> Neg for UExpression<'ast, T> {
    type Output = Self;

    fn neg(self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        UExpressionInner::Neg(box self).annotate(bitwidth)
    }
}

impl<'ast, T: Field> UExpression<'ast, T> {
    pub fn xor(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Xor(box self, box other).annotate(bitwidth)
    }

    pub fn or(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Or(box self, box other).annotate(bitwidth)
    }

    pub fn and(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::And(box self, box other).annotate(bitwidth)
    }

    pub fn pos(self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        UExpressionInner::Pos(box self).annotate(bitwidth)
    }

    pub fn left_shift(self, by: UExpression<'ast, T>) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(by.bitwidth, UBitwidth::B32);
        UExpressionInner::LeftShift(box self, box by).annotate(bitwidth)
    }

    pub fn right_shift(self, by: UExpression<'ast, T>) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(by.bitwidth, UBitwidth::B32);
        UExpressionInner::RightShift(box self, box by).annotate(bitwidth)
    }

    pub fn floor_sub(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::FloorSub(box self, box other).annotate(bitwidth)
    }
}

impl<'ast, T: Field> From<u128> for UExpressionInner<'ast, T> {
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
pub struct UExpression<'ast, T> {
    pub bitwidth: UBitwidth,
    pub metadata: Option<UMetadata>,
    pub inner: UExpressionInner<'ast, T>,
}

impl<'ast, T> From<u16> for UExpression<'ast, T> {
    fn from(u: u16) -> Self {
        UExpressionInner::Value(u as u128).annotate(UBitwidth::B16)
    }
}

impl<'ast, T> From<u8> for UExpression<'ast, T> {
    fn from(u: u8) -> Self {
        UExpressionInner::Value(u as u128).annotate(UBitwidth::B8)
    }
}

impl<'ast, T> PartialEq<u32> for UExpression<'ast, T> {
    fn eq(&self, other: &u32) -> bool {
        match self.as_inner() {
            UExpressionInner::Value(v) => *v == *other as u128,
            _ => true,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum UExpressionInner<'ast, T> {
    Block(BlockExpression<'ast, T, UExpression<'ast, T>>),
    Identifier(Identifier<'ast>),
    Value(u128),
    Add(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    Sub(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    FloorSub(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    Mult(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    Div(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    Rem(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    Xor(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    And(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    Or(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    Not(Box<UExpression<'ast, T>>),
    Neg(Box<UExpression<'ast, T>>),
    Pos(Box<UExpression<'ast, T>>),
    FunctionCall(FunctionCallExpression<'ast, T, UExpression<'ast, T>>),
    LeftShift(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    RightShift(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
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
