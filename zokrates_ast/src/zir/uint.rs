use crate::common::expressions::{UValueExpression, UnaryExpression, ValueExpression};
use crate::zir::IdentifierExpression;
use crate::{common::expressions::BinaryExpression, common::operators::*, zir::types::UBitwidth};
use derivative::Derivative;
use serde::{Deserialize, Serialize};
use zokrates_field::Field;

use super::{ConditionalExpression, SelectExpression};

impl<'ast, T: Field> UExpression<'ast, T> {
    #[allow(clippy::should_implement_trait)]
    pub fn add(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Add(BinaryExpression::new(self, other)).annotate(bitwidth)
    }

    #[allow(clippy::should_implement_trait)]
    pub fn sub(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Sub(BinaryExpression::new(self, other)).annotate(bitwidth)
    }

    pub fn select(values: Vec<Self>, index: Self) -> UExpression<'ast, T> {
        let bitwidth = values[0].bitwidth;
        UExpressionInner::Select(SelectExpression::new(values, index)).annotate(bitwidth)
    }

    pub fn mult(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Mult(BinaryExpression::new(self, other)).annotate(bitwidth)
    }

    #[allow(clippy::should_implement_trait)]
    pub fn div(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Div(BinaryExpression::new(self, other)).annotate(bitwidth)
    }

    #[allow(clippy::should_implement_trait)]
    pub fn rem(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Rem(BinaryExpression::new(self, other)).annotate(bitwidth)
    }

    pub fn xor(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Xor(BinaryExpression::new(self, other)).annotate(bitwidth)
    }

    #[allow(clippy::should_implement_trait)]
    pub fn not(self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        UExpressionInner::Not(UnaryExpression::new(self)).annotate(bitwidth)
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

    pub fn left_shift(self, by: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        UExpressionInner::LeftShift(BinaryExpression::new(self, by)).annotate(bitwidth)
    }

    pub fn right_shift(self, by: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        UExpressionInner::RightShift(BinaryExpression::new(self, by)).annotate(bitwidth)
    }
}

impl<'ast, T> From<u128> for UExpressionInner<'ast, T> {
    fn from(e: u128) -> Self {
        UExpressionInner::Value(ValueExpression::new(e))
    }
}

impl<'ast, T> From<u32> for UExpression<'ast, T> {
    fn from(u: u32) -> Self {
        UExpressionInner::from(u as u128).annotate(UBitwidth::B32)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub enum ShouldReduce {
    Unknown,
    True,
    False,
}

impl ShouldReduce {
    pub fn to_bool(&self) -> bool {
        match self {
            ShouldReduce::Unknown => {
                unreachable!("should_reduce should be convertible to a bool but it's unknown")
            }
            ShouldReduce::True => true,
            ShouldReduce::False => false,
        }
    }

    pub fn is_unknown(&self) -> bool {
        *self == ShouldReduce::Unknown
    }

    pub fn is_true(&self) -> bool {
        *self == ShouldReduce::True
    }

    pub fn is_false(&self) -> bool {
        *self == ShouldReduce::False
    }

    // we can always enable a reduction
    pub fn make_true(self) -> Self {
        ShouldReduce::True
    }

    // we cannot disable a reduction that was enabled
    pub fn make_false(self) -> Self {
        match self {
            ShouldReduce::True => unreachable!("Attempt to disable a required reduction"),
            _ => ShouldReduce::False,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct UMetadata<T> {
    pub max: T,
    pub should_reduce: ShouldReduce,
}

impl<T: Field> UMetadata<T> {
    pub fn with_max<U: Into<T>>(max: U) -> Self {
        UMetadata {
            max: max.into(),
            should_reduce: ShouldReduce::Unknown,
        }
    }

    pub fn bitwidth(&self) -> u32 {
        self.max.bits()
    }

    // issue the metadata for a parameter of a given bitwidth
    pub fn parameter<W: Into<UBitwidth>>(bitwidth: W) -> Self {
        Self {
            should_reduce: ShouldReduce::False,
            max: T::from(2_u32).pow(bitwidth.into().to_usize()) - T::from(1),
        }
    }
}

#[derive(Derivative)]
#[derivative(PartialEq, Hash)]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct UExpression<'ast, T> {
    pub bitwidth: UBitwidth,
    pub metadata: Option<UMetadata<T>>,
    #[serde(borrow)]
    pub inner: UExpressionInner<'ast, T>,
}

#[derive(Derivative)]
#[derivative(PartialEq, Hash)]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum UExpressionInner<'ast, T> {
    Value(UValueExpression),
    #[serde(borrow)]
    Identifier(IdentifierExpression<'ast, UExpression<'ast, T>>),
    Select(SelectExpression<'ast, T, UExpression<'ast, T>>),
    Add(BinaryExpression<OpAdd, UExpression<'ast, T>, UExpression<'ast, T>, UExpression<'ast, T>>),
    Sub(BinaryExpression<OpSub, UExpression<'ast, T>, UExpression<'ast, T>, UExpression<'ast, T>>),
    Mult(BinaryExpression<OpMul, UExpression<'ast, T>, UExpression<'ast, T>, UExpression<'ast, T>>),
    Div(BinaryExpression<OpDiv, UExpression<'ast, T>, UExpression<'ast, T>, UExpression<'ast, T>>),
    Rem(BinaryExpression<OpRem, UExpression<'ast, T>, UExpression<'ast, T>, UExpression<'ast, T>>),
    Xor(BinaryExpression<OpXor, UExpression<'ast, T>, UExpression<'ast, T>, UExpression<'ast, T>>),
    And(BinaryExpression<OpAnd, UExpression<'ast, T>, UExpression<'ast, T>, UExpression<'ast, T>>),
    Or(BinaryExpression<OpOr, UExpression<'ast, T>, UExpression<'ast, T>, UExpression<'ast, T>>),
    LeftShift(
        BinaryExpression<OpLsh, UExpression<'ast, T>, UExpression<'ast, T>, UExpression<'ast, T>>,
    ),
    RightShift(
        BinaryExpression<OpRsh, UExpression<'ast, T>, UExpression<'ast, T>, UExpression<'ast, T>>,
    ),
    Not(UnaryExpression<OpNot, UExpression<'ast, T>, UExpression<'ast, T>>),
    Conditional(ConditionalExpression<'ast, T, UExpression<'ast, T>>),
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

impl<'ast, T: Field> UExpression<'ast, T> {
    pub fn metadata(self, metadata: UMetadata<T>) -> UExpression<'ast, T> {
        UExpression {
            metadata: Some(metadata),
            ..self
        }
    }

    pub fn with_max<U: Into<T>>(self, max: U) -> Self {
        UExpression {
            metadata: Some(UMetadata::with_max(max)),
            ..self
        }
    }
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
