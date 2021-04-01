use crate::zir::identifier::Identifier;
use crate::zir::types::UBitwidth;
use crate::zir::BooleanExpression;
use zokrates_field::Field;

impl<'ast, T: Field> UExpression<'ast, T> {
    pub fn add(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Add(box self, box other).annotate(bitwidth)
    }

    pub fn sub(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Sub(box self, box other).annotate(bitwidth)
    }

    pub fn mult(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Mult(box self, box other).annotate(bitwidth)
    }

    pub fn div(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Div(box self, box other).annotate(bitwidth)
    }

    pub fn rem(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Rem(box self, box other).annotate(bitwidth)
    }

    pub fn xor(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Xor(box self, box other).annotate(bitwidth)
    }

    pub fn not(self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        UExpressionInner::Not(box self).annotate(bitwidth)
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

    pub fn left_shift(self, by: UExpression<'ast, T>) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(by.bitwidth(), UBitwidth::B32);
        UExpressionInner::LeftShift(box self, box by).annotate(bitwidth)
    }

    pub fn right_shift(self, by: UExpression<'ast, T>) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(by.bitwidth(), UBitwidth::B32);
        UExpressionInner::RightShift(box self, box by).annotate(bitwidth)
    }
}

impl<'ast, T: Field> From<u128> for UExpressionInner<'ast, T> {
    fn from(e: u128) -> Self {
        UExpressionInner::Value(e)
    }
}

impl<'ast, T: Field> From<&'ast str> for UExpressionInner<'ast, T> {
    fn from(e: &'ast str) -> Self {
        UExpressionInner::Identifier(e.into())
    }
}

impl<'ast, T> From<u32> for UExpression<'ast, T> {
    fn from(u: u32) -> Self {
        UExpressionInner::Value(u as u128).annotate(UBitwidth::B32)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
        self.max.bits() as u32
    }

    // issue the metadata for a parameter of a given bitwidth
    pub fn parameter<W: Into<UBitwidth>>(bitwidth: W) -> Self {
        Self {
            should_reduce: ShouldReduce::False,
            max: T::from(2_u32).pow(bitwidth.into().to_usize()) - T::from(1),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UExpression<'ast, T> {
    pub bitwidth: UBitwidth,
    pub metadata: Option<UMetadata<T>>,
    pub inner: UExpressionInner<'ast, T>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UExpressionInner<'ast, T> {
    Identifier(Identifier<'ast>),
    Value(u128),
    Add(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    Sub(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    Mult(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    Div(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    Rem(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    Xor(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    And(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    Or(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    LeftShift(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    RightShift(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    Not(Box<UExpression<'ast, T>>),
    IfElse(
        Box<BooleanExpression<'ast, T>>,
        Box<UExpression<'ast, T>>,
        Box<UExpression<'ast, T>>,
    ),
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
