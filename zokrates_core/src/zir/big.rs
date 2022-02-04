use super::identifier::Identifier;
use super::reduction::ShouldReduce;
use super::{BooleanExpression, UExpression};
use num_bigint::BigUint;
use zokrates_field::Field;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BigMetadata<T> {
    pub max: [T; 4],
    pub should_reduce: ShouldReduce,
}

impl<T: Field> BigMetadata<T> {
    pub fn with_max(max: [T; 4]) -> Self {
        BigMetadata {
            max,
            should_reduce: ShouldReduce::Unknown,
        }
    }

    pub fn bitwidth(&self) -> u32 {
        self.max.iter().map(|m| m.bits()).max().unwrap() as u32
    }

    // issue the metadata for a parameter
    pub fn parameter() -> Self {
        use std::convert::TryInto;

        Self {
            should_reduce: ShouldReduce::False,
            max: (0..4)
                .map(|_| T::from(2_u32).pow(64) - T::from(1))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        }
    }
}

#[derive(Clone, PartialEq, Hash, Eq, Debug)]
pub struct BigExpression<'ast, T> {
    pub metadata: Option<BigMetadata<T>>,
    pub inner: BigExpressionInner<'ast, T>,
}

impl<'ast, T: Field> BigExpression<'ast, T> {
    pub fn metadata(self, metadata: BigMetadata<T>) -> Self {
        Self {
            metadata: Some(metadata),
            ..self
        }
    }

    pub fn with_max(self, max: [T; 4]) -> Self {
        self.metadata(BigMetadata::with_max(max))
    }
}

impl<'ast, T> BigExpression<'ast, T> {
    pub fn as_inner(&self) -> &BigExpressionInner<'ast, T> {
        &self.inner
    }

    pub fn into_inner(self) -> BigExpressionInner<'ast, T> {
        self.inner
    }
}

/// An expression of type `field`
#[derive(Clone, PartialEq, Hash, Eq, Debug)]
pub enum BigExpressionInner<'ast, T> {
    Value(BigUint),
    Identifier(Identifier<'ast>),
    Select(Vec<BigExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    Add(Box<BigExpression<'ast, T>>, Box<BigExpression<'ast, T>>),
    Mult(Box<BigExpression<'ast, T>>, Box<BigExpression<'ast, T>>),
    IfElse(
        Box<BooleanExpression<'ast, T>>,
        Box<BigExpression<'ast, T>>,
        Box<BigExpression<'ast, T>>,
    ),
}

impl<'ast, T> BigExpressionInner<'ast, T> {
    pub fn annotate(self) -> BigExpression<'ast, T> {
        BigExpression {
            metadata: None,
            inner: self,
        }
    }
}
