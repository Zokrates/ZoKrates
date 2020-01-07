use typed_absy::identifier::Identifier;
use typed_absy::types::FunctionKey;
use typed_absy::ArrayExpression;
use typed_absy::BooleanExpression;
use typed_absy::FieldElementExpression;
use typed_absy::TypedExpression;
use zokrates_field::field::Field;

type Bitwidth = usize;

impl<'ast, U: Uint, T: Field> UExpression<'ast, U, T> {
    pub fn add(self, other: Self) -> UExpression<'ast, U, T> {
        UExpressionInner::Add(box self, box other).annotate()
    }

    pub fn sub(self, other: Self) -> UExpression<'ast, U, T> {
        UExpressionInner::Sub(box self, box other).annotate()
    }

    pub fn mult(self, other: Self) -> UExpression<'ast, U, T> {
        UExpressionInner::Mult(box self, box other).annotate()
    }

    pub fn xor(self, other: Self) -> UExpression<'ast, U, T> {
        UExpressionInner::Xor(box self, box other).annotate()
    }

    pub fn or(self, other: Self) -> UExpression<'ast, U, T> {
        UExpressionInner::Or(box self, box other).annotate()
    }

    pub fn and(self, other: Self) -> UExpression<'ast, U, T> {
        UExpressionInner::And(box self, box other).annotate()
    }

    pub fn not(self) -> UExpression<'ast, U, T> {
        UExpressionInner::Not(box self).annotate()
    }

    pub fn left_shift(self, by: FieldElementExpression<'ast, T>) -> UExpression<'ast, U, T> {
        UExpressionInner::LeftShift(box self, box by).annotate()
    }

    pub fn right_shift(self, by: FieldElementExpression<'ast, T>) -> UExpression<'ast, U, T> {
        UExpressionInner::RightShift(box self, box by).annotate()
    }
}

impl<'ast, U: Uint, T: Field> From<u128> for UExpressionInner<'ast, U, T> {
    fn from(e: u128) -> Self {
        UExpressionInner::Value(e)
    }
}

impl<'ast, U: Uint, T: Field> From<&'ast str> for UExpressionInner<'ast, U, T> {
    fn from(e: &'ast str) -> Self {
        UExpressionInner::Identifier(e.into())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UMetadata {
    pub bitwidth: Option<Bitwidth>,
    pub should_reduce: Option<bool>,
}

pub use zir::Uint;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UExpression<'ast, U: Uint, T: Field> {
    pub metadata: Option<UMetadata>,
    pub inner: UExpressionInner<'ast, U, T>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UExpressionInner<'ast, U: Uint, T: Field> {
    Identifier(Identifier<'ast>),
    Value(U),
    Add(Box<UExpression<'ast, U, T>>, Box<UExpression<'ast, U, T>>),
    Sub(Box<UExpression<'ast, U, T>>, Box<UExpression<'ast, U, T>>),
    Mult(Box<UExpression<'ast, U, T>>, Box<UExpression<'ast, U, T>>),
    Xor(Box<UExpression<'ast, U, T>>, Box<UExpression<'ast, U, T>>),
    And(Box<UExpression<'ast, U, T>>, Box<UExpression<'ast, U, T>>),
    Or(Box<UExpression<'ast, U, T>>, Box<UExpression<'ast, U, T>>),
    Not(Box<UExpression<'ast, U, T>>),
    LeftShift(
        Box<UExpression<'ast, U, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    RightShift(
        Box<UExpression<'ast, U, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    FunctionCall(FunctionKey<'ast>, Vec<TypedExpression<'ast, T>>),
    Select(
        Box<ArrayExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    IfElse(
        Box<BooleanExpression<'ast, T>>,
        Box<UExpression<'ast, U, T>>,
        Box<UExpression<'ast, U, T>>,
    ),
}

impl<'ast, U: Uint, T: Field> UExpressionInner<'ast, U, T> {
    pub fn bitwidth(&self) -> Bitwidth {
        unimplemented!()
    }

    pub fn annotate(self) -> UExpression<'ast, U, T> {
        UExpression {
            metadata: None,
            inner: self,
        }
    }
}

impl<'ast, U: Uint, T: Field> UExpression<'ast, U, T> {
    pub fn metadata(self, metadata: UMetadata) -> UExpression<'ast, U, T> {
        UExpression {
            metadata: Some(metadata),
            ..self
        }
    }
}

impl<'ast, U: Uint, T: Field> UExpression<'ast, U, T> {
    pub fn bitwidth(&self) -> Bitwidth {
        unimplemented!()
    }

    pub fn as_inner(&self) -> &UExpressionInner<'ast, U, T> {
        &self.inner
    }

    pub fn into_inner(self) -> UExpressionInner<'ast, U, T> {
        self.inner
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    // fn count_readjustments<'ast, T: Field>(e: UExpression<'ast, U, T>) -> usize {
    //     let metadata = e.metadata;
    //     let inner = e.inner;

    //     use self::UExpressionInner::*;

    //     match inner {
    //         Identifier(_) => 0,
    //         Value(_) => 0,
    //         Mult(box left, box right) | Xor(box left, box right) | Add(box left, box right) => {
    //             let l = count_readjustments(left);
    //             let r = count_readjustments(right);
    //             r + l
    //                 + if metadata
    //                     .map(|m| m.should_reduce.unwrap_or(true))
    //                     .unwrap_or(true)
    //                 {
    //                     1
    //                 } else {
    //                     0
    //                 }
    //         }
    //     }
    // }

    // #[test]
    // fn _100_times_a() {
    //     // a * 100 where a is 8 bits and the host field prime has 254 bits
    //     // we don't readjust until we overflow 253 bits
    //     // each addition increases the bitwidth by 1
    //     // 253 = 100*1 + 153, so we can do all multiplications without readjusting

    //     let e = (0..100).fold(
    //         UExpressionInner::Identifier("a".into()).annotate(8),
    //         |acc, _| UExpression::add(acc, UExpressionInner::Identifier("a".into()).annotate(8)),
    //     );

    //     let e = e.reduce::<FieldPrime>();

    //     assert_eq!(count_readjustments(e), 0);
    // }

    // #[test]
    // fn _100_powers_of_a() {
    //     // a ** 100 where a is 8 bits and the host field prime has 254 bits
    //     // we don't readjust until we overflow 253 bits
    //     // each multiplication increases the bitwidth by 8
    //     // 253 = 31 * 8 + 5, so we do 31 multiplications followed by one readjustment, three times. Then we have 7 multiplications left
    //     // we readjusted 3 times

    //     let e = (0..100).fold(
    //         UExpressionInner::Identifier("a".into()).annotate(8),
    //         |acc, _| UExpression::mult(acc, UExpressionInner::Identifier("a".into()).annotate(8)),
    //     );

    //     let e = e.reduce::<FieldPrime>();

    //     assert_eq!(count_readjustments(e), 3);
    // }
}
