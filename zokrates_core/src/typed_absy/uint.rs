use typed_absy::identifier::Identifier;
use typed_absy::ArrayExpression;
use typed_absy::BooleanExpression;
use typed_absy::FieldElementExpression;
use zokrates_field::field::Field;

type Bitwidth = usize;

impl<'ast, T: Field> UExpression<'ast, T> {
    pub fn add(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Add(box self, box other).annotate(bitwidth)
    }

    pub fn mult(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Mult(box self, box other).annotate(bitwidth)
    }

    pub fn xor(self, other: Self) -> UExpression<'ast, T> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Xor(box self, box other).annotate(bitwidth)
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UMetadata {
    pub bitwidth: Option<Bitwidth>,
    pub should_reduce: Option<bool>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UExpression<'ast, T: Field> {
    pub bitwidth: Bitwidth,
    pub metadata: Option<UMetadata>,
    pub inner: UExpressionInner<'ast, T>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UExpressionInner<'ast, T: Field> {
    Identifier(Identifier<'ast>),
    Value(u128),
    Add(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    Mult(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    Xor(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    Select(
        Box<ArrayExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    IfElse(
        Box<BooleanExpression<'ast, T>>,
        Box<UExpression<'ast, T>>,
        Box<UExpression<'ast, T>>,
    ),
}

impl<'ast, T: Field> UExpressionInner<'ast, T> {
    pub fn annotate(self, bitwidth: Bitwidth) -> UExpression<'ast, T> {
        UExpression {
            metadata: None,
            bitwidth,
            inner: self,
        }
    }
}

impl<'ast, T: Field> UExpression<'ast, T> {
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

impl<'ast, T: Field> UExpression<'ast, T> {
    pub fn bitwidth(&self) -> Bitwidth {
        self.bitwidth
    }

    pub fn as_inner(&self) -> &UExpressionInner<'ast, T> {
        &self.inner
    }

    pub fn into_inner(self) -> UExpressionInner<'ast, T> {
        self.inner
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    // fn count_readjustments<'ast, T: Field>(e: UExpression<'ast, T>) -> usize {
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
