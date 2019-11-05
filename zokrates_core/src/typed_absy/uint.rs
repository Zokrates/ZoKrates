use typed_absy::identifier::Identifier;
use zokrates_field::field::Field;

type Bitwidth = usize;

impl<'ast> UExpression<'ast> {
    pub fn add(self, other: Self) -> UExpression<'ast> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Add(box self, box other).annotate(bitwidth)
    }

    pub fn mult(self, other: Self) -> UExpression<'ast> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Mult(box self, box other).annotate(bitwidth)
    }

    pub fn xor(self, other: Self) -> UExpression<'ast> {
        let bitwidth = self.bitwidth;
        assert_eq!(bitwidth, other.bitwidth);
        UExpressionInner::Xor(box self, box other).annotate(bitwidth)
    }
}

impl<'ast> From<u128> for UExpressionInner<'ast> {
    fn from(e: u128) -> Self {
        UExpressionInner::Value(e)
    }
}

impl<'ast> From<&'ast str> for UExpressionInner<'ast> {
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
pub struct UExpression<'ast> {
    pub bitwidth: Bitwidth,
    pub metadata: Option<UMetadata>,
    pub inner: UExpressionInner<'ast>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UExpressionInner<'ast> {
    Identifier(Identifier<'ast>),
    Value(u128),
    Add(Box<UExpression<'ast>>, Box<UExpression<'ast>>),
    Mult(Box<UExpression<'ast>>, Box<UExpression<'ast>>),
    Xor(Box<UExpression<'ast>>, Box<UExpression<'ast>>),
}

impl<'ast> UExpressionInner<'ast> {
    pub fn annotate(self, bitwidth: Bitwidth) -> UExpression<'ast> {
        UExpression {
            metadata: None,
            bitwidth,
            inner: self,
        }
    }
}

impl<'ast> UExpression<'ast> {
    fn metadata(self, metadata: UMetadata) -> UExpression<'ast> {
        UExpression {
            metadata: Some(metadata),
            ..self
        }
    }
}

fn bitwidth(a: u128) -> Bitwidth {
    (128 - a.leading_zeros()) as Bitwidth
}

impl<'ast> UExpression<'ast> {
    pub fn reduce<T: Field>(self) -> Self {
        let max_bitwidth = T::get_required_bits() - 1;

        let range = self.bitwidth;

        assert!(range < max_bitwidth / 2);

        let metadata = self.metadata;
        let inner = self.inner;

        use self::UExpressionInner::*;

        match inner {
            Value(v) => Value(v).annotate(range).metadata(UMetadata {
                bitwidth: Some(bitwidth(v)),
                should_reduce: Some(
                    metadata
                        .map(|m| m.should_reduce.unwrap_or(false))
                        .unwrap_or(false),
                ),
            }),
            Identifier(id) => Identifier(id).annotate(range).metadata(UMetadata {
                bitwidth: Some(range),
                should_reduce: Some(
                    metadata
                        .map(|m| m.should_reduce.unwrap_or(false))
                        .unwrap_or(false),
                ),
            }),
            Add(box left, box right) => {
                // reduce the two terms
                let left = left.reduce::<T>();
                let right = right.reduce::<T>();

                let left_metadata = left.metadata.clone().unwrap();
                let right_metadata = right.metadata.clone().unwrap();

                // determine the bitwidth of each term. It's their current bitwidth, unless they are tagged as `should_reduce` in which case they now have bitwidth 8
                let left_bitwidth = left_metadata
                    .should_reduce
                    .map(|should_reduce| {
                        if should_reduce {
                            range
                        } else {
                            left_metadata.bitwidth.unwrap()
                        }
                    })
                    .unwrap();
                let right_bitwidth = right_metadata
                    .should_reduce
                    .map(|should_reduce| {
                        if should_reduce {
                            range
                        } else {
                            right_metadata.bitwidth.unwrap()
                        }
                    })
                    .unwrap();

                let output_width = std::cmp::max(left_bitwidth, right_bitwidth) + 1; // bitwidth(a + b) = max(bitwidth(a), bitwidth(b)) + 1

                if output_width > max_bitwidth {
                    // the addition doesnt fit, we reduce both terms first (TODO maybe one would be enough here)

                    let left = UExpression {
                        metadata: Some(UMetadata {
                            should_reduce: Some(true),
                            ..left_metadata
                        }),
                        ..left
                    };

                    let right = UExpression {
                        metadata: Some(UMetadata {
                            should_reduce: Some(true),
                            ..right_metadata
                        }),
                        ..right
                    };

                    UExpression::add(left, right).metadata(UMetadata {
                        bitwidth: Some(range + 1),
                        should_reduce: Some(
                            metadata
                                .map(|m| m.should_reduce.unwrap_or(false))
                                .unwrap_or(false),
                        ),
                    })
                } else {
                    // the addition fits, so we just add
                    UExpression::add(left, right).metadata(UMetadata {
                        bitwidth: Some(output_width),
                        should_reduce: Some(
                            metadata
                                .map(|m| m.should_reduce.unwrap_or(false))
                                .unwrap_or(false),
                        ),
                    })
                }
            }
            Xor(box left, box right) => {
                // reduce the two terms
                let left = left.reduce::<T>();
                let right = right.reduce::<T>();

                let left_metadata = left.metadata.clone().unwrap();
                let right_metadata = right.metadata.clone().unwrap();

                // for xor we need both terms to be in range. Therefore we reduce them to being in range.
                // NB: if they are already in range, the flattening process will ignore the reduction
                let left = left.metadata(UMetadata {
                    should_reduce: Some(true),
                    ..left_metadata
                });

                let right = right.metadata(UMetadata {
                    should_reduce: Some(true),
                    ..right_metadata
                });

                UExpression::xor(left, right)
            }
            Mult(box left, box right) => {
                // reduce the two terms
                let left = left.reduce::<T>();
                let right = right.reduce::<T>();

                let left_metadata = left.metadata.clone().unwrap();
                let right_metadata = right.metadata.clone().unwrap();

                // determine the bitwidth of each term. It's their current bitwidth, unless they are tagged as `should_reduce` in which case they now have bitwidth 8
                let left_bitwidth = left_metadata
                    .should_reduce
                    .map(|should_reduce| {
                        if should_reduce {
                            range
                        } else {
                            left_metadata.bitwidth.unwrap()
                        }
                    })
                    .unwrap();
                let right_bitwidth = right_metadata
                    .should_reduce
                    .map(|should_reduce| {
                        if should_reduce {
                            range
                        } else {
                            right_metadata.bitwidth.unwrap()
                        }
                    })
                    .unwrap();

                let output_width = left_bitwidth + right_bitwidth; // bitwidth(a*b) = bitwidth(a) + bitwidth(b)

                if output_width > max_bitwidth {
                    // the multiplication doesnt fit, we reduce both terms first (TODO maybe one would be enough here)

                    let left = UExpression {
                        metadata: Some(UMetadata {
                            should_reduce: Some(true),
                            ..left_metadata
                        }),
                        ..left
                    };

                    let right = UExpression {
                        metadata: Some(UMetadata {
                            should_reduce: Some(true),
                            ..right_metadata
                        }),
                        ..right
                    };

                    UExpression::mult(left, right).metadata(UMetadata {
                        bitwidth: Some(2 * range),
                        should_reduce: Some(
                            metadata
                                .map(|m| m.should_reduce.unwrap_or(false))
                                .unwrap_or(false),
                        ),
                    })
                } else {
                    // the multiplication fits, so we just multiply
                    UExpression::mult(left, right).metadata(UMetadata {
                        bitwidth: Some(output_width),
                        should_reduce: Some(
                            metadata
                                .map(|m| m.should_reduce.unwrap_or(false))
                                .unwrap_or(false),
                        ),
                    })
                }
            }
        }
    }
}

impl<'ast> UExpression<'ast> {
    pub fn bitwidth(&self) -> Bitwidth {
        self.bitwidth
    }

    pub fn as_inner(&self) -> &UExpressionInner<'ast> {
        &self.inner
    }

    pub fn into_inner(self) -> UExpressionInner<'ast> {
        self.inner
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    fn count_readjustments(e: UExpression) -> usize {
        let metadata = e.metadata;
        let inner = e.inner;

        use self::UExpressionInner::*;

        match inner {
            Identifier(_) => 0,
            Value(_) => 0,
            Mult(box left, box right) | Xor(box left, box right) | Add(box left, box right) => {
                let l = count_readjustments(left);
                let r = count_readjustments(right);
                r + l
                    + if metadata
                        .map(|m| m.should_reduce.unwrap_or(true))
                        .unwrap_or(true)
                    {
                        1
                    } else {
                        0
                    }
            }
        }
    }

    #[test]
    fn _100_times_a() {
        // a * 100 where a is 8 bits and the host field prime has 254 bits
        // we don't readjust until we overflow 253 bits
        // each addition increases the bitwidth by 1
        // 253 = 100*1 + 153, so we can do all multiplications without readjusting

        let e = (0..100).fold(
            UExpressionInner::Identifier("a".into()).annotate(8),
            |acc, _| UExpression::add(acc, UExpressionInner::Identifier("a".into()).annotate(8)),
        );

        let e = e.reduce::<FieldPrime>();

        assert_eq!(count_readjustments(e), 0);
    }

    #[test]
    fn _100_powers_of_a() {
        // a ** 100 where a is 8 bits and the host field prime has 254 bits
        // we don't readjust until we overflow 253 bits
        // each multiplication increases the bitwidth by 8
        // 253 = 31 * 8 + 5, so we do 31 multiplications followed by one readjustment, three times. Then we have 7 multiplications left
        // we readjusted 3 times

        let e = (0..100).fold(
            UExpressionInner::Identifier("a".into()).annotate(8),
            |acc, _| UExpression::mult(acc, UExpressionInner::Identifier("a".into()).annotate(8)),
        );

        let e = e.reduce::<FieldPrime>();

        assert_eq!(count_readjustments(e), 3);
    }
}
