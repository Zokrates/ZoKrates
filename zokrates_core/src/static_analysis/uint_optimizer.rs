use crate::embed::FlatEmbed;
use crate::zir::folder::*;
use crate::zir::*;
use std::collections::HashMap;
use std::convert::TryInto;
use std::ops::{BitAnd, Shl, Shr};
use zokrates_field::Field;

#[derive(Default)]
pub struct UintOptimizer<'ast, T: Field> {
    uints: HashMap<ZirAssignee<'ast>, UMetadata<T>>,
    bigs: HashMap<ZirAssignee<'ast>, BigMetadata<T>>,
}

impl<'ast, T: Field> UintOptimizer<'ast, T> {
    pub fn optimize(p: ZirProgram<'ast, T>) -> ZirProgram<'ast, T> {
        UintOptimizer::default().fold_program(p)
    }

    fn register_uint(&mut self, a: ZirAssignee<'ast>, m: UMetadata<T>) {
        self.uints.insert(a, m);
    }

    fn register_big(&mut self, a: ZirAssignee<'ast>, m: BigMetadata<T>) {
        self.bigs.insert(a, m);
    }
}

impl<'ast, T> UExpression<'ast, T> {
    fn force_reduce(self) -> Self {
        let metadata = self.metadata.unwrap();

        let should_reduce = metadata.should_reduce.make_true();

        UExpression {
            metadata: Some(UMetadata {
                should_reduce,
                ..metadata
            }),
            ..self
        }
    }

    fn force_no_reduce(self) -> Self {
        let metadata = self.metadata.unwrap();

        let should_reduce = metadata.should_reduce.make_false();

        UExpression {
            metadata: Some(UMetadata {
                should_reduce,
                ..metadata
            }),
            ..self
        }
    }
}

impl<'ast, T> BigExpression<'ast, T> {
    fn force_reduce(self) -> Self {
        let metadata = self.metadata.unwrap();

        let should_reduce = metadata.should_reduce.make_true();

        Self {
            metadata: Some(BigMetadata {
                should_reduce,
                ..metadata
            }),
            ..self
        }
    }

    fn force_no_reduce(self) -> Self {
        let metadata = self.metadata.unwrap();

        let should_reduce = metadata.should_reduce.make_false();

        Self {
            metadata: Some(BigMetadata {
                should_reduce,
                ..metadata
            }),
            ..self
        }
    }
}

impl<'ast, T: Field> Folder<'ast, T> for UintOptimizer<'ast, T> {
    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        match e {
            FieldElementExpression::Select(a, box i) => {
                let a = a
                    .into_iter()
                    .map(|e| self.fold_field_expression(e))
                    .collect();
                let i = self.fold_uint_expression(i);

                FieldElementExpression::Select(a, box i.force_reduce())
            }
            _ => fold_field_expression(self, e),
        }
    }

    fn fold_big_expression(&mut self, e: BigExpression<'ast, T>) -> BigExpression<'ast, T> {
        use BigExpressionInner::*;

        let range = 64;

        let range_max: T = (2_u128.pow(range as u32) - 1).into();

        match e.inner {
            Value(v) => Value(v.clone()).annotate().with_max(
                v.to_u64_digits()
                    .into_iter()
                    .chain(std::iter::repeat(0))
                    .take(4)
                    .collect::<Vec<_>>()
                    .into_iter()
                    .map(|d| T::from(d))
                    .rev()
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap(),
            ),
            Identifier(id) => Identifier(id.clone()).annotate().metadata(
                self.bigs
                    .get(&Variable::big(id.clone()))
                    .cloned()
                    .unwrap_or_else(|| panic!("identifier should have been defined: {}", id)),
            ),
            Add(box left, box right) => {
                let left = self.fold_big_expression(left);
                let right = self.fold_big_expression(right);

                let left_metadata = left.metadata.clone().unwrap();
                let right_metadata = right.metadata.clone().unwrap();

                let (should_reduce_left, should_reduce_right, max) = left_metadata
                    .max
                    .iter()
                    .zip(right_metadata.max)
                    .map(|(left_max, right_max)| {
                        left_max
                            .checked_add(&right_max)
                            .map(|max| (false, false, max))
                            .unwrap_or_else(|| {
                                range_max
                                    .checked_add(&right_max)
                                    .map(|max| (true, false, max))
                                    .unwrap_or_else(|| {
                                        left_max
                                            .checked_add(&range_max.clone())
                                            .map(|max| (false, true, max))
                                            .unwrap_or_else(|| {
                                                (true, true, range_max.clone() + range_max.clone())
                                            })
                                    })
                            })
                    })
                    .fold(
                        (false, false, vec![]),
                        |(mut should_reduce_left, mut should_reduce_right, mut max), (l, r, m)| {
                            should_reduce_left |= l;
                            should_reduce_right |= r;
                            max.push(m);
                            (should_reduce_left, should_reduce_right, max)
                        },
                    );

                let left = if should_reduce_left {
                    left.force_reduce()
                } else {
                    left.force_no_reduce()
                };

                let right = if should_reduce_right {
                    right.force_reduce()
                } else {
                    right.force_no_reduce()
                };

                let max = max.try_into().unwrap();

                Add(box left, box right).annotate().with_max(max)
            }
            Mult(box left, box right) => {
                let left = self.fold_big_expression(left);
                let right = self.fold_big_expression(right);

                let left_max = left.metadata.clone().unwrap().max;
                let right_max = right.metadata.clone().unwrap().max;

                let max: [T; 4] = (0..4)
                    .map(|_| range_max.clone())
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();

                // the operands must be in canonical form before they can be multiplied
                let left = left.force_reduce();
                let right = right.force_reduce();

                Mult(box left, box right).annotate().with_max(max)
            }
            e => unimplemented!("{}", e.annotate()),
        }
    }

    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> BooleanExpression<'ast, T> {
        match e {
            BooleanExpression::Select(a, box i) => {
                let a = a
                    .into_iter()
                    .map(|e| self.fold_boolean_expression(e))
                    .collect();
                let i = self.fold_uint_expression(i);

                BooleanExpression::Select(a, box i.force_reduce())
            }
            BooleanExpression::UintEq(box left, box right) => {
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

                let left = left.force_reduce();
                let right = right.force_reduce();

                BooleanExpression::UintEq(box left, box right)
            }
            BooleanExpression::UintLt(box left, box right) => {
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

                let left = left.force_reduce();
                let right = right.force_reduce();

                BooleanExpression::UintLt(box left, box right)
            }
            BooleanExpression::UintLe(box left, box right) => {
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

                let left = left.force_reduce();
                let right = right.force_reduce();

                BooleanExpression::UintLe(box left, box right)
            }
            BooleanExpression::UintGt(box left, box right) => {
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

                let left = left.force_reduce();
                let right = right.force_reduce();

                BooleanExpression::UintGt(box left, box right)
            }
            BooleanExpression::UintGe(box left, box right) => {
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

                let left = left.force_reduce();
                let right = right.force_reduce();

                BooleanExpression::UintGe(box left, box right)
            }
            e => fold_boolean_expression(self, e),
        }
    }

    fn fold_uint_expression(&mut self, e: UExpression<'ast, T>) -> UExpression<'ast, T> {
        if e.metadata.is_some() {
            return e;
        }

        let max_bitwidth = T::get_required_bits() - 1;

        let range = e.bitwidth.to_usize();

        let range_max: T = (2_u128.pow(range as u32) - 1).into();

        assert!(range < max_bitwidth / 2);

        let inner = e.inner;

        use self::UExpressionInner::*;

        let res = match inner {
            Value(v) => Value(v).annotate(range).with_max(v),
            Identifier(id) => Identifier(id.clone()).annotate(range).metadata(
                self.uints
                    .get(&Variable::uint(id.clone(), range))
                    .cloned()
                    .unwrap_or_else(|| panic!("identifier should have been defined: {}", id)),
            ),
            Select(values, box index) => {
                let index = self.fold_uint_expression(index);

                let index = index.force_reduce();

                let values: Vec<_> = values
                    .into_iter()
                    .map(|v| self.fold_uint_expression(v).force_no_reduce())
                    .collect();

                let max_value = T::try_from(
                    values
                        .iter()
                        .map(|v| v.metadata.as_ref().unwrap().max.to_biguint())
                        .max()
                        .unwrap(),
                )
                .unwrap();

                UExpression::select(values, index).with_max(max_value)
            }
            Add(box left, box right) => {
                // reduce the two terms
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

                let left_max = left.metadata.clone().unwrap().max;
                let right_max = right.metadata.clone().unwrap().max;

                let (should_reduce_left, should_reduce_right, max) = left_max
                    .checked_add(&right_max)
                    .map(|max| (false, false, max))
                    .unwrap_or_else(|| {
                        range_max
                            .checked_add(&right_max)
                            .map(|max| (true, false, max))
                            .unwrap_or_else(|| {
                                left_max
                                    .checked_add(&range_max.clone())
                                    .map(|max| (false, true, max))
                                    .unwrap_or_else(|| (true, true, range_max.clone() + range_max))
                            })
                    });

                let left = if should_reduce_left {
                    left.force_reduce()
                } else {
                    left.force_no_reduce()
                };
                let right = if should_reduce_right {
                    right.force_reduce()
                } else {
                    right.force_no_reduce()
                };

                UExpression::add(left, right).with_max(max)
            }
            Sub(box left, box right) => {
                // let `target` the target bitwidth of `left` and `right`
                // `0 <= left <= max_left`
                // `0 <= right <= max_right`
                // `- max_right <= left - right <= max_right`
                // let `n_bits_left` the number of bits needed to represent `max_left`
                // let `n = max(n_bits_left, target)`
                // let offset = 2**n`

                // `2**n - max_left <= a - b + 2 ** n <= bound  where  bound = max_left + offset`

                // If ´bound < N´, we return `bound` as the max of ´left - right`
                // Else we start again, reducing `left`. In this case `max_left` becomes `2**target - 1`
                // Else we start again, reducing `right`. In this case `offset` becomes `2**target`
                // Else we start again reducing both. In this case `bound` becomes `2**(target+1) - 1` which is always
                // smaller or equal to N for target in {8, 16, 32}

                // reduce the two terms
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

                let left_max = left.metadata.clone().unwrap().max;
                let right_bitwidth = right.metadata.clone().unwrap().bitwidth();

                let offset =
                    T::from(2u32).pow(std::cmp::max(right_bitwidth, range as u32) as usize);

                let target_offset = T::from(2u32).pow(range);

                let (should_reduce_left, should_reduce_right, max) =
                    if right_bitwidth as usize == T::get_required_bits() - 1 {
                        // if and only if `right_bitwidth` is `T::get_required_bits() - 1`, then `offset` is out of the interval
                        // [0, 2**(max_bitwidth)[, therefore we need to reduce `right`
                        left_max
                            .checked_add(&target_offset)
                            .map(|max| (false, true, max))
                            .unwrap_or_else(|| (true, true, range_max.clone() + target_offset))
                    } else {
                        left_max
                            .checked_add(&offset)
                            .map(|max| (false, false, max))
                            .unwrap_or_else(|| {
                                range_max
                                    .clone()
                                    .checked_add(&offset)
                                    .map(|max| (true, false, max))
                                    .unwrap_or_else(
                                        // this is unreachable because the max value for `range_max + offset` is
                                        // 2**32 + 2**(T::get_required_bits() - 2) < 2**(T::get_required_bits() - 1)
                                        || unreachable!(),
                                    )
                            })
                    };

                let left = if should_reduce_left {
                    left.force_reduce()
                } else {
                    left.force_no_reduce()
                };
                let right = if should_reduce_right {
                    right.force_reduce()
                } else {
                    right.force_no_reduce()
                };

                UExpression::sub(left, right).with_max(max)
            }
            Xor(box left, box right) => {
                // reduce the two terms
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

                UExpression::xor(left.force_reduce(), right.force_reduce()).with_max(range_max)
            }
            And(box left, box right) => {
                // reduce the two terms
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

                UExpression::and(left.force_reduce(), right.force_reduce()).with_max(range_max)
            }
            Or(box left, box right) => {
                // reduce the two terms
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

                UExpression::or(left.force_reduce(), right.force_reduce()).with_max(range_max)
            }
            Mult(box left, box right) => {
                // reduce the two terms
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

                let left_max = left.metadata.clone().unwrap().max;
                let right_max = right.metadata.clone().unwrap().max;

                let (should_reduce_left, should_reduce_right, max) = left_max
                    .checked_mul(&right_max)
                    .map(|max| (false, false, max))
                    .unwrap_or_else(|| {
                        range_max
                            .checked_mul(&right_max)
                            .map(|max| (true, false, max))
                            .unwrap_or_else(|| {
                                left_max
                                    .checked_mul(&range_max.clone())
                                    .map(|max| (false, true, max))
                                    .unwrap_or_else(|| (true, true, range_max.clone() * range_max))
                            })
                    });

                let left = if should_reduce_left {
                    left.force_reduce()
                } else {
                    left.force_no_reduce()
                };
                let right = if should_reduce_right {
                    right.force_reduce()
                } else {
                    right.force_no_reduce()
                };

                UExpression::mult(left, right).with_max(max)
            }
            Div(box left, box right) => {
                // reduce the two terms
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

                UExpression::div(left.force_reduce(), right.force_reduce()).with_max(range_max)
            }
            Rem(box left, box right) => {
                // reduce the two terms
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

                UExpression::rem(left.force_reduce(), right.force_reduce()).with_max(range_max)
            }
            Not(box e) => {
                let e = self.fold_uint_expression(e);

                UExpressionInner::Not(box e.force_reduce())
                    .annotate(range)
                    .with_max(range_max)
            }
            LeftShift(box e, by) => {
                // reduce both terms
                let e = self.fold_uint_expression(e);

                let e_max: num_bigint::BigUint = e.metadata.as_ref().unwrap().max.to_biguint();
                let max = e_max
                    .shl(by as usize)
                    .bitand(&(2_u128.pow(range as u32) - 1).into());

                let max = T::try_from(max).unwrap();

                UExpression::left_shift(e.force_reduce(), by).with_max(max)
            }
            RightShift(box e, by) => {
                // reduce both terms
                let e = self.fold_uint_expression(e);

                let e_max: num_bigint::BigUint = e.metadata.as_ref().unwrap().max.to_biguint();
                let max = e_max
                    .bitand(&(2_u128.pow(range as u32) - 1).into())
                    .shr(by as usize);

                let max = T::try_from(max).unwrap();

                UExpression::right_shift(e.force_reduce(), by).with_max(max)
            }
            IfElse(box condition, box consequence, box alternative) => {
                let condition = self.fold_boolean_expression(condition);
                let consequence = self.fold_uint_expression(consequence);
                let alternative = self.fold_uint_expression(alternative);

                let consequence_max = consequence.metadata.clone().unwrap().max;
                let alternative_max = alternative.metadata.clone().unwrap().max;

                let max = std::cmp::max(consequence_max.to_biguint(), alternative_max.to_biguint());

                UExpression::if_else(
                    condition,
                    consequence.force_no_reduce(),
                    alternative.force_no_reduce(),
                )
                .with_max(T::try_from(max).unwrap())
            }
        };

        assert!(res.metadata.is_some());

        res
    }

    fn fold_statement(&mut self, s: ZirStatement<'ast, T>) -> Vec<ZirStatement<'ast, T>> {
        match s {
            ZirStatement::Definition(a, e) => {
                let e = self.fold_expression(e);

                let e = match e {
                    ZirExpression::Uint(i) => {
                        let i = i.force_no_reduce();
                        self.register_uint(a.clone(), i.metadata.clone().unwrap());
                        ZirExpression::Uint(i)
                    }
                    ZirExpression::Big(b) => {
                        let b = b.force_no_reduce();
                        self.register_big(a.clone(), b.metadata.clone().unwrap());
                        ZirExpression::Big(b)
                    }
                    e => e,
                };

                vec![ZirStatement::Definition(a, e)]
            }
            // we need to put back in range to return
            ZirStatement::Return(expressions) => vec![ZirStatement::Return(
                expressions
                    .into_iter()
                    .map(|e| match e {
                        ZirExpression::Uint(e) => {
                            let e = self.fold_uint_expression(e);

                            let e = e.force_reduce();

                            ZirExpression::Uint(e)
                        }
                        ZirExpression::Big(e) => {
                            let e = self.fold_big_expression(e);

                            let e = e.force_reduce();

                            ZirExpression::Big(e)
                        }
                        e => self.fold_expression(e),
                    })
                    .collect(),
            )],
            ZirStatement::MultipleDefinition(
                lhs,
                ZirExpressionList::EmbedCall(embed, generics, arguments),
            ) => {
                match embed {
                    FlatEmbed::U64FromBits => {
                        assert_eq!(lhs.len(), 1);
                        self.register_uint(
                            lhs[0].clone(),
                            UMetadata {
                                max: T::from(2).pow(64) - T::from(1),
                                should_reduce: ShouldReduce::False,
                            },
                        );
                    }
                    FlatEmbed::U32FromBits => {
                        assert_eq!(lhs.len(), 1);
                        self.register_uint(
                            lhs[0].clone(),
                            UMetadata {
                                max: T::from(2).pow(32) - T::from(1),
                                should_reduce: ShouldReduce::False,
                            },
                        );
                    }
                    FlatEmbed::U16FromBits => {
                        assert_eq!(lhs.len(), 1);
                        self.register_uint(
                            lhs[0].clone(),
                            UMetadata {
                                max: T::from(2).pow(16) - T::from(1),
                                should_reduce: ShouldReduce::False,
                            },
                        );
                    }
                    FlatEmbed::U8FromBits => {
                        assert_eq!(lhs.len(), 1);
                        self.register_uint(
                            lhs[0].clone(),
                            UMetadata {
                                max: T::from(2).pow(8) - T::from(1),
                                should_reduce: ShouldReduce::False,
                            },
                        );
                    }
                    _ => {}
                };

                match embed {
                    FlatEmbed::U8ToBits
                    | FlatEmbed::U16ToBits
                    | FlatEmbed::U32ToBits
                    | FlatEmbed::U64ToBits => {
                        vec![ZirStatement::MultipleDefinition(
                            lhs,
                            ZirExpressionList::EmbedCall(
                                embed,
                                generics,
                                arguments
                                    .into_iter()
                                    .map(|e| match e {
                                        ZirExpression::Uint(e) => {
                                            let e = self.fold_uint_expression(e);
                                            let e = e.force_reduce();
                                            ZirExpression::Uint(e)
                                        }
                                        e => self.fold_expression(e),
                                    })
                                    .collect(),
                            ),
                        )]
                    }
                    _ => {
                        vec![ZirStatement::MultipleDefinition(
                            lhs,
                            ZirExpressionList::EmbedCall(
                                embed,
                                generics,
                                arguments
                                    .into_iter()
                                    .map(|e| self.fold_expression(e))
                                    .collect(),
                            ),
                        )]
                    }
                }
            }
            ZirStatement::Assertion(BooleanExpression::UintEq(box left, box right), metadata) => {
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

                // we can only compare two unsigned integers if they are in range
                let left = left.force_reduce();
                let right = right.force_reduce();

                vec![ZirStatement::Assertion(
                    BooleanExpression::UintEq(box left, box right),
                    metadata,
                )]
            }
            s => fold_statement(self, s),
        }
    }

    fn fold_parameter(&mut self, p: Parameter<'ast>) -> Parameter<'ast> {
        let id = match p.id.get_type() {
            Type::Uint(bitwidth) => {
                self.register_uint(p.id.clone(), UMetadata::parameter(bitwidth));
                p.id
            }
            Type::Big => {
                self.register_big(p.id.clone(), BigMetadata::parameter());
                p.id
            }
            _ => p.id,
        };

        Parameter {
            id: self.fold_variable(id),
            ..p
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::Bn128Field;

    use pretty_assertions::assert_eq;

    /// generate a test for a binary operator
    ///
    /// # Arguments
    ///
    /// * `left_max` the max value of the left argument
    /// * `expected_reduce_left` whether we expect the optimizer to reduce the left argument
    /// * `right_max` the max value of the right argument
    /// * `expected_reduce_right` whether we expect the optimizer to reduce the left argument
    /// * `res_max` the expected max value of the output
    macro_rules! uint_test {
        ( $left_max:expr, $expected_reduce_left:expr, $right_max:expr, $expected_reduce_right:expr, $op:ident, $res_max:expr ) => {{
            let left = e_with_max($left_max);

            let right = e_with_max($right_max);

            let left_expected = if $expected_reduce_left {
                force_reduce(left.clone())
            } else {
                force_no_reduce(left.clone())
            };

            let right_expected = if $expected_reduce_right {
                force_reduce(right.clone())
            } else {
                force_no_reduce(right.clone())
            };

            assert_eq!(
                UintOptimizer::new()
                    .fold_uint_expression(UExpression::$op(left.clone(), right.clone())),
                UExpression::$op(left_expected, right_expected).with_max($res_max)
            );
        }};
    }

    fn e_with_max<'a, U: Into<Bn128Field>>(max: U) -> UExpression<'a, Bn128Field> {
        UExpressionInner::Identifier("foo".into())
            .annotate(32)
            .metadata(UMetadata::with_max(max))
    }

    #[test]
    fn add() {
        // no reduction
        uint_test!(42, false, 33, false, add, 75);
        // left reduction
        uint_test!(
            Bn128Field::max_unique_value(),
            true,
            1,
            false,
            add,
            0x100000000_u128
        );
        // right reduction
        uint_test!(
            1,
            false,
            Bn128Field::max_unique_value(),
            true,
            add,
            0x100000000_u128
        );
        // right and left reductions
        uint_test!(
            Bn128Field::max_unique_value(),
            true,
            Bn128Field::max_unique_value(),
            true,
            add,
            0x1fffffffe_u128
        );
    }

    #[test]
    fn sub() {
        // no reduction
        uint_test!(42, false, 33, false, sub, 0x100000000_u128 + 42);
        // left reduction
        uint_test!(
            Bn128Field::max_unique_value(),
            true,
            1,
            false,
            sub,
            0x1ffffffff_u128
        );
        // right reduction
        uint_test!(
            1,
            false,
            Bn128Field::max_unique_value(),
            true,
            sub,
            0x100000001_u128
        );
        // right and left reductions
        uint_test!(
            Bn128Field::max_unique_value(),
            true,
            Bn128Field::max_unique_value(),
            true,
            sub,
            0x1ffffffff_u128
        );
    }

    #[test]
    fn mult() {
        // no reduction
        uint_test!(42, false, 33, false, mult, 1386);
        // left reduction
        uint_test!(
            Bn128Field::max_unique_value(),
            true,
            2,
            false,
            mult,
            0x1fffffffe_u128
        );
        // right reduction
        uint_test!(
            2,
            false,
            Bn128Field::max_unique_value(),
            true,
            mult,
            0x1fffffffe_u128
        );
        // right and left reductions
        uint_test!(
            Bn128Field::max_unique_value(),
            true,
            Bn128Field::max_unique_value(),
            true,
            mult,
            0xfffffffe00000001_u128
        );
    }

    #[test]
    fn bitwise() {
        // xor
        uint_test!(42, true, 33, true, xor, 0xffffffff_u32);
        // or
        uint_test!(42, true, 33, true, or, 0xffffffff_u32);
        // and
        uint_test!(42, true, 33, true, and, 0xffffffff_u32);
        // not
        let e = e_with_max(255);

        let e_expected = force_reduce(e.clone());

        assert_eq!(
            UintOptimizer::new().fold_uint_expression(UExpression::not(e)),
            UExpression::not(e_expected).with_max(0xffffffff_u32)
        );
    }

    #[test]
    fn right_shift() {
        fn right_shift_test<U: Into<Bn128Field>>(e_max: U, by: u32, output_max: u32) {
            let left = e_with_max(e_max);

            let right = by;

            let left_expected = force_reduce(left.clone());

            let right_expected = right;

            assert_eq!(
                UintOptimizer::new()
                    .fold_uint_expression(UExpression::right_shift(left.clone(), right)),
                UExpression::right_shift(left_expected, right_expected).with_max(output_max)
            );
        }

        right_shift_test(0xff_u128, 2, 0xff >> 2);
        right_shift_test(2, 2, 2 >> 2);
        right_shift_test(Bn128Field::max_unique_value(), 2, 0xffffffff >> 2);
    }

    #[test]
    fn left_shift() {
        fn left_shift_test<U: Into<Bn128Field>>(e_max: U, by: u32, output_max: u32) {
            let left = e_with_max(e_max);

            let right = by;

            let left_expected = force_reduce(left.clone());

            let right_expected = right;

            assert_eq!(
                UintOptimizer::new()
                    .fold_uint_expression(UExpression::left_shift(left.clone(), right)),
                UExpression::left_shift(left_expected, right_expected).with_max(output_max)
            );
        }

        left_shift_test(0xff_u128, 2, 0xff << 2);
        left_shift_test(2, 2, 2 << 2);
        left_shift_test(Bn128Field::max_unique_value(), 2, 0xffffffff << 2);
    }

    #[test]
    fn if_else() {
        // `left` and `right` are smaller than the target
        let consequence: UExpression<Bn128Field> = UExpressionInner::Identifier("a".into())
            .annotate(32)
            .metadata(UMetadata::with_max(42u32));

        let alternative = UExpressionInner::Identifier("b".into())
            .annotate(32)
            .metadata(UMetadata::with_max(33u32));

        assert_eq!(
            UintOptimizer::new()
                .fold_uint_expression(UExpression::if_else(
                    BooleanExpression::Value(true),
                    consequence,
                    alternative
                ))
                .metadata
                .unwrap()
                .max,
            Bn128Field::from(42)
        );
    }
}
