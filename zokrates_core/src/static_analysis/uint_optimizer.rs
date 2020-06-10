use crate::zir::*;
use std::collections::HashMap;
use zir::folder::*;
use zokrates_field::Field;

#[derive(Default)]
pub struct UintOptimizer<'ast, T: Field> {
    ids: HashMap<ZirAssignee<'ast>, UMetadata<T>>,
}

impl<'ast, T: Field> UintOptimizer<'ast, T> {
    pub fn new() -> Self {
        UintOptimizer {
            ids: HashMap::new(),
        }
    }

    pub fn optimize(p: ZirProgram<'ast, T>) -> ZirProgram<'ast, T> {
        UintOptimizer::new().fold_program(p)
    }

    fn register(&mut self, a: ZirAssignee<'ast>, m: UMetadata<T>) {
        self.ids.insert(a, m);
    }
}

fn force_reduce<'ast, T: Field>(e: UExpression<'ast, T>) -> UExpression<'ast, T> {
    let metadata = e.metadata.unwrap();

    let should_reduce = metadata.should_reduce.make_true();

    UExpression {
        metadata: Some(UMetadata {
            should_reduce,
            ..metadata
        }),
        ..e
    }
}

fn force_no_reduce<'ast, T: Field>(e: UExpression<'ast, T>) -> UExpression<'ast, T> {
    let metadata = e.metadata.unwrap();

    let should_reduce = metadata.should_reduce.make_false();

    UExpression {
        metadata: Some(UMetadata {
            should_reduce,
            ..metadata
        }),
        ..e
    }
}

impl<'ast, T: Field> Folder<'ast, T> for UintOptimizer<'ast, T> {
    fn fold_uint_expression(&mut self, e: UExpression<'ast, T>) -> UExpression<'ast, T> {
        if e.metadata.is_some() {
            return e;
        }

        let max_bitwidth = T::get_required_bits() - 1;

        let range = e.bitwidth.to_usize();

        let range_max: T = (2_usize.pow(range as u32) - 1).into();

        assert!(range < max_bitwidth / 2);

        let inner = e.inner;

        use self::UExpressionInner::*;

        let res = match inner {
            Value(v) => Value(v).annotate(range).with_max(v),
            Identifier(id) => Identifier(id.clone()).annotate(range).metadata(
                self.ids
                    .get(&Variable::uint(id.clone(), range))
                    .cloned()
                    .expect(&format!("identifier should have been defined: {}", id)),
            ),
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
                            .clone()
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
                    force_reduce(left)
                } else {
                    force_no_reduce(left)
                };
                let right = if should_reduce_right {
                    force_reduce(right)
                } else {
                    force_no_reduce(right)
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
                            .checked_add(&target_offset.clone())
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
                    force_reduce(left)
                } else {
                    force_no_reduce(left)
                };
                let right = if should_reduce_right {
                    force_reduce(right)
                } else {
                    force_no_reduce(right)
                };

                UExpression::sub(left, right).with_max(max)
            }
            Xor(box left, box right) => {
                // reduce the two terms
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

                UExpression::xor(force_reduce(left), force_reduce(right)).with_max(range_max)
            }
            And(box left, box right) => {
                // reduce the two terms
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

                UExpression::and(force_reduce(left), force_reduce(right)).with_max(range_max)
            }
            Or(box left, box right) => {
                // reduce the two terms
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

                UExpression::or(force_reduce(left), force_reduce(right)).with_max(range_max)
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
                            .clone()
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
                    force_reduce(left)
                } else {
                    force_no_reduce(left)
                };
                let right = if should_reduce_right {
                    force_reduce(right)
                } else {
                    force_no_reduce(right)
                };

                UExpression::mult(left, right).with_max(max)
            }
            Not(box e) => {
                let e = self.fold_uint_expression(e);

                UExpressionInner::Not(box force_reduce(e))
                    .annotate(range)
                    .with_max(range_max)
            }
            LeftShift(box e, box by) => {
                // reduce the two terms
                let e = self.fold_uint_expression(e);
                let by = self.fold_field_expression(by);

                let by_u = match by {
                    FieldElementExpression::Number(ref by) => {
                        by.to_dec_string().parse::<usize>().unwrap()
                    }
                    _ => unreachable!(),
                };

                let bitwidth = e.metadata.clone().unwrap().bitwidth();

                let max =
                    T::from(2).pow(std::cmp::min(bitwidth as usize + by_u, range)) - T::from(1);

                UExpression::left_shift(force_reduce(e), by).with_max(max)
            }
            RightShift(box e, box by) => {
                // reduce the two terms
                let e = self.fold_uint_expression(e);
                let by = self.fold_field_expression(by);

                let by_u = match by {
                    FieldElementExpression::Number(ref by) => {
                        by.to_dec_string().parse::<usize>().unwrap()
                    }
                    _ => unreachable!(),
                };

                let bitwidth = e.metadata.clone().unwrap().bitwidth();

                let max = T::from(2)
                    .pow(bitwidth as usize - std::cmp::min(by_u, bitwidth as usize))
                    - T::from(1);

                UExpression::right_shift(force_reduce(e), by).with_max(max)
            }
            IfElse(box condition, box consequence, box alternative) => {
                let consequence = self.fold_uint_expression(consequence);
                let alternative = self.fold_uint_expression(alternative);

                let consequence_max = consequence.metadata.clone().unwrap().max;
                let alternative_max = alternative.metadata.clone().unwrap().max;

                let max = std::cmp::max(consequence_max.to_biguint(), alternative_max.to_biguint());

                UExpression::if_else(
                    condition,
                    force_no_reduce(consequence),
                    force_no_reduce(alternative),
                )
                .with_max(max)
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
                        let i = force_no_reduce(i);
                        self.register(a.clone(), i.metadata.clone().unwrap());
                        ZirExpression::Uint(i)
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

                            let e = force_reduce(e);

                            ZirExpression::Uint(e)
                        }
                        e => self.fold_expression(e),
                    })
                    .collect(),
            )],
            ZirStatement::MultipleDefinition(lhs, rhs) => match rhs {
                ZirExpressionList::FunctionCall(key, arguments, ty) => match key.clone().id {
                    "_U32_FROM_BITS" => {
                        assert_eq!(lhs.len(), 1);
                        self.register(
                            lhs[0].clone(),
                            UMetadata {
                                max: T::from(2).pow(32) - T::from(1),
                                should_reduce: ShouldReduce::False,
                            },
                        );
                        vec![ZirStatement::MultipleDefinition(
                            lhs,
                            ZirExpressionList::FunctionCall(key, arguments, ty),
                        )]
                    }
                    "_U16_FROM_BITS" => {
                        assert_eq!(lhs.len(), 1);
                        self.register(
                            lhs[0].clone(),
                            UMetadata {
                                max: T::from(2).pow(16) - T::from(1),
                                should_reduce: ShouldReduce::False,
                            },
                        );
                        vec![ZirStatement::MultipleDefinition(
                            lhs,
                            ZirExpressionList::FunctionCall(key, arguments, ty),
                        )]
                    }
                    "_U8_FROM_BITS" => {
                        assert_eq!(lhs.len(), 1);
                        self.register(
                            lhs[0].clone(),
                            UMetadata {
                                max: T::from(2).pow(8) - T::from(1),
                                should_reduce: ShouldReduce::False,
                            },
                        );
                        vec![ZirStatement::MultipleDefinition(
                            lhs,
                            ZirExpressionList::FunctionCall(key, arguments, ty),
                        )]
                    }
                    _ => vec![ZirStatement::MultipleDefinition(
                        lhs,
                        ZirExpressionList::FunctionCall(
                            key,
                            arguments
                                .into_iter()
                                .map(|e| self.fold_expression(e))
                                .collect(),
                            ty,
                        ),
                    )],
                },
            },
            // we need to put back in range to assert
            ZirStatement::Condition(lhs, rhs) => {
                match (self.fold_expression(lhs), self.fold_expression(rhs)) {
                    (ZirExpression::Uint(lhs), ZirExpression::Uint(rhs)) => {
                        vec![ZirStatement::Condition(
                            force_reduce(lhs).into(),
                            force_reduce(rhs).into(),
                        )]
                    }
                    (lhs, rhs) => vec![ZirStatement::Condition(lhs, rhs)],
                }
            }
            s => fold_statement(self, s),
        }
    }

    fn fold_parameter(&mut self, p: Parameter<'ast>) -> Parameter<'ast> {
        let id = match p.id.get_type() {
            Type::Uint(bitwidth) => {
                self.register(p.id.clone(), UMetadata::parameter(bitwidth));
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

    extern crate pretty_assertions;
    use self::pretty_assertions::assert_eq;

    macro_rules! uint_test {
        ( $left_max:expr, $left_reduce:expr, $right_max:expr, $right_reduce:expr, $method:ident, $res_max:expr  ) => {{
            let left = e_with_max($left_max);

            let right = e_with_max($right_max);

            let left_expected = if $left_reduce {
                force_reduce(left.clone())
            } else {
                force_no_reduce(left.clone())
            };

            let right_expected = if $right_reduce {
                force_reduce(right.clone())
            } else {
                force_no_reduce(right.clone())
            };

            assert_eq!(
                UintOptimizer::new()
                    .fold_uint_expression(UExpression::$method(left.clone(), right.clone())),
                UExpression::$method(left_expected, right_expected).with_max($res_max)
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
        let e = e_with_max(255);

        let e_expected = force_reduce(e.clone());

        assert_eq!(
            UintOptimizer::new().fold_uint_expression(UExpression::right_shift(
                e,
                FieldElementExpression::Number(Bn128Field::from(2))
            )),
            UExpression::right_shift(
                e_expected,
                FieldElementExpression::Number(Bn128Field::from(2))
            )
            .with_max(63)
        );

        let e = e_with_max(2);

        let e_expected = force_reduce(e.clone());

        assert_eq!(
            UintOptimizer::new().fold_uint_expression(UExpression::right_shift(
                e,
                FieldElementExpression::Number(Bn128Field::from(2))
            )),
            UExpression::right_shift(
                e_expected,
                FieldElementExpression::Number(Bn128Field::from(2))
            )
            .with_max(0)
        );
    }

    #[test]
    fn left_shift() {
        let e = e_with_max(255);

        let e_expected = force_reduce(e.clone());

        assert_eq!(
            UintOptimizer::new().fold_uint_expression(UExpression::left_shift(
                e,
                FieldElementExpression::Number(Bn128Field::from(2))
            )),
            UExpression::left_shift(
                e_expected,
                FieldElementExpression::Number(Bn128Field::from(2))
            )
            .with_max(1023)
        );

        let e = e_with_max(0xffffffff_u32);

        let e_expected = force_reduce(e.clone());

        assert_eq!(
            UintOptimizer::new().fold_uint_expression(UExpression::left_shift(
                e,
                FieldElementExpression::Number(Bn128Field::from(2))
            )),
            UExpression::left_shift(
                e_expected,
                FieldElementExpression::Number(Bn128Field::from(2))
            )
            .with_max(0xffffffff_u32)
        );
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
