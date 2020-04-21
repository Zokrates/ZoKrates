use num_bigint::BigUint;
use crate::embed::FlatEmbed;
use crate::zir::*;
use std::collections::HashMap;
use std::marker::PhantomData;
use zir::bitwidth;
use zir::folder::*;
use zokrates_field::field::Field;

#[derive(Default)]
pub struct UintOptimizer<'ast, T: Field> {
    ids: HashMap<ZirAssignee<'ast>, UMetadata>,
    phantom: PhantomData<T>,
}

impl<'ast, T: Field> UintOptimizer<'ast, T> {
    pub fn new() -> Self {
        UintOptimizer {
            ids: HashMap::new(),
            phantom: PhantomData,
        }
    }

    pub fn optimize(p: ZirProgram<'ast, T>) -> ZirProgram<'ast, T> {
        UintOptimizer::new().fold_program(p)
    }

    fn register(&mut self, a: ZirAssignee<'ast>, m: UMetadata) {
        // match (a, m) {
        //     (a, ZirExpression::Uint(e)) => {
                self.ids.insert(a, m);
            // }
            // _ => {}
        // }
    }
}

impl<'ast, T: Field> Folder<'ast, T> for UintOptimizer<'ast, T> {
    fn fold_uint_expression(&mut self, e: UExpression<'ast, T>) -> UExpression<'ast, T> {
        let max_bitwidth = T::get_required_bits() - 1;

        let max = T::max_value().into_big_uint();

        let range = e.bitwidth;

        let range_max: BigUint = (2_usize.pow(range as u32) - 1).into();

        assert!(range < max_bitwidth / 2);

        if e.metadata.is_some() {
            return e;
        }

        let metadata = e.metadata;
        let inner = e.inner;

        use self::UExpressionInner::*;

        let res = match inner {
            Value(v) => Value(v).annotate(range).metadata(UMetadata {
                max: Some(v.into()),
                bitwidth: Some(range),
                should_reduce: Some(
                    metadata
                        .map(|m| m.should_reduce.unwrap_or(false))
                        .unwrap_or(false),
                ),
            }),
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

                let left_metadata = left.metadata.clone().unwrap();
                let right_metadata = right.metadata.clone().unwrap();

                // determine the bitwidth of each term. It's their current bitwidth, unless they are tagged as `should_reduce` in which case they now have bitwidth 8
                let left_after = left_metadata.after(range);

                let right_after = right_metadata.after(range);

                let left_max = left_after.clone().max.unwrap();

                let right_max = right_after.clone().max.unwrap();

                //let output_width = std::cmp::max(left_after.bitwidth.unwrap(), right_after.bitwidth.unwrap()) + 1; // bitwidth(a + b) = max(bitwidth(a), bitwidth(b)) + 1

                if left_max.clone() + right_max.clone() > max {
                    // the addition doesnt fit, we try to reduce one term

                    if left_max.clone() + range_max.clone() <= max {
                        let right = UExpression {
                            metadata: Some(UMetadata {
                                should_reduce: Some(true),
                                ..right_after
                            }),
                            ..right
                        };

                        UExpression::add(left, right).metadata(UMetadata {
                            max: Some(left_max.clone() + range_max.clone()),
                            bitwidth: Some(std::cmp::max(left_after.bitwidth.unwrap(), range) + 1),
                            should_reduce: Some(
                                metadata
                                    .map(|m| m.should_reduce.unwrap_or(false))
                                    .unwrap_or(false),
                            ),
                        })
                    } else if right_max.clone() + range_max.clone() <= max {
                        let left = UExpression {
                            metadata: Some(UMetadata {
                                should_reduce: Some(true),
                                ..left_after
                            }),
                            ..left
                        };

                        UExpression::add(left, right).metadata(UMetadata {
                            max: Some(left_max.clone() + right_max.clone()),
                            bitwidth: Some(std::cmp::max(right_after.bitwidth.unwrap(), range) + 1),
                            should_reduce: Some(
                                metadata
                                    .map(|m| m.should_reduce.unwrap_or(false))
                                    .unwrap_or(false),
                            ),
                        })
                    } else {
                        let left = UExpression {
                            metadata: Some(UMetadata {
                                should_reduce: Some(true),
                                ..left_after
                            }),
                            ..left
                        };

                        let right = UExpression {
                            metadata: Some(UMetadata {
                                should_reduce: Some(true),
                                ..right_after
                            }),
                            ..right
                        };

                        UExpression::add(left, right).metadata(UMetadata {
                            max: Some(range_max.clone() * 2_u32),
                            bitwidth: Some(range + 1),
                            should_reduce: Some(
                                metadata
                                    .map(|m| m.should_reduce.unwrap_or(false))
                                    .unwrap_or(false),
                            ),
                        })
                    }
                } else {
                    // the addition fits, so we just add
                    UExpression::add(left, right).metadata(UMetadata {
                        max: Some(left_max.clone() + right_max.clone()),
                        bitwidth: Some(std::cmp::max(left_after.bitwidth.unwrap(), right_after.bitwidth.unwrap())),
                        should_reduce: Some(
                            metadata
                                .map(|m| m.should_reduce.unwrap_or(false))
                                .unwrap_or(false),
                        ),
                    })
                }
            }
            Sub(box left, box right) => {
                // reduce the two terms
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

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

                // a(p), b(q) both of target n (p and q their real bitwidth)
                // a(p) - b(q) can always underflow
                // instead consider s = a(p) - b(q) + 2**q which is always positive
                // the min of s is 0 and the max is 2**p + 2**q, which is smaller than 2**(max(p, q) + 1)

                // so we can use s(max(p, q) + 1) as a representation of a - b if max(p, q) + 1 < max_bitwidth

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

                    UExpression::sub(left, right).metadata(UMetadata {
                        max: Some(2_u32 * range_max),
                        bitwidth: Some(range + 1),
                        should_reduce: Some(
                            metadata
                                .map(|m| m.should_reduce.unwrap_or(false))
                                .unwrap_or(false),
                        ),
                    })
                } else {
                    UExpression::sub(left, right).metadata(UMetadata {
                        max: None,
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
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

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

                UExpression::xor(left, right).metadata(UMetadata {
                    max: Some(range_max.clone()),
                    bitwidth: Some(range),
                    should_reduce: Some(false),
                })
            }
            And(box left, box right) => {
                // reduce the two terms
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

                let left_metadata = left.metadata.clone().unwrap();
                let right_metadata = right.metadata.clone().unwrap();

                // for and we need both terms to be in range. Therefore we reduce them to being in range.
                // NB: if they are already in range, the flattening process will ignore the reduction
                let left = left.metadata(UMetadata {
                    should_reduce: Some(true),
                    ..left_metadata
                });

                let right = right.metadata(UMetadata {
                    should_reduce: Some(true),
                    ..right_metadata
                });

                UExpression::and(left, right).metadata(UMetadata {
                    max: Some(range_max.clone()),
                    bitwidth: Some(range),
                    should_reduce: Some(false),
                })
            }
            Or(box left, box right) => {
                // reduce the two terms
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

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

                UExpression::or(left, right).metadata(UMetadata {
                    max: None,
                    bitwidth: Some(range),
                    should_reduce: Some(false),
                })
            }
            Mult(box left, box right) => {
                // reduce the two terms
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

                let left_metadata = left.metadata.clone().unwrap();
                let right_metadata = right.metadata.clone().unwrap();

                // determine the bitwidth of each term. It's their current bitwidth, unless they are tagged as `should_reduce` in which case they now have bitwidth 8
                let left_after = left_metadata.after(range);

                let right_after = right_metadata.after(range);
                let output_width = left_after.bitwidth.clone().unwrap() + right_after.bitwidth.clone().unwrap(); // bitwidth(a*b) = bitwidth(a) + bitwidth(b)

                let left_max = left_after.clone().max.unwrap();

                let right_max = right_after.clone().max.unwrap();

                if left_max.clone() * right_max.clone() > max {
                    // the addition doesnt fit, we try to reduce one term

                    if left_max.clone() * range_max.clone() <= max {
                        let right = UExpression {
                            metadata: Some(UMetadata {
                                should_reduce: Some(true),
                                ..right_after
                            }),
                            ..right
                        };

                        UExpression::mult(left, right).metadata(UMetadata {
                            max: Some(left_max.clone() * range_max.clone()),
                            bitwidth: Some(std::cmp::max(left_after.bitwidth.unwrap(), range) + 1),
                            should_reduce: Some(
                                metadata
                                    .map(|m| m.should_reduce.unwrap_or(false))
                                    .unwrap_or(false),
                            ),
                        })
                    } else if right_max.clone() * range_max.clone() <= max {
                        let left = UExpression {
                            metadata: Some(UMetadata {
                                should_reduce: Some(true),
                                ..left_after
                            }),
                            ..left
                        };

                        UExpression::mult(left, right).metadata(UMetadata {
                            max: Some(left_max.clone() * right_max.clone()),
                            bitwidth: Some(std::cmp::max(right_after.bitwidth.unwrap(), range) + 1),
                            should_reduce: Some(
                                metadata
                                    .map(|m| m.should_reduce.unwrap_or(false))
                                    .unwrap_or(false),
                            ),
                        })
                    } else {
                        let left = UExpression {
                            metadata: Some(UMetadata {
                                should_reduce: Some(true),
                                ..left_after
                            }),
                            ..left
                        };

                        let right = UExpression {
                            metadata: Some(UMetadata {
                                should_reduce: Some(true),
                                ..right_after
                            }),
                            ..right
                        };

                        UExpression::mult(left, right).metadata(UMetadata {
                            max: Some(range_max.clone() * range_max.clone()),
                            bitwidth: Some(range + 1),
                            should_reduce: Some(
                                metadata
                                    .map(|m| m.should_reduce.unwrap_or(false))
                                    .unwrap_or(false),
                            ),
                        })
                    }
                } else {
                    // the addition fits, so we just add
                    UExpression::mult(left, right).metadata(UMetadata {
                        max: Some(left_max.clone() * right_max.clone()),
                        bitwidth: Some(std::cmp::max(left_after.bitwidth.unwrap(), right_after.bitwidth.unwrap())),
                        should_reduce: Some(
                            metadata
                                .map(|m| m.should_reduce.unwrap_or(false))
                                .unwrap_or(false),
                        ),
                    })
                }
            }
            Not(box e) => {
                let e = self.fold_uint_expression(e);

                let e_metadata = e.metadata.clone().unwrap();

                let e_bitwidth = range;

                let e = e.metadata(UMetadata {
                    should_reduce: Some(true),
                    ..e_metadata
                });

                UExpressionInner::Not(box e)
                    .annotate(range)
                    .metadata(UMetadata {
                        max: Some(range_max.clone()),
                        bitwidth: Some(range),
                        should_reduce: Some(true),
                    })
            }
            LeftShift(box e, box by) => {
                // reduce the two terms
                let e = self.fold_uint_expression(e);
                let by = self.fold_field_expression(by);

                let e_metadata = e.metadata.clone().unwrap();

                // for shift we need the expression to be in range. Therefore we reduce them to being in range.
                // NB: if they are already in range, the flattening process will ignore the reduction
                let e = e.metadata(UMetadata {
                    should_reduce: Some(true),
                    ..e_metadata
                });

                UExpression::left_shift(e, by).metadata(UMetadata {
                    max: Some(range_max.clone()),
                    bitwidth: Some(range),
                    should_reduce: Some(true),
                })
            }
            RightShift(box e, box by) => {
                // reduce the two terms
                let e = self.fold_uint_expression(e);
                let by = self.fold_field_expression(by);

                let e_metadata = e.metadata.clone().unwrap();

                // for shift we need the expression to be in range. Therefore we reduce them to being in range.
                // NB: if they are already in range, the flattening process will ignore the reduction
                let e = e.metadata(UMetadata {
                    should_reduce: Some(true),
                    ..e_metadata
                });

                UExpression::right_shift(e, by).metadata(UMetadata {
                    max: Some(range_max.clone()),
                    bitwidth: Some(range),
                    should_reduce: Some(true),
                })
            }
            IfElse(box condition, box consequence, box alternative) => {
                let consequence = self.fold_uint_expression(consequence);
                let alternative = self.fold_uint_expression(alternative);

                let consequence_metadata = consequence.metadata.clone().unwrap();
                let alternative_metadata = alternative.metadata.clone().unwrap();

                let consequence_bitwidth = consequence_metadata
                    .should_reduce
                    .map(|should_reduce| {
                        if should_reduce {
                            range
                        } else {
                            consequence_metadata.bitwidth.unwrap()
                        }
                    })
                    .unwrap();
                let alternative_bitwidth = alternative_metadata
                    .should_reduce
                    .map(|should_reduce| {
                        if should_reduce {
                            range
                        } else {
                            alternative_metadata.bitwidth.unwrap()
                        }
                    })
                    .unwrap();

                let output_width = std::cmp::max(consequence_bitwidth, alternative_bitwidth);

                UExpression::if_else(condition, consequence, alternative).metadata(UMetadata {
                    max: None,
                    bitwidth: Some(output_width),
                    should_reduce: Some(
                        metadata
                            .map(|m| m.should_reduce.unwrap_or(false))
                            .unwrap_or(false),
                    ),
                })
            }
            e => fold_uint_expression_inner(self, range, e).annotate(range),
        };

        assert!(res.metadata.is_some());

        res
    }

    fn fold_statement(&mut self, s: ZirStatement<'ast, T>) -> Vec<ZirStatement<'ast, T>> {
        match s {
            ZirStatement::Definition(a, e) => {
                let e = self.fold_expression(e);
                match e {
                    ZirExpression::Uint(ref i) => {
                        self.register(a.clone(), i.metadata.clone().unwrap());
                    },
                    _ => {}
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

                            let e = UExpression {
                                metadata: Some(UMetadata {
                                    should_reduce: Some(true),
                                    ..e.metadata.unwrap()
                                }),
                                ..e
                            };

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
                        self.register(lhs[0].clone(), UMetadata {
                            max: Some(BigUint::from(2_u64.pow(32_u32) - 1)),
                            bitwidth: Some(32),
                            should_reduce: Some(true),
                        });
                        vec![ZirStatement::MultipleDefinition(
                            lhs,
                            ZirExpressionList::FunctionCall(key, arguments, ty),
                        )]
                    }
                    _ => {
                        vec![ZirStatement::MultipleDefinition(
                            lhs,
                            ZirExpressionList::FunctionCall(
                                key,
                                arguments
                                    .into_iter()
                                    .map(|e| self.fold_expression(e))
                                    .collect(),
                                ty,
                            ),
                        )]
                    }
                },
            },
            // we need to put back in range to assert
            ZirStatement::Condition(lhs, rhs) => {
                match (self.fold_expression(lhs), self.fold_expression(rhs)) {
                    (ZirExpression::Uint(lhs), ZirExpression::Uint(rhs)) => {
                        let lhs_metadata = lhs.metadata.clone().unwrap();
                        let rhs_metadata = rhs.metadata.clone().unwrap();
                        vec![ZirStatement::Condition(
                            lhs.metadata(UMetadata {
                                should_reduce: Some(true),
                                ..lhs_metadata
                            })
                            .into(),
                            rhs.metadata(UMetadata {
                                should_reduce: Some(true),
                                ..rhs_metadata
                            })
                            .into(),
                        )]
                    }
                    (lhs, rhs) => vec![ZirStatement::Condition(lhs, rhs)],
                }
            }
            s => fold_statement(self, s),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn existing_metadata() {
        let e = UExpressionInner::Identifier("foo".into())
            .annotate(32)
            .metadata(UMetadata {
                max: None,
                bitwidth: Some(33),
                should_reduce: Some(false),
            });

        let mut optimizer: UintOptimizer<FieldPrime> = UintOptimizer::new();

        let optimized = optimizer.fold_uint_expression(e.clone());

        assert_eq!(e, optimized);
    }
}
