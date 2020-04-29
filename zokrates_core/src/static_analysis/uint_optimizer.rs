use crate::embed::FlatEmbed;
use crate::zir::*;
use num_bigint::BigUint;
use std::collections::HashMap;
use std::marker::PhantomData;
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
        self.ids.insert(a, m);
    }
}

fn force_reduce<'ast, T: Field>(e: UExpression<'ast, T>) -> UExpression<'ast, T> {
    UExpression {
        metadata: Some(UMetadata {
            should_reduce: Some(true),
            ..e.metadata.unwrap()
        }),
        ..e
    }
}

fn force_no_reduce<'ast, T: Field>(e: UExpression<'ast, T>) -> UExpression<'ast, T> {
    UExpression {
        metadata: Some(UMetadata {
            should_reduce: Some(false),
            ..e.metadata.unwrap()
        }),
        ..e
    }
}

impl<'ast, T: Field> Folder<'ast, T> for UintOptimizer<'ast, T> {
    fn fold_uint_expression(&mut self, e: UExpression<'ast, T>) -> UExpression<'ast, T> {
        let max_bitwidth = T::get_required_bits() - 1;

        let range = e.bitwidth;

        let range_max: BigUint = (2_usize.pow(range as u32) - 1).into();

        assert!(range < max_bitwidth / 2);

        if e.metadata.is_some() {
            unreachable!("{:?} had metadata", e);
        }

        let metadata = e.metadata;
        let inner = e.inner;

        use self::UExpressionInner::*;

        let res = match inner {
            Value(v) => Value(v).annotate(range).metadata(UMetadata {
                max: v.into(),
                
                should_reduce: Some(false),
            }),
            Identifier(id) => Identifier(id.clone()).annotate(range).metadata(
                self.ids
                    .get(&Variable::uint(id.clone(), range))
                    .cloned()
                    .expect(&format!("identifier should have been defined: {}", id)),
            ),
            Add(box left, box right) => {
                use num::CheckedAdd;

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
                    left
                };
                let right = if should_reduce_right {
                    force_reduce(right)
                } else {
                    right
                };

                UExpression::add(left, right).metadata(UMetadata {
                    max,
                    
                    should_reduce: Some(false),
                })
            }
            Sub(box left, box right) => {
                unimplemented!()
                // // reduce the two terms
                // let left = self.fold_uint_expression(left);
                // let right = self.fold_uint_expression(right);

                // let left_metadata = left.metadata.clone().unwrap();
                // let right_metadata = right.metadata.clone().unwrap();

                // // determine the bitwidth of each term. It's their current bitwidth, unless they are tagged as `should_reduce` in which case they now have bitwidth 8
                // let left_bitwidth = left_metadata
                //     .should_reduce
                //     .map(|should_reduce| {
                //         if should_reduce {
                //             range
                //         } else {
                //             left_metadata.bitwidth.unwrap()
                //         }
                //     })
                //     .unwrap();
                // let right_bitwidth = right_metadata
                //     .should_reduce
                //     .map(|should_reduce| {
                //         if should_reduce {
                //             range
                //         } else {
                //             right_metadata.bitwidth.unwrap()
                //         }
                //     })
                //     .unwrap();

                // // a(p), b(q) both of target n (p and q their real bitwidth)
                // // a(p) - b(q) can always underflow
                // // instead consider s = a(p) - b(q) + 2**q which is always positive
                // // the min of s is 0 and the max is 2**p + 2**q, which is smaller than 2**(max(p, q) + 1)

                // // so we can use s(max(p, q) + 1) as a representation of a - b if max(p, q) + 1 < max_bitwidth

                // let output_width = std::cmp::max(left_bitwidth, right_bitwidth) + 1; // bitwidth(a + b) = max(bitwidth(a), bitwidth(b)) + 1

                // if output_width > max_bitwidth {
                //     // the addition doesnt fit, we reduce both terms first (TODO maybe one would be enough here)

                //     let left = UExpression {
                //         metadata: Some(UMetadata {
                //             should_reduce: Some(true),
                //             ..left_metadata
                //         }),
                //         ..left
                //     };

                //     let right = UExpression {
                //         metadata: Some(UMetadata {
                //             should_reduce: Some(true),
                //             ..right_metadata
                //         }),
                //         ..right
                //     };

                //     UExpression::sub(left, right).metadata(UMetadata {
                //         max: 2_u32 * range_max,
                //         bitwidth: Some(range + 1),
                //         should_reduce: Some(
                //             metadata
                //                 .map(|m| m.should_reduce.unwrap_or(false))
                //                 .unwrap_or(false),
                //         ),
                //     })
                // } else {
                //     UExpression::sub(left, right).metadata(UMetadata {
                //         max: None,
                //         bitwidth: Some(output_width),
                //         should_reduce: Some(
                //             metadata
                //                 .map(|m| m.should_reduce.unwrap_or(false))
                //                 .unwrap_or(false),
                //         ),
                //     })
                // }
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
                    max: range_max.clone(),
                    
                    should_reduce: Some(false),
                })
            }
            And(box left, box right) => {
                // reduce the two terms
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

                UExpression::and(force_reduce(left), force_reduce(right)).metadata(UMetadata {
                    max: range_max.clone(),
                    
                    should_reduce: Some(false),
                })
            }
            Or(box left, box right) => {
                // reduce the two terms
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

                UExpression::or(force_reduce(left), force_reduce(right)).metadata(UMetadata {
                    max: range_max.clone(),
                    
                    should_reduce: Some(false),
                })
            }
            Mult(box left, box right) => {
                use num::CheckedMul;

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
                    left
                };
                let right = if should_reduce_right {
                    force_reduce(right)
                } else {
                    right
                };

                UExpression::mult(left, right).metadata(UMetadata {
                    max,
                    should_reduce: Some(false),
                })
            }
            Not(box e) => {
                let e = self.fold_uint_expression(e);

                UExpressionInner::Not(box force_reduce(e))
                    .annotate(range)
                    .metadata(UMetadata {
                        max: range_max.clone(),
                        
                        should_reduce: Some(false),
                    })
            }
            LeftShift(box e, box by) => {
                // reduce the two terms
                let e = self.fold_uint_expression(e);
                let by = self.fold_field_expression(by);

                UExpression::left_shift(force_reduce(e), by).metadata(UMetadata {
                    max: range_max.clone(),
                    should_reduce: Some(true),
                })
            }
            RightShift(box e, box by) => {
                // reduce the two terms
                let e = self.fold_uint_expression(e);
                let by = self.fold_field_expression(by);

                UExpression::right_shift(force_reduce(e), by).metadata(UMetadata {
                    max: range_max.clone(),
                    
                    should_reduce: Some(false),
                })
            }
            IfElse(box condition, box consequence, box alternative) => {
                let consequence = self.fold_uint_expression(consequence);
                let alternative = self.fold_uint_expression(alternative);

                let consequence_max = consequence.metadata.clone().unwrap().max;
                let alternative_max = alternative.metadata.clone().unwrap().max;

                let max = std::cmp::max(consequence_max, alternative_max);

                UExpression::if_else(condition, consequence, alternative).metadata(UMetadata {
                    max,
                    
                    should_reduce: Some(false),
                })
            }
            e => unimplemented!("{:?}", e),
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
                        self.register(
                            lhs[0].clone(),
                            UMetadata {
                                max: BigUint::from(2_u64.pow(32_u32) - 1),
                                should_reduce: Some(false),
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

    fn fold_parameter(&mut self, p: Parameter<'ast>) -> Parameter<'ast> {
        let id = match p.id.get_type() {
            Type::Uint(bitwidth) => {
                self.register(
                    p.id.clone(),
                    UMetadata {
                        max: BigUint::from(2_u64.pow(bitwidth as u32) - 1),
                        should_reduce: Some(false),
                    },
                );
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
    use zokrates_field::field::FieldPrime;

    #[test]
    fn existing_metadata() {
        let e = UExpressionInner::Identifier("foo".into())
            .annotate(32)
            .metadata(UMetadata {
                max: BigUint::from(2_u64.pow(33_u32) - 1),
                should_reduce: Some(false),
            });

        let mut optimizer: UintOptimizer<FieldPrime> = UintOptimizer::new();

        let optimized = optimizer.fold_uint_expression(e.clone());

        assert_eq!(e, optimized);
    }
}
