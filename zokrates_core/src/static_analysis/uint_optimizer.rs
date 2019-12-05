use crate::typed_absy::*;
use std::collections::HashMap;
use typed_absy::bitwidth;
use typed_absy::folder::*;
use zokrates_field::field::Field;

#[derive(Default)]
pub struct UintOptimizer<'ast, T: Field> {
    ids: HashMap<TypedAssignee<'ast, T>, UMetadata>,
}

impl<'ast, T: Field> UintOptimizer<'ast, T> {
    pub fn new() -> Self {
        UintOptimizer {
            ids: HashMap::new(),
        }
    }

    pub fn optimize(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        UintOptimizer::new().fold_program(p)
    }

    fn register(&mut self, a: TypedAssignee<'ast, T>, e: TypedExpression<'ast, T>) {
        match (a, e) {
            (a, TypedExpression::Uint(e)) => {
                println!("{} := {}", a, e);
                self.ids.insert(a, e.metadata.unwrap_or(UMetadata {bitwidth: Some(42), should_reduce: Some(true)}));
            }
            (a, TypedExpression::Array(e)) => {
                let (inner_type, size) = match e.get_type() {
                    Type::Array(box inner_type, size) => (inner_type, size),
                    _ => unreachable!(),
                };

                for i in 0..size {
                    match inner_type {
                        Type::Array(..) => {
                            self.register(
                                TypedAssignee::Select(
                                    box a.clone(),
                                    box FieldElementExpression::Number(T::from(i)),
                                ),
                                ArrayExpression::select(
                                    e.clone(),
                                    FieldElementExpression::Number(T::from(i)),
                                )
                                .into(),
                            );
                        }
                        Type::Uint(..) => {
                            self.register(
                                TypedAssignee::Select(
                                    box a.clone(),
                                    box FieldElementExpression::Number(T::from(i)),
                                ),
                                UExpression::select(
                                    e.clone(),
                                    FieldElementExpression::Number(T::from(i)),
                                )
                                .into(),
                            );
                        }
                        Type::Struct(..) => unimplemented!(),
                        _ => {}
                    }
                }
            }
            (a, TypedExpression::Struct(e)) => unimplemented!(),
            _ => {}
        }
    }
}

impl<'ast, T: Field> Folder<'ast, T> for UintOptimizer<'ast, T> {
    fn fold_uint_expression(&mut self, e: UExpression<'ast, T>) -> UExpression<'ast, T> {
        let max_bitwidth = T::get_required_bits() - 1;

        let range = e.bitwidth;

        assert!(range < max_bitwidth / 2);

        println!("{:?}", e);

        if e.metadata.is_some() {
            return e;
        }

        let metadata = e.metadata;
        let inner = e.inner;

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
            Identifier(id) => Identifier(id.clone()).annotate(range).metadata(
                self.ids
                    .get(&TypedAssignee::Identifier(Variable::uint(id, range)))
                    .cloned()
                    .unwrap(),
            ),
            Add(box left, box right) => {
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
                    bitwidth: Some(range),
                    should_reduce: Some(true),
                })
            }
            Mult(box left, box right) => {
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
                    bitwidth: Some(output_width),
                    should_reduce: Some(
                        metadata
                            .map(|m| m.should_reduce.unwrap_or(false))
                            .unwrap_or(false),
                    ),
                })
            }
            Select(box array, box index) => {
                let array = self.fold_array_expression(array);
                let index = self.fold_field_expression(index);

                let (inner_type, size) = match array.get_type() {
                    Type::Array(box inner_type, size) => (inner_type, size),
                    _ => unreachable!(),
                };

                Select(box array.clone(), box index.clone())
                    .annotate(range)
                    .metadata(match (array.into_inner(), index) {
                        (ArrayExpressionInner::Value(v), FieldElementExpression::Number(n)) => {
                            let n_as_usize = n.to_dec_string().parse::<usize>().unwrap();
                            if n_as_usize < size {
                                unreachable!()
                            } else {
                                unreachable!(
                                    "out of bounds index ({} >= {}) found during static analysis",
                                    n_as_usize, size
                                );
                            }
                        }
                        (
                            ArrayExpressionInner::Identifier(id),
                            FieldElementExpression::Number(n),
                        ) => self
                            .ids
                            .get(&TypedAssignee::Select(
                                box TypedAssignee::Identifier(Variable::array(
                                    id.clone(),
                                    inner_type.clone(),
                                    size,
                                )),
                                box FieldElementExpression::Number(n.clone()).into(),
                            ))
                            .unwrap()
                            .clone(),
                        (a, i) => unreachable!("{} {}", a, i),
                    })
            }
        }
    }

    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        println!("{}", s);
        match s {
            TypedStatement::Definition(a, e) => {
                let e = self.fold_expression(e);
                self.register(a.clone(), e.clone());
                vec![TypedStatement::Definition(a, e)]
            }
            // we need to put back in range to return
            TypedStatement::Return(expressions) => vec![TypedStatement::Return(
                expressions
                    .into_iter()
                    .map(|e| match e {
                        TypedExpression::Uint(e) => {
                            let e = self.fold_uint_expression(e);

                            let e = UExpression {
                                metadata: Some(UMetadata {
                                    should_reduce: Some(true),
                                    ..e.metadata.unwrap()
                                }),
                                ..e
                            };

                            TypedExpression::Uint(e)
                        }
                        e => self.fold_expression(e),
                    })
                    .collect(),
            )],
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
                bitwidth: Some(33),
                should_reduce: Some(false),
            });

        let mut optimizer: UintOptimizer<FieldPrime> = UintOptimizer::new();

        let optimized = optimizer.fold_uint_expression(e.clone());

        assert_eq!(e, optimized);
    }
}
