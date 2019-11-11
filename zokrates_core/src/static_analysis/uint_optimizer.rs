use typed_absy::bitwidth;
use std::collections::HashMap;
use zokrates_field::field::Field;
use typed_absy::folder::*;
use crate::typed_absy::*;
use std::marker::PhantomData;

#[derive(Default)]
pub struct UintOptimizer<'ast, T> {
	ids: HashMap<Identifier<'ast>, UMetadata>,
	phantom: PhantomData<T>
}

impl<'ast, T: Field> UintOptimizer<'ast, T> {

	pub fn new() -> Self {
		UintOptimizer {
			ids: HashMap::new(),
			phantom: PhantomData
		}
	}

	pub fn optimize(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
		UintOptimizer::new().fold_program(p)
	}
}

impl<'ast, T: Field> Folder<'ast, T> for UintOptimizer<'ast, T> {
	fn fold_uint_expression(&mut self, e: UExpression<'ast>) -> UExpression<'ast> {
		let max_bitwidth = T::get_required_bits() - 1;

        let range = e.bitwidth;

        assert!(range < max_bitwidth / 2);

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
            Identifier(id) => Identifier(id.clone()).annotate(range).metadata(self.ids.get(&id).cloned().unwrap_or(UMetadata {
                bitwidth: Some(range),
                should_reduce: Some(
                    metadata
                        .map(|m| m.should_reduce.unwrap_or(false))
                        .unwrap_or(false),
                ),
            })),
            Add(box left, box right) => {
                // reduce the two terms
                let left = self.fold_uint_expression(left);
                let right = self.fold_uint_expression(right);

                println!("{} + {}", left, right);

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

                println!("{}", output_width);

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
        }
	}

	fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
		match s {
			TypedStatement::Definition(TypedAssignee::Identifier(id), TypedExpression::Uint(e)) => {
				let e = self.fold_uint_expression(e);
				self.ids.insert(id.id.clone(), e.metadata.clone().unwrap());
				vec![TypedStatement::Definition(TypedAssignee::Identifier(id), TypedExpression::Uint(e))]
			},
			// we need to put back in range to return
			TypedStatement::Return(expressions) => vec![TypedStatement::Return(expressions
                .into_iter()
                .map(|e| match e {
                	TypedExpression::Uint(e) => {
                		let e = self.fold_uint_expression(e);
                		let e = UExpression {
		                    metadata: Some(UMetadata {
		                        should_reduce: Some(true),
		                        bitwidth: e.metadata.unwrap().bitwidth,
		                    }),
		                    ..e
		                };

		                TypedExpression::Uint(e)
                	}
                	e => self.fold_expression(e)
                })
                .collect())],
			s => fold_statement(self, s)
		}
	}
}