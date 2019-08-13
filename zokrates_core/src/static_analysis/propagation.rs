//! Module containing constant propagation for the typed AST
//!
//! @file propagation.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use crate::typed_absy::folder::*;
use crate::typed_absy::*;
use std::collections::HashMap;
use zokrates_field::field::Field;

pub struct Propagator<'ast, T: Field> {
    constants: HashMap<TypedAssignee<'ast, T>, TypedExpression<'ast, T>>,
}

impl<'ast, T: Field> Propagator<'ast, T> {
    fn new() -> Self {
        Propagator {
            constants: HashMap::new(),
        }
    }

    pub fn propagate(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        Propagator::new().fold_program(p)
    }
}

impl<'ast, T: Field> Folder<'ast, T> for Propagator<'ast, T> {
    fn fold_function(&mut self, f: TypedFunction<'ast, T>) -> TypedFunction<'ast, T> {
        self.constants = HashMap::new();
        fold_function(self, f)
    }

    fn fold_array_value(&mut self, v: TypedArrayValue<'ast, T>) -> TypedArrayValue<'ast, T> {
        TypedArrayValue(
            v.0.into_iter()
                .map(|v| self.fold_spread_or_expression(v))
                .flat_map(|v| match v {
                    v @ TypedSpreadOrExpression::Expression(..) => vec![v],
                    TypedSpreadOrExpression::Spread(a) => match a {
                        FieldElementArrayExpression::Value(_, v) => v.0,
                        _ => vec![TypedSpreadOrExpression::Spread(a)],
                    },
                })
                .collect(),
        )
    }

    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        let res = match s {
			TypedStatement::Declaration(v) => Some(TypedStatement::Declaration(v)),
			TypedStatement::Return(expressions) => Some(TypedStatement::Return(expressions.into_iter().map(|e| self.fold_expression(e)).collect())),
			// propagation to the defined variable if rhs is a constant
			TypedStatement::Definition(TypedAssignee::Identifier(var), expr) => {
				match self.fold_expression(expr) {
					e @ TypedExpression::Boolean(BooleanExpression::Value(..)) | e @ TypedExpression::FieldElement(FieldElementExpression::Number(..)) => {
						self.constants.insert(TypedAssignee::Identifier(var), e);
						None
					},
					TypedExpression::FieldElementArray(FieldElementArrayExpression::Value(size, array)) => {

                        let array = self.fold_array_value(array);

						match array.0.iter().all(|v| match v {
							TypedSpreadOrExpression::Expression(TypedExpression::FieldElement(FieldElementExpression::Number(..))) => true,
							_ => false
						}) {
							true => {
								// all elements of the array are constants
								self.constants.insert(TypedAssignee::Identifier(var), FieldElementArrayExpression::Value(size, array).into());
								None
							},
							false => {
								Some(TypedStatement::Definition(TypedAssignee::Identifier(var), FieldElementArrayExpression::Value(size, array).into()))
							}
						}
					},
					e => {
						Some(TypedStatement::Definition(TypedAssignee::Identifier(var), e))
					}
				}
			},
			// a[b] = c
			TypedStatement::Definition(TypedAssignee::ArrayElement(box TypedAssignee::Identifier(var), box index), expr) => {
				let index = self.fold_field_expression(index);
				let expr = self.fold_expression(expr);

				match (index, expr) {
					(
						FieldElementExpression::Number(n),
						TypedExpression::FieldElement(expr @ FieldElementExpression::Number(..))
					) => {
						// a[42] = 33
						// -> store (a[42] -> 33) in the constants, possibly overwriting the previous entry
						self.constants.entry(TypedAssignee::Identifier(var)).and_modify(|e| {
							match *e {
								TypedExpression::FieldElementArray(FieldElementArrayExpression::Value(size, ref mut v)) => {
									let n_as_usize = n.to_dec_string().parse::<usize>().unwrap();
									if n_as_usize < size {
										v.0[n_as_usize] = TypedSpreadOrExpression::Expression(expr.into());
									} else {
										panic!(format!("out of bounds index ({} >= {}) found during static analysis", n_as_usize, size));
									}
								},
								_ => panic!("constants should only store constants")
							}
						});
						None
					},
					(index, expr) => {
						// a[42] = e
						// -> remove a from the constants as one of its elements is not constant
						self.constants.remove(&TypedAssignee::Identifier(var.clone()));
						Some(TypedStatement::Definition(TypedAssignee::ArrayElement(box TypedAssignee::Identifier(var), box index), expr))
					}
				}
			},
			TypedStatement::Definition(..) => panic!("multi dimensinal arrays are not supported, this should have been caught during semantic checking"),
			// propagate lhs and rhs for conditions
			TypedStatement::Condition(e1, e2) => {
				// could stop execution here if condition is known to fail
				Some(TypedStatement::Condition(self.fold_expression(e1), self.fold_expression(e2)))
			},
			// we unrolled for loops in the previous step
			TypedStatement::For(..) => panic!("for loop is unexpected, it should have been unrolled"),
			TypedStatement::MultipleDefinition(variables, expression_list) => {
				let expression_list = self.fold_expression_list(expression_list);
				Some(TypedStatement::MultipleDefinition(variables, expression_list))
			}
		};
        match res {
            Some(v) => vec![v],
            None => vec![],
        }
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        match e {
            FieldElementExpression::Identifier(id) => {
                match self
                    .constants
                    .get(&TypedAssignee::Identifier(Variable::field_element(
                        id.clone(),
                    ))) {
                    Some(e) => match e {
                        TypedExpression::FieldElement(e) => e.clone(),
                        _ => {
                            panic!("constant stored for a field element should be a field element")
                        }
                    },
                    None => FieldElementExpression::Identifier(id),
                }
            }
            FieldElementExpression::Add(box e1, box e2) => match (
                self.fold_field_expression(e1),
                self.fold_field_expression(e2),
            ) {
                (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                    FieldElementExpression::Number(n1 + n2)
                }
                (e1, e2) => FieldElementExpression::Add(box e1, box e2),
            },
            FieldElementExpression::Sub(box e1, box e2) => match (
                self.fold_field_expression(e1),
                self.fold_field_expression(e2),
            ) {
                (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                    FieldElementExpression::Number(n1 - n2)
                }
                (e1, e2) => FieldElementExpression::Sub(box e1, box e2),
            },
            FieldElementExpression::Mult(box e1, box e2) => match (
                self.fold_field_expression(e1),
                self.fold_field_expression(e2),
            ) {
                (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                    FieldElementExpression::Number(n1 * n2)
                }
                (e1, e2) => FieldElementExpression::Mult(box e1, box e2),
            },
            FieldElementExpression::Div(box e1, box e2) => match (
                self.fold_field_expression(e1),
                self.fold_field_expression(e2),
            ) {
                (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                    FieldElementExpression::Number(n1 / n2)
                }
                (e1, e2) => FieldElementExpression::Div(box e1, box e2),
            },
            FieldElementExpression::Pow(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1);
                let e2 = self.fold_field_expression(e2);
                match (e1, e2) {
                    (_, FieldElementExpression::Number(ref n2)) if *n2 == T::from(0) => {
                        FieldElementExpression::Number(T::from(1))
                    }
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        FieldElementExpression::Number(n1.pow(n2))
                    }
                    (e1, FieldElementExpression::Number(n2)) => {
                        FieldElementExpression::Pow(box e1, box FieldElementExpression::Number(n2))
                    }
                    (_, e2) => panic!(format!(
                        "non-constant exponent {} detected during static analysis",
                        e2
                    )),
                }
            }
            FieldElementExpression::IfElse(box condition, box consequence, box alternative) => {
                let consequence = self.fold_field_expression(consequence);
                let alternative = self.fold_field_expression(alternative);
                match self.fold_boolean_expression(condition) {
                    BooleanExpression::Value(true) => consequence,
                    BooleanExpression::Value(false) => alternative,
                    c => FieldElementExpression::IfElse(box c, box consequence, box alternative),
                }
            }
            FieldElementExpression::Select(box array, box index) => {
                let array = self.fold_field_array_expression(array);
                let index = self.fold_field_expression(index);

                match (array, index) {
                    (
                        FieldElementArrayExpression::Value(size, v),
                        FieldElementExpression::Number(n),
                    ) => {
                        let n_as_usize = n.to_dec_string().parse::<usize>().unwrap();
                        if n_as_usize < size {
                            match v.get(n_as_usize) {
                                TypedExpression::FieldElement(e) => e,
                                _ => unreachable!(),
                            }
                        } else {
                            panic!(format!(
                                "out of bounds index ({} >= {}) found during static analysis",
                                n_as_usize, size
                            ));
                        }
                    }
                    (
                        FieldElementArrayExpression::Identifier(size, id),
                        FieldElementExpression::Number(n),
                    ) => match self.constants.get(&TypedAssignee::ArrayElement(
                        box TypedAssignee::Identifier(Variable::field_array(id.clone(), size)),
                        box FieldElementExpression::Number(n.clone()).into(),
                    )) {
                        Some(e) => match e {
                            TypedExpression::FieldElement(e) => e.clone(),
                            _ => panic!(""),
                        },
                        None => FieldElementExpression::Select(
                            box FieldElementArrayExpression::Identifier(size, id),
                            box FieldElementExpression::Number(n),
                        ),
                    },
                    (a, i) => FieldElementExpression::Select(box a, box i),
                }
            }
            e => fold_field_expression(self, e),
        }
    }

    fn fold_field_array_expression(
        &mut self,
        e: FieldElementArrayExpression<'ast, T>,
    ) -> FieldElementArrayExpression<'ast, T> {
        match e {
            FieldElementArrayExpression::Identifier(size, id) => {
                match self
                    .constants
                    .get(&TypedAssignee::Identifier(Variable::field_array(
                        id.clone(),
                        size,
                    ))) {
                    Some(e) => match e {
                        TypedExpression::FieldElementArray(e) => e.clone(),
                        _ => panic!("constant stored for an array should be an array"),
                    },
                    None => FieldElementArrayExpression::Identifier(size, id),
                }
            }
            FieldElementArrayExpression::Slice(box array, from, to) => {
                let slice = self.fold_field_array_expression(array);
                match slice {
                    FieldElementArrayExpression::Value(size, v) => {
                        FieldElementArrayExpression::Value(to - from, v.slice(from, to))
                    }
                    slice => FieldElementArrayExpression::Slice(box slice, from, to),
                }
            }
            e => fold_field_array_expression(self, e),
        }
    }

    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> BooleanExpression<'ast, T> {
        match e {
            BooleanExpression::Identifier(id) => match self
                .constants
                .get(&TypedAssignee::Identifier(Variable::boolean(id.clone())))
            {
                Some(e) => match e {
                    TypedExpression::Boolean(e) => e.clone(),
                    _ => panic!("constant stored for a boolean should be a boolean"),
                },
                None => BooleanExpression::Identifier(id),
            },
            BooleanExpression::Eq(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1);
                let e2 = self.fold_field_expression(e2);

                match (e1, e2) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        BooleanExpression::Value(n1 == n2)
                    }
                    (e1, e2) => BooleanExpression::Eq(box e1, box e2),
                }
            }
            BooleanExpression::Lt(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1);
                let e2 = self.fold_field_expression(e2);

                match (e1, e2) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        BooleanExpression::Value(n1 < n2)
                    }
                    (e1, e2) => BooleanExpression::Lt(box e1, box e2),
                }
            }
            BooleanExpression::Le(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1);
                let e2 = self.fold_field_expression(e2);

                match (e1, e2) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        BooleanExpression::Value(n1 <= n2)
                    }
                    (e1, e2) => BooleanExpression::Le(box e1, box e2),
                }
            }
            BooleanExpression::Gt(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1);
                let e2 = self.fold_field_expression(e2);

                match (e1, e2) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        BooleanExpression::Value(n1 > n2)
                    }
                    (e1, e2) => BooleanExpression::Gt(box e1, box e2),
                }
            }
            BooleanExpression::Ge(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1);
                let e2 = self.fold_field_expression(e2);

                match (e1, e2) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        BooleanExpression::Value(n1 >= n2)
                    }
                    (e1, e2) => BooleanExpression::Ge(box e1, box e2),
                }
            }
            BooleanExpression::Or(box e1, box e2) => {
                let e1 = self.fold_boolean_expression(e1);
                let e2 = self.fold_boolean_expression(e2);

                match (e1, e2) {
                    // reduction of constants
                    (BooleanExpression::Value(v1), BooleanExpression::Value(v2)) => {
                        BooleanExpression::Value(v1 || v2)
                    }
                    // x || true == true
                    (_, BooleanExpression::Value(true)) | (BooleanExpression::Value(true), _) => {
                        BooleanExpression::Value(true)
                    }
                    // x || false == x
                    (e, BooleanExpression::Value(false)) | (BooleanExpression::Value(false), e) => {
                        e
                    }
                    (e1, e2) => BooleanExpression::Or(box e1, box e2),
                }
            }
            BooleanExpression::And(box e1, box e2) => {
                let e1 = self.fold_boolean_expression(e1);
                let e2 = self.fold_boolean_expression(e2);

                match (e1, e2) {
                    // reduction of constants
                    (BooleanExpression::Value(v1), BooleanExpression::Value(v2)) => {
                        BooleanExpression::Value(v1 && v2)
                    }
                    // x && true == x
                    (e, BooleanExpression::Value(true)) | (BooleanExpression::Value(true), e) => e,
                    // x && false == false
                    (_, BooleanExpression::Value(false)) | (BooleanExpression::Value(false), _) => {
                        BooleanExpression::Value(false)
                    }
                    (e1, e2) => BooleanExpression::And(box e1, box e2),
                }
            }
            BooleanExpression::Not(box e) => {
                let e = self.fold_boolean_expression(e);
                match e {
                    BooleanExpression::Value(v) => BooleanExpression::Value(!v),
                    e => e,
                }
            }
            e => fold_boolean_expression(self, e),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    #[cfg(test)]
    mod expression {
        use super::*;

        #[cfg(test)]
        mod field {
            use super::*;

            #[test]
            fn add() {
                let e = FieldElementExpression::Add(
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                    box FieldElementExpression::Number(FieldPrime::from(3)),
                );

                assert_eq!(
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(FieldPrime::from(5))
                );
            }

            #[test]
            fn sub() {
                let e = FieldElementExpression::Sub(
                    box FieldElementExpression::Number(FieldPrime::from(3)),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                );

                assert_eq!(
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(FieldPrime::from(1))
                );
            }

            #[test]
            fn mult() {
                let e = FieldElementExpression::Mult(
                    box FieldElementExpression::Number(FieldPrime::from(3)),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                );

                assert_eq!(
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(FieldPrime::from(6))
                );
            }

            #[test]
            fn div() {
                let e = FieldElementExpression::Div(
                    box FieldElementExpression::Number(FieldPrime::from(6)),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                );

                assert_eq!(
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(FieldPrime::from(3))
                );
            }

            #[test]
            fn pow() {
                let e = FieldElementExpression::Pow(
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                    box FieldElementExpression::Number(FieldPrime::from(3)),
                );

                assert_eq!(
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(FieldPrime::from(8))
                );
            }

            #[test]
            fn if_else_true() {
                let e = FieldElementExpression::IfElse(
                    box BooleanExpression::Value(true),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                    box FieldElementExpression::Number(FieldPrime::from(3)),
                );

                assert_eq!(
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(FieldPrime::from(2))
                );
            }

            #[test]
            fn if_else_false() {
                let e = FieldElementExpression::IfElse(
                    box BooleanExpression::Value(false),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                    box FieldElementExpression::Number(FieldPrime::from(3)),
                );

                assert_eq!(
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(FieldPrime::from(3))
                );
            }

            #[test]
            fn select() {
                let e = FieldElementExpression::Select(
                    box FieldElementArrayExpression::Value(
                        3,
                        TypedArrayValue(vec![
                            TypedSpreadOrExpression::Expression(
                                FieldElementExpression::Number(FieldPrime::from(1)).into(),
                            ),
                            TypedSpreadOrExpression::Expression(
                                FieldElementExpression::Number(FieldPrime::from(2)).into(),
                            ),
                            TypedSpreadOrExpression::Expression(
                                FieldElementExpression::Number(FieldPrime::from(3)).into(),
                            ),
                        ]),
                    ),
                    box FieldElementExpression::Add(
                        box FieldElementExpression::Number(FieldPrime::from(1)),
                        box FieldElementExpression::Number(FieldPrime::from(1)),
                    ),
                );

                assert_eq!(
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(FieldPrime::from(3))
                );
            }
        }

        #[cfg(test)]
        mod boolean {
            use super::*;

            #[test]
            fn eq() {
                let e_true = BooleanExpression::Eq(
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                );

                let e_false = BooleanExpression::Eq(
                    box FieldElementExpression::Number(FieldPrime::from(4)),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                );

                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_true),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_false),
                    BooleanExpression::Value(false)
                );
            }

            #[test]
            fn lt() {
                let e_true = BooleanExpression::Lt(
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                    box FieldElementExpression::Number(FieldPrime::from(4)),
                );

                let e_false = BooleanExpression::Lt(
                    box FieldElementExpression::Number(FieldPrime::from(4)),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                );

                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_true),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_false),
                    BooleanExpression::Value(false)
                );
            }

            #[test]
            fn le() {
                let e_true = BooleanExpression::Le(
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                );

                let e_false = BooleanExpression::Le(
                    box FieldElementExpression::Number(FieldPrime::from(4)),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                );

                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_true),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_false),
                    BooleanExpression::Value(false)
                );
            }

            #[test]
            fn gt() {
                let e_true = BooleanExpression::Gt(
                    box FieldElementExpression::Number(FieldPrime::from(5)),
                    box FieldElementExpression::Number(FieldPrime::from(4)),
                );

                let e_false = BooleanExpression::Gt(
                    box FieldElementExpression::Number(FieldPrime::from(4)),
                    box FieldElementExpression::Number(FieldPrime::from(5)),
                );

                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_true),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_false),
                    BooleanExpression::Value(false)
                );
            }

            #[test]
            fn ge() {
                let e_true = BooleanExpression::Ge(
                    box FieldElementExpression::Number(FieldPrime::from(5)),
                    box FieldElementExpression::Number(FieldPrime::from(5)),
                );

                let e_false = BooleanExpression::Ge(
                    box FieldElementExpression::Number(FieldPrime::from(4)),
                    box FieldElementExpression::Number(FieldPrime::from(5)),
                );

                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_true),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_false),
                    BooleanExpression::Value(false)
                );
            }

            #[test]
            fn and() {
                let a_bool: Identifier = "a".into();

                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Value(true),
                            box BooleanExpression::Identifier(a_bool.clone())
                        )
                    ),
                    BooleanExpression::Identifier(a_bool.clone())
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Identifier(a_bool.clone()),
                            box BooleanExpression::Value(true),
                        )
                    ),
                    BooleanExpression::Identifier(a_bool.clone())
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Value(false),
                            box BooleanExpression::Identifier(a_bool.clone())
                        )
                    ),
                    BooleanExpression::Value(false)
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Identifier(a_bool.clone()),
                            box BooleanExpression::Value(false),
                        )
                    ),
                    BooleanExpression::Value(false)
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Value(true),
                            box BooleanExpression::Value(false),
                        )
                    ),
                    BooleanExpression::Value(false)
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Value(false),
                            box BooleanExpression::Value(true),
                        )
                    ),
                    BooleanExpression::Value(false)
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Value(true),
                            box BooleanExpression::Value(true),
                        )
                    ),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Value(false),
                            box BooleanExpression::Value(false),
                        )
                    ),
                    BooleanExpression::Value(false)
                );
            }

            #[test]
            fn or() {
                let a_bool: Identifier = "a".into();

                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Value(true),
                        box BooleanExpression::Identifier(a_bool.clone())
                    )),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Identifier(a_bool.clone()),
                        box BooleanExpression::Value(true),
                    )),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Value(false),
                        box BooleanExpression::Identifier(a_bool.clone())
                    )),
                    BooleanExpression::Identifier(a_bool.clone())
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Identifier(a_bool.clone()),
                        box BooleanExpression::Value(false),
                    )),
                    BooleanExpression::Identifier(a_bool.clone())
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Value(true),
                        box BooleanExpression::Value(false),
                    )),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Value(false),
                        box BooleanExpression::Value(true),
                    )),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Value(true),
                        box BooleanExpression::Value(true),
                    )),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Value(false),
                        box BooleanExpression::Value(false),
                    )),
                    BooleanExpression::Value(false)
                );
            }
        }
    }

    #[cfg(test)]
    mod statement {
        use super::*;

        #[cfg(test)]
        mod definition {
            use super::*;

            #[test]
            fn update_constant_array() {
                // field[2] a = [21, 22]
                // // constants should store [21, 22]
                // a[1] = 42
                // // constants should store [21, 42]

                let declaration = TypedStatement::Declaration(Variable::field_array("a".into(), 2));
                let definition = TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_array("a".into(), 2)),
                    FieldElementArrayExpression::Value(
                        2,
                        TypedArrayValue(vec![
                            TypedSpreadOrExpression::Expression(
                                FieldElementExpression::Number(FieldPrime::from(21)).into(),
                            ),
                            TypedSpreadOrExpression::Expression(
                                FieldElementExpression::Number(FieldPrime::from(22)).into(),
                            ),
                        ]),
                    )
                    .into(),
                );
                let overwrite = TypedStatement::Definition(
                    TypedAssignee::ArrayElement(
                        box TypedAssignee::Identifier(Variable::field_array("a".into(), 2)),
                        box FieldElementExpression::Number(FieldPrime::from(1)),
                    ),
                    FieldElementExpression::Number(FieldPrime::from(42)).into(),
                );

                let mut p = Propagator::new();

                p.fold_statement(declaration);
                p.fold_statement(definition);
                let expected_value: TypedExpression<FieldPrime> =
                    FieldElementArrayExpression::Value(
                        2,
                        TypedArrayValue(vec![
                            TypedSpreadOrExpression::Expression(
                                FieldElementExpression::Number(FieldPrime::from(21)).into(),
                            ),
                            TypedSpreadOrExpression::Expression(
                                FieldElementExpression::Number(FieldPrime::from(22)).into(),
                            ),
                        ]),
                    )
                    .into();

                assert_eq!(
                    p.constants
                        .get(&TypedAssignee::Identifier(Variable::field_array(
                            "a".into(),
                            2
                        )))
                        .unwrap(),
                    &expected_value
                );

                p.fold_statement(overwrite);
                let expected_value: TypedExpression<FieldPrime> =
                    FieldElementArrayExpression::Value(
                        2,
                        TypedArrayValue(vec![
                            TypedSpreadOrExpression::Expression(
                                FieldElementExpression::Number(FieldPrime::from(21)).into(),
                            ),
                            TypedSpreadOrExpression::Expression(
                                FieldElementExpression::Number(FieldPrime::from(42)).into(),
                            ),
                        ]),
                    )
                    .into();

                assert_eq!(
                    p.constants
                        .get(&TypedAssignee::Identifier(Variable::field_array(
                            "a".into(),
                            2
                        )))
                        .unwrap(),
                    &expected_value
                );
            }

            #[test]
            fn update_variable_array() {
                // propagation does NOT support "partially constant" arrays. That means that in order for updates to use propagation,
                // the array needs to have been defined as `field[3] = [value1, value2, value3]` with all values propagateable to constants

                // a passed as input
                // // constants should store nothing
                // a[1] = 42
                // // constants should store nothing

                let declaration = TypedStatement::Declaration(Variable::field_array("a".into(), 2));

                let overwrite = TypedStatement::Definition(
                    TypedAssignee::ArrayElement(
                        box TypedAssignee::Identifier(Variable::field_array("a".into(), 2)),
                        box FieldElementExpression::Number(FieldPrime::from(1)),
                    ),
                    FieldElementExpression::Number(FieldPrime::from(42)).into(),
                );

                let mut p = Propagator::new();

                p.fold_statement(declaration);
                p.fold_statement(overwrite);

                assert_eq!(
                    p.constants
                        .get(&TypedAssignee::Identifier(Variable::field_array(
                            "a".into(),
                            2
                        ))),
                    None
                );
            }
        }
    }
}
