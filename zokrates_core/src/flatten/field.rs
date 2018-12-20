use field::Field;
use flat_absy::*;
use flatten::Flattener;
use helpers::{DirectiveStatement, Helper, RustHelper};
use typed_absy::*;
use types::Type;

impl<T: Field> Flattener<T> {
    pub(super) fn flatten_field_expression(
        &mut self,
        expr: FieldElementExpression<T>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
    ) -> FlatExpression<T> {
        match expr {
            FieldElementExpression::Number(x) => FlatExpression::Number(x), // force to be a field element
            FieldElementExpression::Identifier(x) => {
                FlatExpression::Identifier(self.bijection.get_by_left(&x).unwrap().clone())
            }
            FieldElementExpression::Add(box left, box right) => {
                let left_flattened = self.flatten_field_expression(left, statements_flattened);
                let right_flattened = self.flatten_field_expression(right, statements_flattened);
                let new_left = if left_flattened.is_linear() {
                    left_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened.push(FlatStatement::Definition(id, left_flattened));
                    FlatExpression::Identifier(id)
                };
                let new_right = if right_flattened.is_linear() {
                    right_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened.push(FlatStatement::Definition(id, right_flattened));
                    FlatExpression::Identifier(id)
                };
                FlatExpression::Add(box new_left, box new_right)
            }
            FieldElementExpression::Sub(box left, box right) => {
                let left_flattened = self.flatten_field_expression(left, statements_flattened);
                let right_flattened = self.flatten_field_expression(right, statements_flattened);
                let new_left = if left_flattened.is_linear() {
                    left_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened.push(FlatStatement::Definition(id, left_flattened));
                    FlatExpression::Identifier(id)
                };
                let new_right = if right_flattened.is_linear() {
                    right_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened.push(FlatStatement::Definition(id, right_flattened));
                    FlatExpression::Identifier(id)
                };
                FlatExpression::Sub(box new_left, box new_right)
            }
            FieldElementExpression::Mult(box left, box right) => {
                let left_flattened = self.flatten_field_expression(left, statements_flattened);
                let right_flattened = self.flatten_field_expression(right, statements_flattened);
                let new_left = if left_flattened.is_linear() {
                    if let FlatExpression::Sub(..) = left_flattened {
                        let id = self.use_sym();
                        statements_flattened.push(FlatStatement::Definition(id, left_flattened));
                        FlatExpression::Identifier(id)
                    } else {
                        left_flattened
                    }
                } else {
                    let id = self.use_sym();
                    statements_flattened.push(FlatStatement::Definition(id, left_flattened));
                    FlatExpression::Identifier(id)
                };
                let new_right = if right_flattened.is_linear() {
                    if let FlatExpression::Sub(..) = right_flattened {
                        let id = self.use_sym();
                        statements_flattened.push(FlatStatement::Definition(id, right_flattened));
                        FlatExpression::Identifier(id)
                    } else {
                        right_flattened
                    }
                } else {
                    let id = self.use_sym();
                    statements_flattened.push(FlatStatement::Definition(id, right_flattened));
                    FlatExpression::Identifier(id)
                };
                FlatExpression::Mult(box new_left, box new_right)
            }
            FieldElementExpression::Div(box left, box right) => {
                let left_flattened = self.flatten_field_expression(left, statements_flattened);
                let right_flattened = self.flatten_field_expression(right, statements_flattened);
                let new_left: FlatExpression<T> = {
                    let id = self.use_sym();
                    statements_flattened.push(FlatStatement::Definition(id, left_flattened));
                    id.into()
                };
                let new_right: FlatExpression<T> = {
                    let id = self.use_sym();
                    statements_flattened.push(FlatStatement::Definition(id, right_flattened));
                    id.into()
                };

                let invb = self.use_sym();
                let inverse = self.use_sym();

                // # invb = 1/b
                statements_flattened.push(FlatStatement::Directive(DirectiveStatement::new(
                    vec![invb],
                    Helper::Rust(RustHelper::Div),
                    vec![FlatExpression::Number(T::one()), new_right.clone()],
                )));

                // assert(invb * b == 1)
                statements_flattened.push(FlatStatement::Condition(
                    FlatExpression::Number(T::one()),
                    FlatExpression::Mult(box invb.into(), box new_right.clone().into()),
                ));

                // # c = a/b
                statements_flattened.push(FlatStatement::Directive(DirectiveStatement::new(
                    vec![inverse],
                    Helper::Rust(RustHelper::Div),
                    vec![new_left.clone(), new_right.clone()],
                )));

                // assert(c * b == a)
                statements_flattened.push(FlatStatement::Condition(
                    new_left.into(),
                    FlatExpression::Mult(box new_right, box inverse.into()),
                ));

                inverse.into()
            }
            FieldElementExpression::Pow(box base, box exponent) => {
                match exponent {
                    FieldElementExpression::Number(ref e) => {
                        // flatten the base expression
                        let base_flattened = self
                            .flatten_field_expression(base.clone(), statements_flattened)
                            .apply_recursive_substitution(&self.substitution);

                        // we require from the base to be linear
                        // TODO change that
                        assert!(base_flattened.is_linear());

                        match e {
                            e if *e == T::zero() => FlatExpression::Number(T::one()),
                            // flatten(base ** 1) == flatten(base)
                            e if *e == T::one() => base_flattened,
                            // flatten(base ** 2) == flatten(base) * flatten(base)
                            // in this case, no need to define an intermediate variable
                            // as if a is linear, a ** 2 quadratic
                            e if *e == T::from(2) => {
                                FlatExpression::Mult(box base_flattened.clone(), box base_flattened)
                            }
                            // flatten(base ** n) = flatten(base) * flatten(base ** (n-1))
                            e => {
                                // flatten(base ** (n-1))
                                let tmp_expression = self
                                    .flatten_field_expression(
                                        FieldElementExpression::Pow(
                                            box base,
                                            box FieldElementExpression::Number(
                                                e.clone() - T::one(),
                                            ),
                                        ),
                                        statements_flattened,
                                    )
                                    .apply_recursive_substitution(&self.substitution);

                                let id = self.use_sym();

                                statements_flattened
                                    .push(FlatStatement::Definition(id, tmp_expression));

                                FlatExpression::Mult(
                                    box FlatExpression::Identifier(id),
                                    box base_flattened,
                                )
                            }
                        }
                    }
                    _ => panic!("Expected number as pow exponent"),
                }
            }
            FieldElementExpression::IfElse(box condition, box consequent, box alternative) => self
                .flatten_function_call(
                    &"_if_else_field".to_string(),
                    vec![Type::FieldElement],
                    vec![condition.into(), consequent.into(), alternative.into()],
                    statements_flattened,
                )
                .expressions[0]
                .clone(),
            FieldElementExpression::FunctionCall(id, param_expressions) => {
                let exprs_flattened = self.flatten_function_call(
                    &id,
                    vec![Type::FieldElement],
                    param_expressions,
                    statements_flattened,
                );
                assert!(exprs_flattened.expressions.len() == 1); // outside of MultipleDefinition, FunctionCalls must return a single value
                exprs_flattened.expressions[0].clone()
            }
            FieldElementExpression::Select(box array, box index) => {
                match index {
                    FieldElementExpression::Number(n) => match array {
                        FieldElementArrayExpression::Identifier(size, id) => {
                            assert!(n < T::from(size));
                            FlatExpression::Identifier(
                                self.get_latest_var_substitution(&format!("{}_c{}", id, n))
                                    .clone(),
                            )
                        }
                        FieldElementArrayExpression::Value(size, expressions) => {
                            assert!(n < T::from(size));
                            self.flatten_field_expression(
                                expressions[n.to_dec_string().parse::<usize>().unwrap()].clone(),
                                statements_flattened,
                            )
                            .apply_recursive_substitution(&self.substitution)
                        }
                        FieldElementArrayExpression::FunctionCall(..) => {
                            unimplemented!("please use intermediate variables for now")
                        }
                    },
                    e => {
                        let size = array.size();
                        // we have array[e] with e an arbitrary expression
                        // first we check that e is in 0..array.len(), so we check that sum(if e == i then 1 else 0) == 1
                        // here depending on the size, we could use a proper range check based on bits
                        let range_check = (0..size)
                            .map(|i| {
                                FieldElementExpression::IfElse(
                                    box BooleanExpression::Eq(
                                        box e.clone(),
                                        box FieldElementExpression::Number(T::from(i)),
                                    ),
                                    box FieldElementExpression::Number(T::from(1)),
                                    box FieldElementExpression::Number(T::from(0)),
                                )
                            })
                            .fold(FieldElementExpression::Number(T::from(0)), |acc, e| {
                                FieldElementExpression::Add(box acc, box e)
                            });

                        let range_check_statement = TypedStatement::Condition(
                            FieldElementExpression::Number(T::from(1)).into(),
                            range_check.into(),
                        );

                        let range_check = self.flatten_statement(range_check_statement);

                        statements_flattened.extend(range_check);

                        // now we flatten to sum(if e == i then array[i] else 0)
                        let lookup = (0..size)
                            .map(|i| {
                                FieldElementExpression::IfElse(
                                    box BooleanExpression::Eq(
                                        box e.clone(),
                                        box FieldElementExpression::Number(T::from(i)),
                                    ),
                                    box match array.clone() {
                                        FieldElementArrayExpression::Identifier(_, id) => {
                                            FieldElementExpression::Identifier(format!(
                                                "{}_c{}",
                                                id, i
                                            ))
                                        }
                                        FieldElementArrayExpression::Value(size, expressions) => {
                                            assert_eq!(size, expressions.len());
                                            expressions[i].clone()
                                        }
                                        FieldElementArrayExpression::FunctionCall(..) => {
                                            unimplemented!(
                                                "please use intermediate variables for now"
                                            )
                                        }
                                    },
                                    box FieldElementExpression::Number(T::from(0)),
                                )
                            })
                            .fold(FieldElementExpression::Number(T::from(0)), |acc, e| {
                                FieldElementExpression::Add(box acc, box e)
                            });

                        self.flatten_field_expression(lookup, statements_flattened)
                            .apply_recursive_substitution(&self.substitution)
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use absy::Variable;
    use field::FieldPrime;

    #[test]
    fn array_selection() {
        // field[3] foo = [1, 2, 3]
        // foo[1]

        let mut flattener = Flattener::new();

        let statement = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_array("foo", 3)),
            FieldElementArrayExpression::Value(
                3,
                vec![
                    FieldElementExpression::Number(FieldPrime::from(1)),
                    FieldElementExpression::Number(FieldPrime::from(2)),
                    FieldElementExpression::Number(FieldPrime::from(3)),
                ],
            )
            .into(),
        );

        let expression = FieldElementExpression::Select(
            box FieldElementArrayExpression::Identifier(3, String::from("foo")),
            box FieldElementExpression::Number(FieldPrime::from(1)),
        );

        let _statements_flattened = flattener.flatten_statement(statement);

        let flat_expression = flattener.flatten_field_expression(expression, &mut vec![]);

        assert_eq!(
            flat_expression,
            FlatExpression::Identifier(FlatVariable::new(1)),
        );
    }
}
