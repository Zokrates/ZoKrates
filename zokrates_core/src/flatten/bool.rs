use flat_absy::*;
use flatten::Flattener;
use helpers::{DirectiveStatement, Helper, RustHelper};
use typed_absy::*;
use zokrates_field::field::Field;

impl<T: Field> Flattener<T> {
    /// Flattens a boolean expression
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `condition` - `Condition` that will be flattened.
    ///
    /// # Postconditions
    ///
    /// * `flatten_boolean_expressions` always returns a linear expression,
    /// * in order to preserve composability.
    pub(super) fn flatten_boolean_expression(
        &mut self,
        expression: BooleanExpression<T>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
    ) -> FlatExpression<T> {
        // those will be booleans in the future
        match expression {
            BooleanExpression::Identifier(x) => {
                FlatExpression::Identifier(self.bijection.get_by_left(&x).unwrap().clone())
            }
            BooleanExpression::Lt(box lhs, box rhs) => {
                // We know from semantic checking that lhs and rhs have the same type
                // What the expression will flatten to depends on that type

                let field_bits = T::get_required_bits();

                let lhs_flattened = self.flatten_field_expression(lhs, statements_flattened);
                let rhs_flattened = self.flatten_field_expression(rhs, statements_flattened);

                // lhs
                let lhs_id = self.use_sym();
                statements_flattened.push(FlatStatement::Definition(lhs_id, lhs_flattened));

                // check that lhs and rhs are within the right range, ie, their last two bits are zero

                // lhs
                {
                    // define variables for the bits
                    let lhs_bits: Vec<FlatVariable> =
                        (0..field_bits).map(|_| self.use_sym()).collect();

                    // add a directive to get the bits
                    statements_flattened.push(FlatStatement::Directive(DirectiveStatement::new(
                        lhs_bits.clone(),
                        Helper::Rust(RustHelper::Bits),
                        vec![lhs_id],
                    )));

                    // bitness checks
                    for i in 0..field_bits - 2 {
                        statements_flattened.push(FlatStatement::Condition(
                            FlatExpression::Identifier(lhs_bits[i + 2]),
                            FlatExpression::Mult(
                                box FlatExpression::Identifier(lhs_bits[i + 2]),
                                box FlatExpression::Identifier(lhs_bits[i + 2]),
                            ),
                        ));
                    }

                    // bit decomposition check
                    let mut lhs_sum = FlatExpression::Number(T::from(0));

                    for i in 0..field_bits - 2 {
                        lhs_sum = FlatExpression::Add(
                            box lhs_sum,
                            box FlatExpression::Mult(
                                box FlatExpression::Identifier(lhs_bits[i + 2]),
                                box FlatExpression::Number(T::from(2).pow(field_bits - 2 - i - 1)),
                            ),
                        );
                    }

                    statements_flattened.push(FlatStatement::Condition(
                        FlatExpression::Identifier(lhs_id),
                        lhs_sum,
                    ));
                }

                // rhs
                let rhs_id = self.use_sym();
                statements_flattened.push(FlatStatement::Definition(rhs_id, rhs_flattened));

                // rhs
                {
                    // define variables for the bits
                    let rhs_bits: Vec<FlatVariable> =
                        (0..field_bits).map(|_| self.use_sym()).collect();

                    // add a directive to get the bits
                    statements_flattened.push(FlatStatement::Directive(DirectiveStatement::new(
                        rhs_bits.clone(),
                        Helper::Rust(RustHelper::Bits),
                        vec![rhs_id],
                    )));

                    // bitness checks
                    for i in 0..field_bits - 2 {
                        statements_flattened.push(FlatStatement::Condition(
                            FlatExpression::Identifier(rhs_bits[i + 2]),
                            FlatExpression::Mult(
                                box FlatExpression::Identifier(rhs_bits[i + 2]),
                                box FlatExpression::Identifier(rhs_bits[i + 2]),
                            ),
                        ));
                    }

                    // bit decomposition check
                    let mut rhs_sum = FlatExpression::Number(T::from(0));

                    for i in 0..field_bits - 2 {
                        rhs_sum = FlatExpression::Add(
                            box rhs_sum,
                            box FlatExpression::Mult(
                                box FlatExpression::Identifier(rhs_bits[i + 2]),
                                box FlatExpression::Number(T::from(2).pow(field_bits - 2 - i - 1)),
                            ),
                        );
                    }

                    statements_flattened.push(FlatStatement::Condition(
                        FlatExpression::Identifier(rhs_id),
                        rhs_sum,
                    ));
                }

                // sym = (lhs * 2) - (rhs * 2)
                let subtraction_result_id = self.use_sym();

                statements_flattened.push(FlatStatement::Definition(
                    subtraction_result_id,
                    FlatExpression::Sub(
                        box FlatExpression::Mult(
                            box FlatExpression::Number(T::from(2)),
                            box FlatExpression::Identifier(lhs_id),
                        ),
                        box FlatExpression::Mult(
                            box FlatExpression::Number(T::from(2)),
                            box FlatExpression::Identifier(rhs_id),
                        ),
                    ),
                ));

                // define variables for the bits
                let sub_bits: Vec<FlatVariable> = (0..field_bits).map(|_| self.use_sym()).collect();

                // add a directive to get the bits
                statements_flattened.push(FlatStatement::Directive(DirectiveStatement::new(
                    sub_bits.clone(),
                    Helper::Rust(RustHelper::Bits),
                    vec![subtraction_result_id],
                )));

                // bitness checks
                for i in 0..field_bits {
                    statements_flattened.push(FlatStatement::Condition(
                        FlatExpression::Identifier(sub_bits[i]),
                        FlatExpression::Mult(
                            box FlatExpression::Identifier(sub_bits[i]),
                            box FlatExpression::Identifier(sub_bits[i]),
                        ),
                    ));
                }

                // sum(sym_b{i} * 2**i)
                let mut expr = FlatExpression::Number(T::from(0));

                for i in 0..field_bits {
                    expr = FlatExpression::Add(
                        box expr,
                        box FlatExpression::Mult(
                            box FlatExpression::Identifier(sub_bits[i]),
                            box FlatExpression::Number(T::from(2).pow(field_bits - i - 1)),
                        ),
                    );
                }

                statements_flattened.push(FlatStatement::Condition(
                    FlatExpression::Identifier(subtraction_result_id),
                    expr,
                ));

                FlatExpression::Identifier(sub_bits[0])
            }
            BooleanExpression::Eq(box lhs, box rhs) => {
                // We know from semantic checking that lhs and rhs have the same type
                // What the expression will flatten to depends on that type

                // Wanted: (Y = (X != 0) ? 1 : 0)
                // X = a - b
                // # Y = if X == 0 then 0 else 1 fi
                // # M = if X == 0 then 1 else 1/X fi
                // Y == X * M
                // 0 == (1-Y) * X

                let name_x = self.use_sym();
                let name_y = self.use_sym();
                let name_m = self.use_sym();
                let name_1_y = self.use_sym();

                let x = self.flatten_field_expression(
                    FieldElementExpression::Sub(box lhs, box rhs),
                    statements_flattened,
                );

                statements_flattened.push(FlatStatement::Definition(name_x, x));
                statements_flattened.push(FlatStatement::Directive(DirectiveStatement::new(
                    vec![name_y, name_m],
                    Helper::Rust(RustHelper::ConditionEq),
                    vec![name_x],
                )));
                statements_flattened.push(FlatStatement::Condition(
                    FlatExpression::Identifier(name_y),
                    FlatExpression::Mult(
                        box FlatExpression::Identifier(name_x),
                        box FlatExpression::Identifier(name_m),
                    ),
                ));
                statements_flattened.push(FlatStatement::Definition(
                    name_1_y,
                    FlatExpression::Sub(
                        box FlatExpression::Number(T::one()),
                        box FlatExpression::Identifier(name_y),
                    ),
                ));
                statements_flattened.push(FlatStatement::Condition(
                    FlatExpression::Number(T::zero()),
                    FlatExpression::Mult(
                        box FlatExpression::Identifier(name_1_y),
                        box FlatExpression::Identifier(name_x),
                    ),
                ));

                FlatExpression::Identifier(name_1_y)
            }
            BooleanExpression::Le(box lhs, box rhs) => {
                let lt = self.flatten_boolean_expression(
                    BooleanExpression::Lt(box lhs.clone(), box rhs.clone()),
                    statements_flattened,
                );
                let eq = self.flatten_boolean_expression(
                    BooleanExpression::Eq(box lhs.clone(), box rhs.clone()),
                    statements_flattened,
                );
                FlatExpression::Add(box eq, box lt)
            }
            BooleanExpression::Gt(lhs, rhs) => self
                .flatten_boolean_expression(BooleanExpression::Lt(rhs, lhs), statements_flattened),
            BooleanExpression::Ge(lhs, rhs) => self
                .flatten_boolean_expression(BooleanExpression::Le(rhs, lhs), statements_flattened),
            BooleanExpression::Or(box lhs, box rhs) => {
                let x = box self.flatten_boolean_expression(lhs, statements_flattened);
                let y = box self.flatten_boolean_expression(rhs, statements_flattened);
                assert!(x.is_linear() && y.is_linear());
                let name_x_and_y = self.use_sym();
                statements_flattened.push(FlatStatement::Definition(
                    name_x_and_y,
                    FlatExpression::Mult(x.clone(), y.clone()),
                ));
                FlatExpression::Sub(
                    box FlatExpression::Add(x, y),
                    box FlatExpression::Identifier(name_x_and_y),
                )
            }
            BooleanExpression::And(box lhs, box rhs) => {
                let x = self.flatten_boolean_expression(lhs, statements_flattened);
                let y = self.flatten_boolean_expression(rhs, statements_flattened);

                let name_x_and_y = self.use_sym();
                assert!(x.is_linear() && y.is_linear());
                statements_flattened.push(FlatStatement::Definition(
                    name_x_and_y,
                    FlatExpression::Mult(box x, box y),
                ));

                FlatExpression::Identifier(name_x_and_y)
            }
            BooleanExpression::Not(box exp) => {
                let x = self.flatten_boolean_expression(exp, statements_flattened);
                FlatExpression::Sub(box FlatExpression::Number(T::one()), box x)
            }
            BooleanExpression::Value(b) => FlatExpression::Number(match b {
                true => T::from(1),
                false => T::from(0),
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn geq_leq() {
        let mut flattener = Flattener::new();
        let expression_le = BooleanExpression::Le(
            box FieldElementExpression::Number(FieldPrime::from(32)),
            box FieldElementExpression::Number(FieldPrime::from(4)),
        );

        let expression_ge = BooleanExpression::Ge(
            box FieldElementExpression::Number(FieldPrime::from(32)),
            box FieldElementExpression::Number(FieldPrime::from(4)),
        );

        flattener.flatten_boolean_expression(expression_le, &mut vec![]);

        flattener.flatten_boolean_expression(expression_ge, &mut vec![]);
    }

    #[test]
    fn if_else() {
        let mut flattener = Flattener::new();
        let expression = FieldElementExpression::IfElse(
            box BooleanExpression::Eq(
                box FieldElementExpression::Number(FieldPrime::from(32)),
                box FieldElementExpression::Number(FieldPrime::from(4)),
            ),
            box FieldElementExpression::Number(FieldPrime::from(12)),
            box FieldElementExpression::Number(FieldPrime::from(51)),
        );

        flattener.load_corelib();

        let _expression_flattened = flattener.flatten_field_expression(expression, &mut vec![]);
    }

    #[test]
    fn bool_and() {
        let expression = FieldElementExpression::IfElse(
            box BooleanExpression::And(
                box BooleanExpression::Eq(
                    box FieldElementExpression::Number(FieldPrime::from(4)),
                    box FieldElementExpression::Number(FieldPrime::from(4)),
                ),
                box BooleanExpression::Lt(
                    box FieldElementExpression::Number(FieldPrime::from(4)),
                    box FieldElementExpression::Number(FieldPrime::from(20)),
                ),
            ),
            box FieldElementExpression::Number(FieldPrime::from(12)),
            box FieldElementExpression::Number(FieldPrime::from(51)),
        );

        let mut flattener = Flattener::new();
        flattener.load_corelib();
        let _expression_flattened = flattener.flatten_field_expression(expression, &mut vec![]);
    }
}
