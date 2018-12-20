use field::Field;
use flat_absy::*;
use flatten::Flattener;
use typed_absy::*;
use types::Type;

impl<T: Field> Flattener<T> {
    pub(super) fn flatten_field_array_expression(
        &mut self,
        expr: FieldElementArrayExpression<T>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
    ) -> Vec<FlatExpression<T>> {
        match expr {
            FieldElementArrayExpression::Identifier(size, x) => (0..size)
                .map(|index| {
                    FlatExpression::Identifier(
                        self.get_latest_var_substitution(&format!("{}_c{}", x, index))
                            .clone(),
                    )
                })
                .collect(),
            FieldElementArrayExpression::Value(size, values) => {
                assert_eq!(size, values.len());
                values
                    .into_iter()
                    .map(|v| self.flatten_field_expression(v, statements_flattened))
                    .collect()
            }
            FieldElementArrayExpression::FunctionCall(size, id, param_expressions) => {
                let exprs_flattened = self.flatten_function_call(
                    &id,
                    vec![Type::FieldElementArray(size)],
                    param_expressions,
                    statements_flattened,
                );
                assert!(exprs_flattened.expressions.len() == size); // outside of MultipleDefinition, FunctionCalls must return a single value
                exprs_flattened.expressions
            }
        }
    }
}
