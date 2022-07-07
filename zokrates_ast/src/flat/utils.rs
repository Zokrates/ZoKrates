use crate::flat::{FlatExpression, Variable};
use zokrates_field::Field;

// util to convert a vector of `(coefficient, expression)` to a flat_expression
// we build a binary tree of additions by splitting the vector recursively
pub fn flat_expression_from_expression_summands<T: Field, U: Clone + Into<FlatExpression<T>>>(
    v: &[(T, U)],
) -> FlatExpression<T> {
    match v.len() {
        0 => FlatExpression::Number(T::zero()),
        1 => {
            let (val, var) = v[0].clone();
            FlatExpression::Mult(box FlatExpression::Number(val), box var.into())
        }
        n => {
            let (u, v) = v.split_at(n / 2);
            FlatExpression::Add(
                box flat_expression_from_expression_summands(u),
                box flat_expression_from_expression_summands(v),
            )
        }
    }
}

pub fn flat_expression_from_bits<T: Field>(v: Vec<FlatExpression<T>>) -> FlatExpression<T> {
    flat_expression_from_expression_summands(
        &v.into_iter()
            .rev()
            .enumerate()
            .map(|(index, var)| (T::from(2).pow(index), var))
            .collect::<Vec<_>>(),
    )
}

pub fn flat_expression_from_variable_summands<T: Field>(v: &[(T, usize)]) -> FlatExpression<T> {
    match v.len() {
        0 => FlatExpression::Number(T::zero()),
        1 => {
            let (val, var) = v[0].clone();
            FlatExpression::Mult(
                box FlatExpression::Number(val),
                box FlatExpression::Identifier(Variable::new(var)),
            )
        }
        n => {
            let (u, v) = v.split_at(n / 2);
            FlatExpression::Add(
                box flat_expression_from_variable_summands(u),
                box flat_expression_from_variable_summands(v),
            )
        }
    }
}
