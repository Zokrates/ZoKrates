use crate::flat::{FlatExpression, Variable};
use std::ops::*;
use zokrates_field::Field;

// util to convert a vector of `(coefficient, expression)` to a flat_expression
// we build a binary tree of additions by splitting the vector recursively
pub fn flat_expression_from_expression_summands<T: Field, U: Clone + Into<FlatExpression<T>>>(
    v: &[(T, U)],
) -> FlatExpression<T> {
    match v.len() {
        0 => FlatExpression::value(T::zero()),
        1 => {
            let (val, var) = v[0].clone();
            FlatExpression::mul(FlatExpression::value(val), var.into())
        }
        n => {
            let (u, v) = v.split_at(n / 2);
            FlatExpression::add(
                flat_expression_from_expression_summands(u),
                flat_expression_from_expression_summands(v),
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
        0 => FlatExpression::value(T::zero()),
        1 => {
            let (val, var) = v[0];
            FlatExpression::mul(
                FlatExpression::value(val),
                FlatExpression::identifier(Variable::new(var)),
            )
        }
        n => {
            let (u, v) = v.split_at(n / 2);
            FlatExpression::add(
                flat_expression_from_variable_summands(u),
                flat_expression_from_variable_summands(v),
            )
        }
    }
}
