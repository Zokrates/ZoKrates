use std::ops::*;
use zokrates_ast::flat::*;
use zokrates_field::Field;

pub fn flat_expression_from_bits<T: Field>(v: Vec<FlatExpression<T>>) -> FlatExpression<T> {
    fn flat_expression_from_bits_aux<T: Field>(
        v: Vec<(T, FlatExpression<T>)>,
    ) -> FlatExpression<T> {
        match v.len() {
            0 => FlatExpression::value(T::zero()),
            1 => {
                let (coeff, var) = v[0].clone();
                FlatExpression::mul(FlatExpression::value(coeff), var)
            }
            n => {
                let (u, v) = v.split_at(n / 2);
                FlatExpression::add(
                    flat_expression_from_bits_aux(u.to_vec()),
                    flat_expression_from_bits_aux(v.to_vec()),
                )
            }
        }
    }

    flat_expression_from_bits_aux(
        v.into_iter()
            .rev()
            .enumerate()
            .map(|(index, var)| (T::from(2).pow(index), var))
            .collect::<Vec<_>>(),
    )
}
