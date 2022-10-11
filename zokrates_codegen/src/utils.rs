use zokrates_ast::flat::*;
use zokrates_field::Field;

pub fn flat_expression_from_bits<T: Field>(v: Vec<FlatExpression<T>>) -> FlatExpression<T> {
    fn flat_expression_from_bits_aux<T: Field>(
        v: Vec<(T, FlatExpression<T>)>,
    ) -> FlatExpression<T> {
        match v.len() {
            0 => FlatExpression::Number(T::zero()),
            1 => {
                let (coeff, var) = v[0].clone();
                FlatExpression::Mult(box FlatExpression::Number(coeff), box var)
            }
            n => {
                let (u, v) = v.split_at(n / 2);
                FlatExpression::Add(
                    box flat_expression_from_bits_aux(u.to_vec()),
                    box flat_expression_from_bits_aux(v.to_vec()),
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
