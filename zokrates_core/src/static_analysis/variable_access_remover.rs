use typed_absy::types::StructMember;
use typed_absy::{folder::*, *};
use zokrates_field::field::Field;

pub struct VariableAccessRemover<'ast, T: Field> {
    statements: Vec<TypedStatement<'ast, T>>,
}

impl<'ast, T: Field> VariableAccessRemover<'ast, T> {
    fn new() -> Self {
        Self { statements: vec![] }
    }

    pub fn apply(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        Self::new().fold_program(p)
    }

    fn select<U: Select<'ast, T> + IfElse<'ast, T>>(
        &mut self,
        a: ArrayExpression<'ast, T>,
        i: FieldElementExpression<'ast, T>,
    ) -> U {
        match i {
            FieldElementExpression::Number(i) => U::select(a, FieldElementExpression::Number(i)),
            i => {
                let size = match a.get_type().clone() {
                    Type::Array(array_ty) => array_ty.size,
                    _ => unreachable!(),
                };

                self.statements.push(TypedStatement::Condition(
                    (0..size)
                        .map(|index| {
                            BooleanExpression::FieldEq(
                                box i.clone(),
                                box FieldElementExpression::Number(index.into()).into(),
                            )
                        })
                        .fold(None, |acc, e| match acc {
                            Some(acc) => Some(BooleanExpression::Or(box acc, box e)),
                            None => Some(e),
                        })
                        .unwrap()
                        .into(),
                    BooleanExpression::Value(true).into(),
                ));

                (0..size)
                    .map(|i| U::select(a.clone(), FieldElementExpression::Number(i.into())))
                    .enumerate()
                    .rev()
                    .fold(None, |acc, (index, res)| match acc {
                        Some(acc) => Some(U::if_else(
                            BooleanExpression::FieldEq(
                                box i.clone(),
                                box FieldElementExpression::Number(index.into()),
                            ),
                            res,
                            acc,
                        )),
                        None => Some(res),
                    })
                    .unwrap()
            }
        }
    }
}

impl<'ast, T: Field> Folder<'ast, T> for VariableAccessRemover<'ast, T> {
    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        match e {
            FieldElementExpression::Select(box a, box i) => self.select(a, i),
            e => fold_field_expression(self, e),
        }
    }

    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> BooleanExpression<'ast, T> {
        match e {
            BooleanExpression::Select(box a, box i) => self.select(a, i),
            e => fold_boolean_expression(self, e),
        }
    }

    fn fold_array_expression_inner(
        &mut self,
        ty: &Type,
        size: usize,
        e: ArrayExpressionInner<'ast, T>,
    ) -> ArrayExpressionInner<'ast, T> {
        match e {
            ArrayExpressionInner::Select(box a, box i) => {
                self.select::<ArrayExpression<'ast, T>>(a, i).into_inner()
            }
            e => fold_array_expression_inner(self, ty, size, e),
        }
    }

    fn fold_struct_expression_inner(
        &mut self,
        members: &Vec<StructMember>,
        e: StructExpressionInner<'ast, T>,
    ) -> StructExpressionInner<'ast, T> {
        match e {
            StructExpressionInner::Select(box a, box i) => {
                self.select::<StructExpression<'ast, T>>(a, i).into_inner()
            }
            e => fold_struct_expression_inner(self, members, e),
        }
    }

    fn fold_uint_expression_inner(
        &mut self,
        bitwidth: usize,
        e: UExpressionInner<'ast, T>,
    ) -> UExpressionInner<'ast, T> {
        match e {
            UExpressionInner::Select(box a, box i) => {
                self.select::<UExpression<'ast, T>>(a, i).into_inner()
            }
            e => fold_uint_expression_inner(self, bitwidth, e),
        }
    }

    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        let s = fold_statement(self, s);
        self.statements.drain(..).chain(s).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn select() {
        // b = a[i]

        // ->

        // i <= 1 == true
        // b = if i == 0 then a[0] else if i == 1 then a[1] else 0

        let access: TypedStatement<FieldPrime> = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_element("b")),
            FieldElementExpression::Select(
                box ArrayExpressionInner::Identifier("a".into()).annotate(Type::FieldElement, 2),
                box FieldElementExpression::Identifier("i".into()),
            )
            .into(),
        );

        assert_eq!(
            VariableAccessRemover::new().fold_statement(access),
            vec![
                TypedStatement::Condition(
                    BooleanExpression::Or(
                        box BooleanExpression::FieldEq(
                            box FieldElementExpression::Identifier("i".into()),
                            box FieldElementExpression::Number(0.into())
                        ),
                        box BooleanExpression::FieldEq(
                            box FieldElementExpression::Identifier("i".into()),
                            box FieldElementExpression::Number(1.into())
                        )
                    )
                    .into(),
                    BooleanExpression::Value(true).into()
                ),
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("b")),
                    FieldElementExpression::if_else(
                        BooleanExpression::FieldEq(
                            box FieldElementExpression::Identifier("i".into()),
                            box FieldElementExpression::Number(0.into())
                        ),
                        FieldElementExpression::Select(
                            box ArrayExpressionInner::Identifier("a".into())
                                .annotate(Type::FieldElement, 2),
                            box FieldElementExpression::Number(0.into()),
                        ),
                        FieldElementExpression::Select(
                            box ArrayExpressionInner::Identifier("a".into())
                                .annotate(Type::FieldElement, 2),
                            box FieldElementExpression::Number(1.into()),
                        )
                    )
                    .into()
                )
            ]
        );
    }
}
