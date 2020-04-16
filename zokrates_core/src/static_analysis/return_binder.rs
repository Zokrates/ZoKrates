use typed_absy::folder::fold_statement;
use typed_absy::identifier::CoreIdentifier;
use typed_absy::*;
use zokrates_field::field::Field;

pub struct ReturnBinder;

impl ReturnBinder {
    pub fn bind<'ast, T: Field>(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        ReturnBinder {}.fold_program(p)
    }
}

impl<'ast, T: Field> Folder<'ast, T> for ReturnBinder {
    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        match s {
            TypedStatement::Return(exprs) => {
                let ret_identifiers: Vec<Identifier<'ast>> = (0..exprs.len())
                    .map(|i| CoreIdentifier::Internal("RETURN", i).into())
                    .collect();

                let ret_expressions: Vec<TypedExpression<'ast, T>> = exprs
                    .iter()
                    .zip(ret_identifiers.iter())
                    .map(|(e, i)| match e.get_type() {
                        Type::FieldElement => FieldElementExpression::Identifier(i.clone()).into(),
                        Type::Boolean => BooleanExpression::Identifier(i.clone()).into(),
                        Type::Array(array_type) => ArrayExpressionInner::Identifier(i.clone())
                            .annotate(*array_type.ty, array_type.size)
                            .into(),
                        Type::Struct(struct_type) => StructExpressionInner::Identifier(i.clone())
                            .annotate(struct_type)
                            .into(),
                        Type::Uint(bitwidth) => UExpressionInner::Identifier(i.clone()).annotate(bitwidth).into()
                    })
                    .collect();

                exprs
                    .into_iter()
                    .zip(ret_identifiers.iter())
                    .map(|(e, i)| {
                        TypedStatement::Definition(
                            TypedAssignee::Identifier(Variable::with_id_and_type(
                                i.clone(),
                                e.get_type(),
                            )),
                            e,
                        )
                    })
                    .chain(std::iter::once(TypedStatement::Return(ret_expressions)))
                    .collect()
            }
            s => fold_statement(self, s),
        }
    }
}
