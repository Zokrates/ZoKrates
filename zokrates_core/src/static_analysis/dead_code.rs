use crate::typed_absy::folder::*;
use crate::typed_absy::Folder;
use crate::typed_absy::*;
use crate::types::{Signature, Type};
use std::collections::HashSet;
use zokrates_field::field::Field;

pub struct DeadCode {
    called: HashSet<String>,
}

impl DeadCode {
    fn new() -> Self {
        DeadCode {
            called: HashSet::new(),
        }
    }

    pub fn clean<T: Field>(p: TypedProg<T>) -> TypedProg<T> {
        DeadCode::new().fold_program(p)
    }
}

impl<'ast, T: Field> Folder<'ast, T> for DeadCode {
    fn fold_program(&mut self, p: TypedProg<'ast, T>) -> TypedProg<'ast, T> {
        let p = fold_program(self, p);
        // only keep functions which are being called, or `main`

        TypedProg {
            functions: p
                .functions
                .into_iter()
                .filter(|f| f.id == "main" || self.called.contains(&f.to_slug()))
                .collect(),
            ..p
        }
    }

    // add extra statements before the modified statement
    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        match s {
            TypedStatement::MultipleDefinition(variables, elist) => match elist {
                TypedExpressionList::FunctionCall(id, exps, types) => {
                    let exps: Vec<_> = exps.into_iter().map(|e| self.fold_expression(e)).collect();

                    let signature = Signature::new()
                        .inputs(exps.iter().map(|e| e.get_type()).collect())
                        .outputs(types.clone());

                    self.called
                        .insert(format!("{}_{}", id, signature.to_slug()));
                    vec![TypedStatement::MultipleDefinition(
                        variables,
                        TypedExpressionList::FunctionCall(id, exps, types),
                    )]
                }
            },
            s => fold_statement(self, s),
        }
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        match e {
            FieldElementExpression::FunctionCall(id, exps) => {
                let exps: Vec<_> = exps.into_iter().map(|e| self.fold_expression(e)).collect();

                let signature = Signature::new()
                    .inputs(exps.iter().map(|e| e.get_type()).collect())
                    .outputs(vec![Type::FieldElement]);

                self.called
                    .insert(format!("{}_{}", id, signature.to_slug()));
                FieldElementExpression::FunctionCall(id, exps)
            }
            e => fold_field_expression(self, e),
        }
    }

    fn fold_field_array_expression(
        &mut self,
        e: FieldElementArrayExpression<'ast, T>,
    ) -> FieldElementArrayExpression<'ast, T> {
        match e {
            FieldElementArrayExpression::FunctionCall(size, id, exps) => {
                let exps: Vec<_> = exps.into_iter().map(|e| self.fold_expression(e)).collect();

                let signature = Signature::new()
                    .inputs(exps.iter().map(|e| e.get_type()).collect())
                    .outputs(vec![Type::FieldElementArray(size)]);

                self.called
                    .insert(format!("{}_{}", id, signature.to_slug()));
                FieldElementArrayExpression::FunctionCall(size, id, exps)
            }
            e => fold_field_array_expression(self, e),
        }
    }
}
