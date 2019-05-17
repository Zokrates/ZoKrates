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

    pub fn clean<T: Field>(p: TypedModule<T>) -> TypedModule<T> {
        DeadCode::new().fold_module(p)
    }
}

impl<T: Field> Folder<T> for DeadCode {
    fn fold_module(&mut self, p: TypedModule<T>) -> TypedModule<T> {
        let p = fold_module(self, p);
        // only keep functions which are being called, or `main`

        unimplemented!()

        // TypedModule {
        //     functions: p
        //         .functions
        //         .into_iter()
        //         .filter(|(key, f)| key.id == "main" || self.called.contains(&f.slug()))
        //         .collect(),
        //     ..p
        // }
    }

    // add extra statements before the modified statement
    fn fold_statement(&mut self, s: TypedStatement<T>) -> Vec<TypedStatement<T>> {
        match s {
            TypedStatement::MultipleDefinition(variables, elist) => match elist {
                TypedExpressionList::FunctionCall(key, exps, types) => {
                    let exps: Vec<_> = exps.into_iter().map(|e| self.fold_expression(e)).collect();

                    let signature = Signature::new()
                        .inputs(exps.iter().map(|e| e.get_type()).collect())
                        .outputs(types.clone());

                    self.called
                        .insert(format!("{}_{}", key.id, signature.to_slug()));
                    vec![TypedStatement::MultipleDefinition(
                        variables,
                        TypedExpressionList::FunctionCall(key, exps, types),
                    )]
                }
            },
            s => fold_statement(self, s),
        }
    }

    fn fold_field_expression(&mut self, e: FieldElementExpression<T>) -> FieldElementExpression<T> {
        match e {
            FieldElementExpression::FunctionCall(id, exps) => {
                let exps: Vec<_> = exps.into_iter().map(|e| self.fold_expression(e)).collect();

                let signature = Signature::new()
                    .inputs(exps.iter().map(|e| e.get_type()).collect())
                    .outputs(vec![Type::FieldElement]);

                self.called
                    .insert(format!("{}_{}", id.id, signature.to_slug()));
                FieldElementExpression::FunctionCall(id, exps)
            }
            e => fold_field_expression(self, e),
        }
    }

    fn fold_field_array_expression(
        &mut self,
        e: FieldElementArrayExpression<T>,
    ) -> FieldElementArrayExpression<T> {
        match e {
            FieldElementArrayExpression::FunctionCall(size, key, exps) => {
                let exps: Vec<_> = exps.into_iter().map(|e| self.fold_expression(e)).collect();

                let signature = Signature::new()
                    .inputs(exps.iter().map(|e| e.get_type()).collect())
                    .outputs(vec![Type::FieldElementArray(size)]);

                self.called
                    .insert(format!("{}_{}", key.id, signature.to_slug()));
                FieldElementArrayExpression::FunctionCall(size, key, exps)
            }
            e => fold_field_array_expression(self, e),
        }
    }
}
