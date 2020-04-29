//! Module containing constant propagation for the typed AST
//!
//! On top of the usual behavior of removing statements which assign a constant to a variable (as the variable can simply be
//! substituted for the constant whenever used), we provide a `verbose` mode which does not remove such statements. This is done
//! as for partial passes which do not visit the whole program, the variables being defined may be be used in parts of the program
//! that are not visited. Keeping the statements is semantically equivalent and enables rebuilding the set of constants at the
//! next pass.
//!
//! @file propagation.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use crate::typed_absy::folder::*;
use crate::typed_absy::*;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::marker::PhantomData;
use typed_absy::types::{StructMember, Type};
use zokrates_field::field::Field;

pub struct RedefinitionOptimizer<'ast, T: Field> {
    identifiers: HashMap<Identifier<'ast>, Identifier<'ast>>,
    phantom: PhantomData<T>,
}

impl<'ast, T: Field> RedefinitionOptimizer<'ast, T> {
    fn new() -> Self {
        RedefinitionOptimizer {
            identifiers: HashMap::new(),
            phantom: PhantomData,
        }
    }

    pub fn optimize(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        RedefinitionOptimizer::new().fold_program(p)
    }
}

fn try_id<'ast, T: Field>(e: &TypedExpression<'ast, T>) -> Option<Identifier<'ast>> {
    match e {
        TypedExpression::FieldElement(FieldElementExpression::Identifier(id)) => Some(id.clone()),
        TypedExpression::Boolean(BooleanExpression::Identifier(id)) => Some(id.clone()),
        TypedExpression::Array(a) => match a.as_inner() {
            ArrayExpressionInner::Identifier(id) => Some(id.clone()),
            _ => None,
        },
        TypedExpression::Struct(a) => match a.as_inner() {
            StructExpressionInner::Identifier(id) => Some(id.clone()),
            _ => None,
        },
        TypedExpression::Uint(a) => match a.as_inner() {
            UExpressionInner::Identifier(id) => Some(id.clone()),
            _ => None,
        },
        _ => None,
    }
}

impl<'ast, T: Field> Folder<'ast, T> for RedefinitionOptimizer<'ast, T> {
    fn fold_function(&mut self, f: TypedFunction<'ast, T>) -> TypedFunction<'ast, T> {
        self.identifiers = HashMap::new();
        fold_function(self, f)
    }

    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        match s {
            TypedStatement::Definition(TypedAssignee::Identifier(var), expr) => {
                let expr = self.fold_expression(expr);

                match try_id(&expr) {
                    Some(id) => {
                        let target = self.identifiers.get(&id).unwrap_or(&id).clone();

                        self.identifiers.insert(var.id, target);
                        vec![]
                    }
                    None => vec![TypedStatement::Definition(
                        TypedAssignee::Identifier(var),
                        expr,
                    )],
                }
            }
            s => fold_statement(self, s),
        }
    }

    fn fold_name(&mut self, s: Identifier<'ast>) -> Identifier<'ast> {
        self.identifiers.get(&s).map(|r| r.clone()).unwrap_or(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;
}
