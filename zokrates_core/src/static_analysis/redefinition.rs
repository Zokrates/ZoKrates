use crate::typed_absy::folder::*;
use crate::typed_absy::*;
use std::collections::HashMap;
use zokrates_field::Field;

pub struct RedefinitionOptimizer<'ast> {
    identifiers: HashMap<Identifier<'ast>, Identifier<'ast>>,
}

impl<'ast> RedefinitionOptimizer<'ast> {
    fn new() -> Self {
        RedefinitionOptimizer {
            identifiers: HashMap::new(),
        }
    }

    pub fn optimize<T: Field>(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
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

impl<'ast, T: Field> Folder<'ast, T> for RedefinitionOptimizer<'ast> {
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
        self.identifiers.get(&s).cloned().unwrap_or(s)
    }
}
