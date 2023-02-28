// Generic walk through an IR AST. Not mutating in place

use super::*;
use crate::common::{
    expressions::{BinaryOrExpression, IdentifierOrExpression},
    flat::Variable,
    Fold, WithSpan,
};
use zokrates_field::Field;

impl<T: Field, F: Folder<T>> Fold<F> for FlatExpression<T> {
    fn fold(self, f: &mut F) -> Self {
        f.fold_expression(self)
    }
}
pub trait Folder<T: Field>: Sized {
    fn fold_program(&mut self, p: FlatProg<T>) -> FlatProg<T> {
        fold_program(self, p)
    }

    fn fold_argument(&mut self, p: Parameter) -> Parameter {
        fold_argument(self, p)
    }

    fn fold_variable(&mut self, v: Variable) -> Variable {
        fold_variable(self, v)
    }

    fn fold_statement(&mut self, s: FlatStatement<T>) -> Vec<FlatStatement<T>> {
        fold_statement(self, s)
    }

    fn fold_expression(&mut self, e: FlatExpression<T>) -> FlatExpression<T> {
        fold_expression(self, e)
    }

    fn fold_binary_expression<Op, L: Fold<Self>, R: Fold<Self>, E>(
        &mut self,
        e: BinaryExpression<Op, L, R, E>,
    ) -> BinaryOrExpression<Op, L, R, E, FlatExpression<T>> {
        fold_binary_expression(self, e)
    }

    fn fold_identifier_expression(
        &mut self,
        e: IdentifierExpression<Variable, FlatExpression<T>>,
    ) -> IdentifierOrExpression<Variable, FlatExpression<T>, FlatExpression<T>> {
        fold_identifier_expression(self, e)
    }

    fn fold_directive(&mut self, d: FlatDirective<T>) -> FlatDirective<T> {
        fold_directive(self, d)
    }
}

pub fn fold_program<T: Field, F: Folder<T>>(f: &mut F, p: FlatProg<T>) -> FlatProg<T> {
    FlatProg {
        arguments: p
            .arguments
            .into_iter()
            .map(|a| f.fold_argument(a))
            .collect(),
        statements: p
            .statements
            .into_iter()
            .flat_map(|s| f.fold_statement(s))
            .collect(),
        ..p
    }
}

pub fn fold_statement<T: Field, F: Folder<T>>(
    f: &mut F,
    s: FlatStatement<T>,
) -> Vec<FlatStatement<T>> {
    match s {
        FlatStatement::Condition(s) => vec![FlatStatement::condition(
            f.fold_expression(s.quad),
            f.fold_expression(s.lin),
            s.error,
        )],
        FlatStatement::Definition(s) => vec![FlatStatement::definition(
            f.fold_variable(s.assignee),
            f.fold_expression(s.rhs),
        )],
        FlatStatement::Directive(d) => vec![FlatStatement::Directive(f.fold_directive(d))],
        FlatStatement::Log(s) => vec![FlatStatement::log(
            s.format_string,
            s.expressions
                .into_iter()
                .map(|(t, e)| (t, e.into_iter().map(|e| f.fold_expression(e)).collect()))
                .collect(),
        )],
    }
}

pub fn fold_expression<T: Field, F: Folder<T>>(
    f: &mut F,
    e: FlatExpression<T>,
) -> FlatExpression<T> {
    match e {
        FlatExpression::Number(n) => FlatExpression::Number(n),
        FlatExpression::Identifier(id) => match f.fold_identifier_expression(id) {
            IdentifierOrExpression::Identifier(e) => FlatExpression::Identifier(e),
            IdentifierOrExpression::Expression(e) => e,
        },
        FlatExpression::Add(e) => match f.fold_binary_expression(e) {
            BinaryOrExpression::Binary(e) => FlatExpression::Add(e),
            BinaryOrExpression::Expression(e) => e,
        },
        FlatExpression::Sub(e) => match f.fold_binary_expression(e) {
            BinaryOrExpression::Binary(e) => FlatExpression::Sub(e),
            BinaryOrExpression::Expression(e) => e,
        },
        FlatExpression::Mult(e) => match f.fold_binary_expression(e) {
            BinaryOrExpression::Binary(e) => FlatExpression::Mult(e),
            BinaryOrExpression::Expression(e) => e,
        },
    }
}

fn fold_identifier_expression<T: Field, F: Folder<T>>(
    f: &mut F,
    e: IdentifierExpression<Variable, FlatExpression<T>>,
) -> IdentifierOrExpression<Variable, FlatExpression<T>, FlatExpression<T>> {
    let id = f.fold_variable(e.id);

    IdentifierOrExpression::Identifier(IdentifierExpression { id, ..e })
}

fn fold_binary_expression<T: Field, F: Folder<T>, Op, L: Fold<F>, R: Fold<F>, E>(
    f: &mut F,
    e: BinaryExpression<Op, L, R, E>,
) -> BinaryOrExpression<Op, L, R, E, FlatExpression<T>> {
    let left = e.left.fold(f);
    let right = e.right.fold(f);

    BinaryOrExpression::Binary(BinaryExpression::new(left, right).span(e.span))
}

pub fn fold_directive<T: Field, F: Folder<T>>(f: &mut F, ds: FlatDirective<T>) -> FlatDirective<T> {
    FlatDirective {
        inputs: ds
            .inputs
            .into_iter()
            .map(|e| f.fold_expression(e))
            .collect(),
        outputs: ds.outputs.into_iter().map(|o| f.fold_variable(o)).collect(),
        ..ds
    }
}

pub fn fold_argument<T: Field, F: Folder<T>>(f: &mut F, a: Parameter) -> Parameter {
    Parameter {
        id: f.fold_variable(a.id),
        private: a.private,
    }
}

pub fn fold_variable<T: Field, F: Folder<T>>(_f: &mut F, v: Variable) -> Variable {
    v
}
