// Generic walk through an IR AST. Not mutating in place

use super::*;
use crate::common::Variable;
use zokrates_field::Field;

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
        return_count: p.return_count,
    }
}

pub fn fold_statement<T: Field, F: Folder<T>>(
    f: &mut F,
    s: FlatStatement<T>,
) -> Vec<FlatStatement<T>> {
    match s {
        FlatStatement::Condition(left, right, error) => vec![FlatStatement::Condition(
            f.fold_expression(left),
            f.fold_expression(right),
            error,
        )],
        FlatStatement::Definition(v, e) => vec![FlatStatement::Definition(
            f.fold_variable(v),
            f.fold_expression(e),
        )],
        FlatStatement::Directive(d) => vec![FlatStatement::Directive(f.fold_directive(d))],
        FlatStatement::Log(s, e) => vec![FlatStatement::Log(
            s,
            e.into_iter()
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
        FlatExpression::Identifier(id) => FlatExpression::Identifier(f.fold_variable(id)),
        FlatExpression::Add(box left, box right) => {
            FlatExpression::Add(box f.fold_expression(left), box f.fold_expression(right))
        }
        FlatExpression::Sub(box left, box right) => {
            FlatExpression::Sub(box f.fold_expression(left), box f.fold_expression(right))
        }
        FlatExpression::Mult(box left, box right) => {
            FlatExpression::Mult(box f.fold_expression(left), box f.fold_expression(right))
        }
    }
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
