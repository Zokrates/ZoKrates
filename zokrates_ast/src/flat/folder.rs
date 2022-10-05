// Generic walk through an IR AST. Not mutating in place

use super::*;
use crate::common::Variable;
use zokrates_field::Field;

pub trait Folder<'ast, T: Field>: Sized {
    fn fold_program(&mut self, p: FlatProg<'ast, T>) -> FlatProg<'ast, T> {
        fold_program(self, p)
    }

    fn fold_argument(&mut self, p: Parameter) -> Parameter {
        fold_argument(self, p)
    }

    fn fold_variable(&mut self, v: Variable) -> Variable {
        fold_variable(self, v)
    }

    fn fold_statement(&mut self, s: FlatStatement<'ast, T>) -> Vec<FlatStatement<'ast, T>> {
        fold_statement(self, s)
    }

    fn fold_expression(&mut self, e: FlatExpression<T>) -> FlatExpression<T> {
        fold_expression(self, e)
    }

    fn fold_directive(&mut self, d: FlatDirective<'ast, T>) -> FlatDirective<'ast, T> {
        fold_directive(self, d)
    }
}

pub fn fold_program<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    p: FlatProg<'ast, T>,
) -> FlatProg<'ast, T> {
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

pub fn fold_statement<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: FlatStatement<'ast, T>,
) -> Vec<FlatStatement<'ast, T>> {
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

pub fn fold_expression<'ast, T: Field, F: Folder<'ast, T>>(
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

pub fn fold_directive<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    ds: FlatDirective<'ast, T>,
) -> FlatDirective<'ast, T> {
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

pub fn fold_argument<'ast, T: Field, F: Folder<'ast, T>>(f: &mut F, a: Parameter) -> Parameter {
    Parameter {
        id: f.fold_variable(a.id),
        private: a.private,
    }
}

pub fn fold_variable<'ast, T: Field, F: Folder<'ast, T>>(_f: &mut F, v: Variable) -> Variable {
    v
}
