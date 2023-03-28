// Generic walk through an IR AST. Not mutating in place

use super::*;
use crate::common::Variable;
use zokrates_field::Field;

pub trait Folder<'ast, T: Field>: Sized {
    fn fold_program(&mut self, p: Prog<'ast, T>) -> Prog<'ast, T> {
        fold_program(self, p)
    }

    fn fold_argument(&mut self, p: Parameter) -> Parameter {
        fold_argument(self, p)
    }

    fn fold_variable(&mut self, v: Variable) -> Variable {
        fold_variable(self, v)
    }

    fn fold_statement(&mut self, s: Statement<'ast, T>) -> Vec<Statement<'ast, T>> {
        fold_statement(self, s)
    }

    fn fold_linear_combination(&mut self, e: LinComb<T>) -> LinComb<T> {
        fold_linear_combination(self, e)
    }

    fn fold_quadratic_combination(&mut self, es: QuadComb<T>) -> QuadComb<T> {
        fold_quadratic_combination(self, es)
    }

    fn fold_directive(&mut self, d: Directive<'ast, T>) -> Directive<'ast, T> {
        fold_directive(self, d)
    }
}

pub fn fold_program<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    p: Prog<'ast, T>,
) -> Prog<'ast, T> {
    Prog {
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
        solvers: p.solvers,
    }
}

pub fn fold_statement<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: Statement<'ast, T>,
) -> Vec<Statement<'ast, T>> {
    match s {
        Statement::Block(statements) => vec![Statement::Block(
            statements
                .into_iter()
                .flat_map(|s| f.fold_statement(s))
                .collect(),
        )],
        Statement::Constraint(quad, lin, message) => vec![Statement::Constraint(
            f.fold_quadratic_combination(quad),
            f.fold_linear_combination(lin),
            message,
        )],
        Statement::Directive(dir) => vec![Statement::Directive(f.fold_directive(dir))],
        Statement::Log(l, e) => vec![Statement::Log(
            l,
            e.into_iter()
                .map(|(t, e)| {
                    (
                        t,
                        e.into_iter()
                            .map(|e| f.fold_linear_combination(e))
                            .collect(),
                    )
                })
                .collect(),
        )],
    }
}

pub fn fold_linear_combination<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: LinComb<T>,
) -> LinComb<T> {
    LinComb(
        e.0.into_iter()
            .map(|(variable, coefficient)| (f.fold_variable(variable), coefficient))
            .collect(),
    )
}

pub fn fold_quadratic_combination<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: QuadComb<T>,
) -> QuadComb<T> {
    QuadComb {
        left: f.fold_linear_combination(e.left),
        right: f.fold_linear_combination(e.right),
    }
}

pub fn fold_directive<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    ds: Directive<'ast, T>,
) -> Directive<'ast, T> {
    Directive {
        inputs: ds
            .inputs
            .into_iter()
            .map(|e| f.fold_quadratic_combination(e))
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
