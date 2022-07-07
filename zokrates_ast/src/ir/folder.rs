// Generic walk through an IR AST. Not mutating in place

use super::*;
use crate::common::Variable;
use zokrates_field::Field;

pub trait Folder<T: Field>: Sized {
    fn fold_program(&mut self, p: Prog<T>) -> Prog<T> {
        fold_program(self, p)
    }

    fn fold_argument(&mut self, p: Parameter) -> Parameter {
        fold_argument(self, p)
    }

    fn fold_variable(&mut self, v: Variable) -> Variable {
        fold_variable(self, v)
    }

    fn fold_statement(&mut self, s: Statement<T>) -> Vec<Statement<T>> {
        fold_statement(self, s)
    }

    fn fold_linear_combination(&mut self, e: LinComb<T>) -> LinComb<T> {
        fold_linear_combination(self, e)
    }

    fn fold_quadratic_combination(&mut self, es: QuadComb<T>) -> QuadComb<T> {
        fold_quadratic_combination(self, es)
    }

    fn fold_directive(&mut self, d: Directive<T>) -> Directive<T> {
        fold_directive(self, d)
    }
}

pub fn fold_program<T: Field, F: Folder<T>>(f: &mut F, p: Prog<T>) -> Prog<T> {
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
    }
}

pub fn fold_statement<T: Field, F: Folder<T>>(f: &mut F, s: Statement<T>) -> Vec<Statement<T>> {
    match s {
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

pub fn fold_linear_combination<T: Field, F: Folder<T>>(f: &mut F, e: LinComb<T>) -> LinComb<T> {
    LinComb(
        e.0.into_iter()
            .map(|(variable, coefficient)| (f.fold_variable(variable), coefficient))
            .collect(),
    )
}

pub fn fold_quadratic_combination<T: Field, F: Folder<T>>(
    f: &mut F,
    e: QuadComb<T>,
) -> QuadComb<T> {
    QuadComb {
        left: f.fold_linear_combination(e.left),
        right: f.fold_linear_combination(e.right),
    }
}

pub fn fold_directive<T: Field, F: Folder<T>>(f: &mut F, ds: Directive<T>) -> Directive<T> {
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

pub fn fold_argument<T: Field, F: Folder<T>>(f: &mut F, a: Parameter) -> Parameter {
    Parameter {
        id: f.fold_variable(a.id),
        private: a.private,
    }
}

pub fn fold_variable<T: Field, F: Folder<T>>(_f: &mut F, v: Variable) -> Variable {
    v
}
