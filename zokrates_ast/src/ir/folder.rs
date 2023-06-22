// Generic walk through an IR AST. Not mutating in place

use super::*;
use crate::common::{flat::Variable, WithSpan};
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

    fn fold_statement_cases(&mut self, s: Statement<'ast, T>) -> Vec<Statement<'ast, T>> {
        fold_statement_cases(self, s)
    }

    fn fold_constraint_statement(&mut self, s: ConstraintStatement<T>) -> Vec<Statement<'ast, T>> {
        fold_constraint_statement(self, s)
    }

    fn fold_directive_statement(
        &mut self,
        s: DirectiveStatement<'ast, T>,
    ) -> Vec<Statement<'ast, T>> {
        fold_directive_statement(self, s)
    }

    fn fold_log_statement(&mut self, s: LogStatement<T>) -> Vec<Statement<'ast, T>> {
        fold_log_statement(self, s)
    }

    fn fold_block_statement(&mut self, s: BlockStatement<'ast, T>) -> Vec<Statement<'ast, T>> {
        fold_block_statement(self, s)
    }

    fn fold_linear_combination(&mut self, e: LinComb<T>) -> LinComb<T> {
        fold_linear_combination(self, e)
    }

    fn fold_quadratic_combination(&mut self, es: QuadComb<T>) -> QuadComb<T> {
        fold_quadratic_combination(self, es)
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
        ..p
    }
}

pub fn fold_constraint_statement<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: ConstraintStatement<T>,
) -> Vec<Statement<'ast, T>> {
    vec![Statement::constraint(
        f.fold_quadratic_combination(s.quad),
        f.fold_linear_combination(s.lin),
        s.error,
    )]
}

pub fn fold_log_statement<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: LogStatement<T>,
) -> Vec<Statement<'ast, T>> {
    vec![Statement::log(
        s.format_string,
        s.expressions
            .into_iter()
            .map(|(t, e)| {
                (
                    t,
                    e.into_iter()
                        .map(|e| f.fold_linear_combination(e))
                        .collect(),
                )
            })
            .collect(),
    )]
}

pub fn fold_block_statement<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: BlockStatement<'ast, T>,
) -> Vec<Statement<'ast, T>> {
    vec![Statement::block(
        s.inner
            .into_iter()
            .flat_map(|s| f.fold_statement(s))
            .collect(),
    )]
}

fn fold_statement<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: Statement<'ast, T>,
) -> Vec<Statement<'ast, T>> {
    let span = s.get_span();
    f.fold_statement_cases(s)
        .into_iter()
        .map(|s| s.span(span))
        .collect()
}

pub fn fold_statement_cases<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: Statement<'ast, T>,
) -> Vec<Statement<'ast, T>> {
    match s {
        Statement::Constraint(s) => f.fold_constraint_statement(s),
        Statement::Directive(s) => f.fold_directive_statement(s),
        Statement::Log(s) => f.fold_log_statement(s),
        Statement::Block(s) => f.fold_block_statement(s),
    }
}

pub fn fold_linear_combination<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: LinComb<T>,
) -> LinComb<T> {
    LinComb::new(
        e.value
            .into_iter()
            .map(|(variable, coefficient)| (f.fold_variable(variable), coefficient))
            .collect(),
    )
    .span(e.span)
}

pub fn fold_quadratic_combination<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: QuadComb<T>,
) -> QuadComb<T> {
    QuadComb::new(
        f.fold_linear_combination(e.left),
        f.fold_linear_combination(e.right),
    )
    .span(e.span)
}

pub fn fold_directive_statement<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    ds: DirectiveStatement<'ast, T>,
) -> Vec<Statement<'ast, T>> {
    vec![Statement::Directive(DirectiveStatement {
        inputs: ds
            .inputs
            .into_iter()
            .map(|e| f.fold_quadratic_combination(e))
            .collect(),
        outputs: ds.outputs.into_iter().map(|o| f.fold_variable(o)).collect(),
        ..ds
    })]
}

pub fn fold_argument<'ast, T: Field, F: Folder<'ast, T>>(f: &mut F, a: Parameter) -> Parameter {
    Parameter {
        id: f.fold_variable(a.id),
        ..a
    }
}

pub fn fold_variable<'ast, T: Field, F: Folder<'ast, T>>(_f: &mut F, v: Variable) -> Variable {
    v
}
