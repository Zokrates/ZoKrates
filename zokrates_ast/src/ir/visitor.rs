// Generic walk through an IR AST. Not mutating in place

use super::*;
use crate::common::flat::Variable;
use zokrates_field::Field;

pub trait Visitor<T: Field>: Sized {
    fn visit_module(&mut self, p: &Prog<T>) {
        visit_module(self, p)
    }

    fn visit_argument(&mut self, p: &Parameter) {
        visit_argument(self, p)
    }

    fn visit_variable(&mut self, v: &Variable) {
        visit_variable(self, v)
    }

    fn visit_value(&mut self, v: &T) {
        visit_value(self, v)
    }

    fn visit_statement(&mut self, s: &Statement<T>) {
        visit_statement(self, s)
    }

    fn visit_linear_combination(&mut self, e: &LinComb<T>) {
        visit_linear_combination(self, e)
    }

    fn visit_quadratic_combination(&mut self, es: &QuadComb<T>) {
        visit_quadratic_combination(self, es)
    }

    fn visit_directive_statement(&mut self, d: &DirectiveStatement<T>) {
        visit_directive_statement(self, d)
    }

    fn visit_runtime_error(&mut self, e: &RuntimeError) {
        visit_runtime_error(self, e)
    }
}

pub fn visit_module<T: Field, F: Visitor<T>>(f: &mut F, p: &Prog<T>) {
    for expr in p.arguments.iter() {
        f.visit_argument(expr);
    }
    for expr in p.statements.iter() {
        f.visit_statement(expr);
    }
}

pub fn visit_statement<T: Field, F: Visitor<T>>(f: &mut F, s: &Statement<T>) {
    match s {
        Statement::Block(s) => {
            for s in &s.inner {
                f.visit_statement(s);
            }
        }
        Statement::Constraint(s) => {
            f.visit_quadratic_combination(&s.quad);
            f.visit_linear_combination(&s.lin);
            if let Some(error) = s.error.as_ref() {
                f.visit_runtime_error(error);
            }
        }
        Statement::Directive(dir) => f.visit_directive_statement(dir),
        Statement::Log(s) => {
            for (_, e) in &s.expressions {
                for e in e {
                    f.visit_linear_combination(e);
                }
            }
        }
    }
}

pub fn visit_linear_combination<T: Field, F: Visitor<T>>(f: &mut F, e: &LinComb<T>) {
    for expr in e.value.iter() {
        f.visit_variable(&expr.0);
        f.visit_value(&expr.1);
    }
}

pub fn visit_quadratic_combination<T: Field, F: Visitor<T>>(f: &mut F, e: &QuadComb<T>) {
    f.visit_linear_combination(&e.left);
    f.visit_linear_combination(&e.right);
}

pub fn visit_directive_statement<T: Field, F: Visitor<T>>(f: &mut F, ds: &DirectiveStatement<T>) {
    for expr in ds.inputs.iter() {
        f.visit_quadratic_combination(expr);
    }
    for expr in ds.outputs.iter() {
        f.visit_variable(expr);
    }
}

pub fn visit_argument<T: Field, F: Visitor<T>>(f: &mut F, a: &Parameter) {
    f.visit_variable(&a.id)
}

pub fn visit_variable<T: Field, F: Visitor<T>>(_f: &mut F, _v: &Variable) {}

pub fn visit_value<T: Field, F: Visitor<T>>(_f: &mut F, _v: &T) {}

fn visit_runtime_error<T: Field, F: Visitor<T>>(_f: &mut F, _: &RuntimeError) {}
