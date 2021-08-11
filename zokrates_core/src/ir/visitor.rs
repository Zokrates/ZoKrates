// Generic walk through an IR AST. Not mutating in place

use crate::flat_absy::flat_variable::FlatVariable;
use crate::ir::*;
use zokrates_field::Field;

pub trait Visitor<T: Field>: Sized {
    fn visit_module(&mut self, p: &Prog<T>) {
        visit_module(self, p)
    }

    fn visit_function(&mut self, f: &Function<T>) {
        visit_function(self, f)
    }

    fn visit_argument(&mut self, p: &FlatVariable) {
        visit_argument(self, p)
    }

    fn visit_variable(&mut self, v: &FlatVariable) {
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

    fn visit_directive(&mut self, d: &Directive<T>) {
        visit_directive(self, d)
    }

    fn visit_runtime_error(&mut self, e: &RuntimeError) {
        visit_runtime_error(self, e)
    }
}

pub fn visit_module<T: Field, F: Visitor<T>>(f: &mut F, p: &Prog<T>) {
    f.visit_function(&p.main)
}

pub fn visit_statement<T: Field, F: Visitor<T>>(f: &mut F, s: &Statement<T>) {
    match s {
        Statement::Constraint(quad, lin, error) => {
            f.visit_quadratic_combination(quad);
            f.visit_linear_combination(lin);
            if let Some(error) = error.as_ref() {
                f.visit_runtime_error(error);
            }
        }
        Statement::Directive(dir) => f.visit_directive(dir),
    }
}

pub fn visit_linear_combination<T: Field, F: Visitor<T>>(f: &mut F, e: &LinComb<T>) {
    for expr in e.0.iter() {
        f.visit_variable(&expr.0);
        f.visit_value(&expr.1);
    }
}

pub fn visit_quadratic_combination<T: Field, F: Visitor<T>>(f: &mut F, e: &QuadComb<T>) {
    f.visit_linear_combination(&e.left);
    f.visit_linear_combination(&e.right);
}

pub fn visit_directive<T: Field, F: Visitor<T>>(f: &mut F, ds: &Directive<T>) {
    for expr in ds.inputs.iter() {
        f.visit_quadratic_combination(expr);
    }
    for expr in ds.outputs.iter() {
        f.visit_variable(expr);
    }
}

pub fn visit_function<T: Field, F: Visitor<T>>(f: &mut F, fun: &Function<T>) {
    for expr in fun.arguments.iter() {
        f.visit_argument(expr);
    }
    for expr in fun.statements.iter() {
        f.visit_statement(expr);
    }
    for expr in fun.returns.iter() {
        f.visit_variable(expr);
    }
}

pub fn visit_argument<T: Field, F: Visitor<T>>(f: &mut F, a: &FlatVariable) {
    f.visit_variable(a)
}

pub fn visit_variable<T: Field, F: Visitor<T>>(_f: &mut F, _v: &FlatVariable) {}

pub fn visit_value<T: Field, F: Visitor<T>>(_f: &mut F, _v: &T) {}

fn visit_runtime_error<T: Field, F: Visitor<T>>(_f: &mut F, _: &RuntimeError) {}
