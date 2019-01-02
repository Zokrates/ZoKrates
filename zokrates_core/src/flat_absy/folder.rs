// Generic walk through a flat AST. Not mutating in place

use flat_absy::flat_variable::FlatVariable;
use flat_absy::*;
use zokrates_field::field::Field;

pub trait Folder<T: Field>: Sized {
    fn fold_program(&mut self, p: FlatProg<T>) -> FlatProg<T> {
        fold_program(self, p)
    }

    fn fold_function(&mut self, f: FlatFunction<T>) -> FlatFunction<T> {
        fold_function(self, f)
    }

    fn fold_parameter(&mut self, p: FlatParameter) -> FlatParameter {
        fold_parameter(self, p)
    }

    fn fold_variable(&mut self, v: FlatVariable) -> FlatVariable {
        v
    }

    fn fold_statement(&mut self, s: FlatStatement<T>) -> Vec<FlatStatement<T>> {
        fold_statement(self, s)
    }

    fn fold_expression(&mut self, e: FlatExpression<T>) -> FlatExpression<T> {
        fold_expression(self, e)
    }

    fn fold_expression_list(&mut self, es: FlatExpressionList<T>) -> FlatExpressionList<T> {
        fold_expression_list(self, es)
    }

    fn fold_directive_statement(&mut self, ds: DirectiveStatement<T>) -> DirectiveStatement<T> {
        fold_directive_statement(self, ds)
    }
}

pub fn fold_program<T: Field, F: Folder<T>>(f: &mut F, p: FlatProg<T>) -> FlatProg<T> {
    FlatProg {
        functions: p
            .functions
            .into_iter()
            .map(|fun| f.fold_function(fun))
            .collect(),
        ..p
    }
}

pub fn fold_statement<T: Field, F: Folder<T>>(
    f: &mut F,
    s: FlatStatement<T>,
) -> Vec<FlatStatement<T>> {
    let res = match s {
        FlatStatement::Return(expression_list) => {
            FlatStatement::Return(f.fold_expression_list(expression_list))
        }
        FlatStatement::Definition(v, e) => {
            FlatStatement::Definition(f.fold_variable(v), f.fold_expression(e))
        }
        FlatStatement::Condition(left, right) => {
            FlatStatement::Condition(f.fold_expression(left), f.fold_expression(right))
        }
        FlatStatement::Directive(ds) => FlatStatement::Directive(f.fold_directive_statement(ds)),
    };
    vec![res]
}

pub fn fold_expression<T: Field, F: Folder<T>>(
    f: &mut F,
    e: FlatExpression<T>,
) -> FlatExpression<T> {
    match e {
        FlatExpression::Number(n) => FlatExpression::Number(n),
        FlatExpression::Identifier(id) => FlatExpression::Identifier(f.fold_variable(id)),
        FlatExpression::Add(box e1, box e2) => {
            let e1 = f.fold_expression(e1);
            let e2 = f.fold_expression(e2);
            FlatExpression::Add(box e1, box e2)
        }
        FlatExpression::Sub(box e1, box e2) => {
            let e1 = f.fold_expression(e1);
            let e2 = f.fold_expression(e2);
            FlatExpression::Sub(box e1, box e2)
        }
        FlatExpression::Mult(box e1, box e2) => {
            let e1 = f.fold_expression(e1);
            let e2 = f.fold_expression(e2);
            FlatExpression::Mult(box e1, box e2)
        }
    }
}

pub fn fold_expression_list<T: Field, F: Folder<T>>(
    f: &mut F,
    e: FlatExpressionList<T>,
) -> FlatExpressionList<T> {
    FlatExpressionList {
        expressions: e
            .expressions
            .into_iter()
            .map(|e| f.fold_expression(e))
            .collect(),
    }
}

pub fn fold_directive_statement<T: Field, F: Folder<T>>(
    f: &mut F,
    ds: DirectiveStatement<T>,
) -> DirectiveStatement<T> {
    DirectiveStatement {
        inputs: ds
            .inputs
            .into_iter()
            .map(|e| f.fold_expression(e))
            .collect(),
        outputs: ds.outputs.into_iter().map(|o| f.fold_variable(o)).collect(),
        ..ds
    }
}

pub fn fold_function<T: Field, F: Folder<T>>(f: &mut F, fun: FlatFunction<T>) -> FlatFunction<T> {
    FlatFunction {
        arguments: fun
            .arguments
            .into_iter()
            .map(|a| f.fold_parameter(a))
            .collect(),
        statements: fun
            .statements
            .into_iter()
            .flat_map(|s| f.fold_statement(s))
            .collect(),
        ..fun
    }
}
pub fn fold_parameter<T: Field, F: Folder<T>>(f: &mut F, p: FlatParameter) -> FlatParameter {
    FlatParameter {
        id: f.fold_variable(p.id),
        ..p
    }
}
