// Generic walk through a typed AST. Not mutating in place

use typed_absy::*;
use zokrates_field::field::Field;

pub trait Folder<T: Field>: Sized {
    fn fold_program(&mut self, p: TypedProg<T>) -> TypedProg<T> {
        fold_program(self, p)
    }

    fn fold_function(&mut self, f: TypedFunction<T>) -> TypedFunction<T> {
        fold_function(self, f)
    }

    fn fold_parameter(&mut self, p: Parameter) -> Parameter {
        Parameter {
            id: self.fold_variable(p.id),
            ..p
        }
    }

    fn fold_name(&mut self, n: String) -> String {
        n
    }

    fn fold_variable(&mut self, v: Variable) -> Variable {
        Variable {
            id: self.fold_name(v.id),
            ..v
        }
    }

    fn fold_assignee(&mut self, a: TypedAssignee<T>) -> TypedAssignee<T> {
        match a {
            TypedAssignee::Identifier(v) => TypedAssignee::Identifier(self.fold_variable(v)),
            TypedAssignee::ArrayElement(box a, box index) => TypedAssignee::ArrayElement(
                box self.fold_assignee(a),
                box self.fold_field_expression(index),
            ),
        }
    }

    fn fold_statement(&mut self, s: TypedStatement<T>) -> Vec<TypedStatement<T>> {
        fold_statement(self, s)
    }

    fn fold_expression(&mut self, e: TypedExpression<T>) -> TypedExpression<T> {
        match e {
            TypedExpression::FieldElement(e) => self.fold_field_expression(e).into(),
            TypedExpression::Boolean(e) => self.fold_boolean_expression(e).into(),
            TypedExpression::FieldElementArray(e) => self.fold_field_array_expression(e).into(),
        }
    }

    fn fold_expression_list(&mut self, es: TypedExpressionList<T>) -> TypedExpressionList<T> {
        match es {
            TypedExpressionList::FunctionCall(id, arguments, types) => {
                TypedExpressionList::FunctionCall(
                    id,
                    arguments
                        .into_iter()
                        .map(|a| self.fold_expression(a))
                        .collect(),
                    types,
                )
            }
        }
    }

    fn fold_field_expression(&mut self, e: FieldElementExpression<T>) -> FieldElementExpression<T> {
        fold_field_expression(self, e)
    }
    fn fold_boolean_expression(&mut self, e: BooleanExpression<T>) -> BooleanExpression<T> {
        fold_boolean_expression(self, e)
    }
    fn fold_field_array_expression(
        &mut self,
        e: FieldElementArrayExpression<T>,
    ) -> FieldElementArrayExpression<T> {
        fold_field_array_expression(self, e)
    }
}

pub fn fold_program<T: Field, F: Folder<T>>(f: &mut F, p: TypedProg<T>) -> TypedProg<T> {
    TypedProg {
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
    s: TypedStatement<T>,
) -> Vec<TypedStatement<T>> {
    let res = match s {
        TypedStatement::Return(expressions) => TypedStatement::Return(
            expressions
                .into_iter()
                .map(|e| f.fold_expression(e))
                .collect(),
        ),
        TypedStatement::Definition(a, e) => {
            TypedStatement::Definition(f.fold_assignee(a), f.fold_expression(e))
        }
        TypedStatement::Declaration(v) => TypedStatement::Declaration(f.fold_variable(v)),
        TypedStatement::Condition(left, right) => {
            TypedStatement::Condition(f.fold_expression(left), f.fold_expression(right))
        }
        TypedStatement::For(v, from, to, statements) => TypedStatement::For(
            f.fold_variable(v),
            from,
            to,
            statements
                .into_iter()
                .flat_map(|s| f.fold_statement(s))
                .collect(),
        ),
        TypedStatement::MultipleDefinition(variables, elist) => TypedStatement::MultipleDefinition(
            variables.into_iter().map(|v| f.fold_variable(v)).collect(),
            f.fold_expression_list(elist),
        ),
    };
    vec![res]
}

pub fn fold_field_array_expression<T: Field, F: Folder<T>>(
    f: &mut F,
    e: FieldElementArrayExpression<T>,
) -> FieldElementArrayExpression<T> {
    match e {
        FieldElementArrayExpression::Identifier(size, id) => {
            FieldElementArrayExpression::Identifier(size, f.fold_name(id))
        }
        FieldElementArrayExpression::Value(size, exprs) => FieldElementArrayExpression::Value(
            size,
            exprs
                .into_iter()
                .map(|e| f.fold_field_expression(e))
                .collect(),
        ),
        FieldElementArrayExpression::FunctionCall(size, id, exps) => {
            let exps = exps.into_iter().map(|e| f.fold_expression(e)).collect();
            FieldElementArrayExpression::FunctionCall(size, id, exps)
        }
        FieldElementArrayExpression::IfElse(box condition, box consequence, box alternative) => {
            FieldElementArrayExpression::IfElse(
                box f.fold_boolean_expression(condition),
                box f.fold_field_array_expression(consequence),
                box f.fold_field_array_expression(alternative),
            )
        }
    }
}

pub fn fold_field_expression<T: Field, F: Folder<T>>(
    f: &mut F,
    e: FieldElementExpression<T>,
) -> FieldElementExpression<T> {
    match e {
        FieldElementExpression::Number(n) => FieldElementExpression::Number(n),
        FieldElementExpression::Identifier(id) => {
            FieldElementExpression::Identifier(f.fold_name(id))
        }
        FieldElementExpression::Add(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            FieldElementExpression::Add(box e1, box e2)
        }
        FieldElementExpression::Sub(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            FieldElementExpression::Sub(box e1, box e2)
        }
        FieldElementExpression::Mult(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            FieldElementExpression::Mult(box e1, box e2)
        }
        FieldElementExpression::Div(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            FieldElementExpression::Div(box e1, box e2)
        }
        FieldElementExpression::Pow(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            FieldElementExpression::Pow(box e1, box e2)
        }
        FieldElementExpression::IfElse(box cond, box cons, box alt) => {
            let cond = f.fold_boolean_expression(cond);
            let cons = f.fold_field_expression(cons);
            let alt = f.fold_field_expression(alt);
            FieldElementExpression::IfElse(box cond, box cons, box alt)
        }
        FieldElementExpression::FunctionCall(id, exps) => {
            let exps = exps.into_iter().map(|e| f.fold_expression(e)).collect();
            FieldElementExpression::FunctionCall(id, exps)
        }
        FieldElementExpression::Select(box array, box index) => {
            let array = f.fold_field_array_expression(array);
            let index = f.fold_field_expression(index);
            FieldElementExpression::Select(box array, box index)
        }
    }
}

pub fn fold_boolean_expression<T: Field, F: Folder<T>>(
    f: &mut F,
    e: BooleanExpression<T>,
) -> BooleanExpression<T> {
    match e {
        BooleanExpression::Value(v) => BooleanExpression::Value(v),
        BooleanExpression::Identifier(id) => BooleanExpression::Identifier(f.fold_name(id)),
        BooleanExpression::Eq(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            BooleanExpression::Eq(box e1, box e2)
        }
        BooleanExpression::Lt(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            BooleanExpression::Lt(box e1, box e2)
        }
        BooleanExpression::Le(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            BooleanExpression::Le(box e1, box e2)
        }
        BooleanExpression::Gt(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            BooleanExpression::Gt(box e1, box e2)
        }
        BooleanExpression::Ge(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            BooleanExpression::Ge(box e1, box e2)
        }
        BooleanExpression::Or(box e1, box e2) => {
            let e1 = f.fold_boolean_expression(e1);
            let e2 = f.fold_boolean_expression(e2);
            BooleanExpression::Or(box e1, box e2)
        }
        BooleanExpression::And(box e1, box e2) => {
            let e1 = f.fold_boolean_expression(e1);
            let e2 = f.fold_boolean_expression(e2);
            BooleanExpression::And(box e1, box e2)
        }
        BooleanExpression::Not(box e) => {
            let e = f.fold_boolean_expression(e);
            BooleanExpression::Not(box e)
        }
    }
}

pub fn fold_function<T: Field, F: Folder<T>>(f: &mut F, fun: TypedFunction<T>) -> TypedFunction<T> {
    TypedFunction {
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
