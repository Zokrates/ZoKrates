// Generic walk through a typed AST. Not mutating in place

use crate::zir::*;
use zokrates_field::field::Field;

pub trait Folder<'ast, T: Field>: Sized {
    fn fold_program(&mut self, p: ZirProgram<'ast, T>) -> ZirProgram<'ast, T> {
        fold_program(self, p)
    }

    fn fold_module(&mut self, p: ZirModule<'ast, T>) -> ZirModule<'ast, T> {
        fold_module(self, p)
    }

    fn fold_function_symbol(
        &mut self,
        s: ZirFunctionSymbol<'ast, T>,
    ) -> ZirFunctionSymbol<'ast, T> {
        fold_function_symbol(self, s)
    }

    fn fold_function(&mut self, f: ZirFunction<'ast, T>) -> ZirFunction<'ast, T> {
        fold_function(self, f)
    }

    fn fold_parameter(&mut self, p: Parameter<'ast>) -> Parameter<'ast> {
        Parameter {
            id: self.fold_variable(p.id),
            ..p
        }
    }

    fn fold_name(&mut self, n: Identifier<'ast>) -> Identifier<'ast> {
        n
    }

    fn fold_variable(&mut self, v: Variable<'ast>) -> Variable<'ast> {
        Variable {
            id: self.fold_name(v.id),
            ..v
        }
    }

    fn fold_assignee(&mut self, a: ZirAssignee<'ast>) -> ZirAssignee<'ast> {
        self.fold_variable(a)
    }

    fn fold_statement(&mut self, s: ZirStatement<'ast, T>) -> Vec<ZirStatement<'ast, T>> {
        fold_statement(self, s)
    }

    fn fold_expression(&mut self, e: ZirExpression<'ast, T>) -> ZirExpression<'ast, T> {
        match e {
            ZirExpression::FieldElement(e) => self.fold_field_expression(e).into(),
            ZirExpression::Boolean(e) => self.fold_boolean_expression(e).into(),
            ZirExpression::U32(e) => self.fold_uint_expression(e).into(),
            ZirExpression::U16(e) => self.fold_uint_expression(e).into(),
            ZirExpression::U8(e) => self.fold_uint_expression(e).into(),
        }
    }

    fn fold_expression_list(
        &mut self,
        es: ZirExpressionList<'ast, T>,
    ) -> ZirExpressionList<'ast, T> {
        match es {
            ZirExpressionList::FunctionCall(id, arguments, types) => {
                ZirExpressionList::FunctionCall(
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

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        fold_field_expression(self, e)
    }
    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> BooleanExpression<'ast, T> {
        fold_boolean_expression(self, e)
    }
    fn fold_uint_expression<U: Uint>(
        &mut self,
        e: UExpression<'ast, U, T>,
    ) -> UExpression<'ast, U, T> {
        fold_uint_expression(self, e)
    }

    fn fold_uint_expression_inner<U: Uint>(
        &mut self,
        e: UExpressionInner<'ast, U, T>,
    ) -> UExpressionInner<'ast, U, T> {
        fold_uint_expression_inner(self, e)
    }
}

pub fn fold_module<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    p: ZirModule<'ast, T>,
) -> ZirModule<'ast, T> {
    ZirModule {
        functions: p
            .functions
            .into_iter()
            .map(|(key, fun)| (key, f.fold_function_symbol(fun)))
            .collect(),
        ..p
    }
}

pub fn fold_statement<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: ZirStatement<'ast, T>,
) -> Vec<ZirStatement<'ast, T>> {
    let res = match s {
        ZirStatement::Return(expressions) => ZirStatement::Return(
            expressions
                .into_iter()
                .map(|e| f.fold_expression(e))
                .collect(),
        ),
        ZirStatement::Definition(a, e) => {
            ZirStatement::Definition(f.fold_assignee(a), f.fold_expression(e))
        }
        ZirStatement::Declaration(v) => ZirStatement::Declaration(f.fold_variable(v)),
        ZirStatement::Condition(left, right) => {
            ZirStatement::Condition(f.fold_expression(left), f.fold_expression(right))
        }
        ZirStatement::MultipleDefinition(variables, elist) => ZirStatement::MultipleDefinition(
            variables.into_iter().map(|v| f.fold_variable(v)).collect(),
            f.fold_expression_list(elist),
        ),
    };
    vec![res]
}

pub fn fold_field_expression<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: FieldElementExpression<'ast, T>,
) -> FieldElementExpression<'ast, T> {
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
        FieldElementExpression::FunctionCall(key, exps) => {
            let exps = exps.into_iter().map(|e| f.fold_expression(e)).collect();
            FieldElementExpression::FunctionCall(key, exps)
        }
    }
}

pub fn fold_boolean_expression<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: BooleanExpression<'ast, T>,
) -> BooleanExpression<'ast, T> {
    match e {
        BooleanExpression::Value(v) => BooleanExpression::Value(v),
        BooleanExpression::Identifier(id) => BooleanExpression::Identifier(f.fold_name(id)),
        BooleanExpression::FieldEq(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            BooleanExpression::FieldEq(box e1, box e2)
        }
        BooleanExpression::BoolEq(box e1, box e2) => {
            let e1 = f.fold_boolean_expression(e1);
            let e2 = f.fold_boolean_expression(e2);
            BooleanExpression::BoolEq(box e1, box e2)
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
        BooleanExpression::IfElse(box cond, box cons, box alt) => {
            let cond = f.fold_boolean_expression(cond);
            let cons = f.fold_boolean_expression(cons);
            let alt = f.fold_boolean_expression(alt);
            BooleanExpression::IfElse(box cond, box cons, box alt)
        }
    }
}

pub fn fold_uint_expression<'ast, U: Uint, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: UExpression<'ast, U, T>,
) -> UExpression<'ast, U, T> {
    UExpression {
        inner: f.fold_uint_expression_inner(e.inner),
        ..e
    }
}

pub fn fold_uint_expression_inner<'ast, U: Uint, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: UExpressionInner<'ast, U, T>,
) -> UExpressionInner<'ast, U, T> {
    match e {
        UExpressionInner::Value(v) => UExpressionInner::Value(v),
        UExpressionInner::Identifier(id) => UExpressionInner::Identifier(f.fold_name(id)),
        UExpressionInner::Add(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            UExpressionInner::Add(box left, box right)
        }
        UExpressionInner::Sub(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            UExpressionInner::Sub(box left, box right)
        }
        UExpressionInner::Mult(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            UExpressionInner::Mult(box left, box right)
        }
        UExpressionInner::Xor(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            UExpressionInner::Xor(box left, box right)
        }
        UExpressionInner::And(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            UExpressionInner::And(box left, box right)
        }
        UExpressionInner::Or(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            UExpressionInner::Or(box left, box right)
        }
        UExpressionInner::LeftShift(box e, box by) => {
            let e = f.fold_uint_expression(e);
            let by = f.fold_field_expression(by);

            UExpressionInner::LeftShift(box e, box by)
        }
        UExpressionInner::RightShift(box e, box by) => {
            let e = f.fold_uint_expression(e);
            let by = f.fold_field_expression(by);

            UExpressionInner::RightShift(box e, box by)
        }
        UExpressionInner::Not(box e) => {
            let e = f.fold_uint_expression(e);

            UExpressionInner::Not(box e)
        }
        UExpressionInner::FunctionCall(key, exps) => {
            let exps = exps.into_iter().map(|e| f.fold_expression(e)).collect();
            UExpressionInner::FunctionCall(key, exps)
        }
        UExpressionInner::IfElse(box cond, box cons, box alt) => {
            let cond = f.fold_boolean_expression(cond);
            let cons = f.fold_uint_expression(cons);
            let alt = f.fold_uint_expression(alt);
            UExpressionInner::IfElse(box cond, box cons, box alt)
        }
    }
}

pub fn fold_function<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    fun: ZirFunction<'ast, T>,
) -> ZirFunction<'ast, T> {
    ZirFunction {
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

pub fn fold_function_symbol<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: ZirFunctionSymbol<'ast, T>,
) -> ZirFunctionSymbol<'ast, T> {
    match s {
        ZirFunctionSymbol::Here(fun) => ZirFunctionSymbol::Here(f.fold_function(fun)),
        there => there, // by default, do not fold modules recursively
    }
}

pub fn fold_program<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    p: ZirProgram<'ast, T>,
) -> ZirProgram<'ast, T> {
    ZirProgram {
        modules: p
            .modules
            .into_iter()
            .map(|(module_id, module)| (module_id, f.fold_module(module)))
            .collect(),
        main: p.main,
    }
}
