// Generic walk through ZIR. Not mutating in place

use crate::typed::identifier::IdTrait;
use crate::zir::types::UBitwidth;
use crate::zir::*;
use zokrates_field::Field;

pub trait Fold<I: IdTrait, T: Field>: Sized {
    fn fold<F: Folder<I, T>>(self, f: &mut F) -> Self;
}

impl<I: IdTrait, T: Field> Fold<I, T> for FieldElementExpression<I, T> {
    fn fold<F: Folder<I, T>>(self, f: &mut F) -> Self {
        f.fold_field_expression(self)
    }
}

impl<I: IdTrait, T: Field> Fold<I, T> for BooleanExpression<I, T> {
    fn fold<F: Folder<I, T>>(self, f: &mut F) -> Self {
        f.fold_boolean_expression(self)
    }
}

impl<I: IdTrait, T: Field> Fold<I, T> for UExpression<I, T> {
    fn fold<F: Folder<I, T>>(self, f: &mut F) -> Self {
        f.fold_uint_expression(self)
    }
}
pub trait Folder<I: IdTrait, T: Field>: Sized {
    fn fold_program(&mut self, p: ZirProgram<I, T>) -> ZirProgram<I, T> {
        fold_program(self, p)
    }

    fn fold_function(&mut self, f: ZirFunction<I, T>) -> ZirFunction<I, T> {
        fold_function(self, f)
    }

    fn fold_parameter(&mut self, p: Parameter<I>) -> Parameter<I> {
        Parameter {
            id: self.fold_variable(p.id),
            ..p
        }
    }

    fn fold_name(&mut self, n: Identifier<I>) -> Identifier<I> {
        n
    }

    fn fold_variable(&mut self, v: Variable<I>) -> Variable<I> {
        Variable {
            id: self.fold_name(v.id),
            ..v
        }
    }

    fn fold_assignee(&mut self, a: ZirAssignee<I>) -> ZirAssignee<I> {
        self.fold_variable(a)
    }

    fn fold_statement(&mut self, s: ZirStatement<I, T>) -> Vec<ZirStatement<I, T>> {
        fold_statement(self, s)
    }

    fn fold_identifier_expression<E: Expr<I, T> + Id<I, T>>(
        &mut self,
        ty: &E::Ty,
        e: IdentifierExpression<I, E>,
    ) -> IdentifierOrExpression<I, T, E> {
        fold_identifier_expression(self, ty, e)
    }

    fn fold_conditional_expression<E: Expr<I, T> + Fold<I, T> + Conditional<I, T>>(
        &mut self,
        ty: &E::Ty,
        e: ConditionalExpression<I, T, E>,
    ) -> ConditionalOrExpression<I, T, E> {
        fold_conditional_expression(self, ty, e)
    }

    fn fold_select_expression<E: Expr<I, T> + Fold<I, T> + Select<I, T>>(
        &mut self,
        ty: &E::Ty,
        e: SelectExpression<I, T, E>,
    ) -> SelectOrExpression<I, T, E> {
        fold_select_expression(self, ty, e)
    }

    fn fold_expression(&mut self, e: ZirExpression<I, T>) -> ZirExpression<I, T> {
        match e {
            ZirExpression::FieldElement(e) => self.fold_field_expression(e).into(),
            ZirExpression::Boolean(e) => self.fold_boolean_expression(e).into(),
            ZirExpression::Uint(e) => self.fold_uint_expression(e).into(),
        }
    }

    fn fold_expression_list(&mut self, es: ZirExpressionList<I, T>) -> ZirExpressionList<I, T> {
        match es {
            ZirExpressionList::EmbedCall(embed, generics, arguments) => {
                ZirExpressionList::EmbedCall(
                    embed,
                    generics,
                    arguments
                        .into_iter()
                        .map(|a| self.fold_expression(a))
                        .collect(),
                )
            }
        }
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<I, T>,
    ) -> FieldElementExpression<I, T> {
        fold_field_expression(self, e)
    }
    fn fold_boolean_expression(&mut self, e: BooleanExpression<I, T>) -> BooleanExpression<I, T> {
        fold_boolean_expression(self, e)
    }
    fn fold_uint_expression(&mut self, e: UExpression<I, T>) -> UExpression<I, T> {
        fold_uint_expression(self, e)
    }

    fn fold_uint_expression_inner(
        &mut self,
        bitwidth: UBitwidth,
        e: UExpressionInner<I, T>,
    ) -> UExpressionInner<I, T> {
        fold_uint_expression_inner(self, bitwidth, e)
    }
}

pub fn fold_statement<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    s: ZirStatement<I, T>,
) -> Vec<ZirStatement<I, T>> {
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
        ZirStatement::IfElse(condition, consequence, alternative) => ZirStatement::IfElse(
            f.fold_boolean_expression(condition),
            consequence
                .into_iter()
                .flat_map(|e| f.fold_statement(e))
                .collect(),
            alternative
                .into_iter()
                .flat_map(|e| f.fold_statement(e))
                .collect(),
        ),
        ZirStatement::Assertion(e, error) => {
            ZirStatement::Assertion(f.fold_boolean_expression(e), error)
        }
        ZirStatement::MultipleDefinition(variables, elist) => ZirStatement::MultipleDefinition(
            variables.into_iter().map(|v| f.fold_variable(v)).collect(),
            f.fold_expression_list(elist),
        ),
        ZirStatement::Log(l, e) => ZirStatement::Log(
            l,
            e.into_iter()
                .map(|(t, e)| (t, e.into_iter().map(|e| f.fold_expression(e)).collect()))
                .collect(),
        ),
    };
    vec![res]
}

pub fn fold_identifier_expression<
    I: IdTrait,
    T: Field,
    E: Expr<I, T> + Id<I, T>,
    F: Folder<I, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: IdentifierExpression<I, E>,
) -> IdentifierOrExpression<I, T, E> {
    IdentifierOrExpression::Identifier(IdentifierExpression::new(f.fold_name(e.id)))
}

pub fn fold_field_expression<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    e: FieldElementExpression<I, T>,
) -> FieldElementExpression<I, T> {
    match e {
        FieldElementExpression::Number(n) => FieldElementExpression::Number(n),
        FieldElementExpression::Identifier(id) => {
            match f.fold_identifier_expression(&Type::FieldElement, id) {
                IdentifierOrExpression::Identifier(i) => FieldElementExpression::Identifier(i),
                IdentifierOrExpression::Expression(e) => e,
            }
        }
        FieldElementExpression::Select(e) => {
            match f.fold_select_expression(&Type::FieldElement, e) {
                SelectOrExpression::Select(s) => FieldElementExpression::Select(s),
                SelectOrExpression::Expression(u) => u,
            }
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
            let e2 = f.fold_uint_expression(e2);
            FieldElementExpression::Pow(box e1, box e2)
        }
        FieldElementExpression::Conditional(c) => {
            match f.fold_conditional_expression(&Type::FieldElement, c) {
                ConditionalOrExpression::Conditional(s) => FieldElementExpression::Conditional(s),
                ConditionalOrExpression::Expression(u) => u,
            }
        }
    }
}

pub fn fold_boolean_expression<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    e: BooleanExpression<I, T>,
) -> BooleanExpression<I, T> {
    match e {
        BooleanExpression::Value(v) => BooleanExpression::Value(v),
        BooleanExpression::Identifier(id) => match f.fold_identifier_expression(&Type::Boolean, id)
        {
            IdentifierOrExpression::Identifier(i) => BooleanExpression::Identifier(i),
            IdentifierOrExpression::Expression(e) => e,
        },
        BooleanExpression::Select(e) => match f.fold_select_expression(&Type::Boolean, e) {
            SelectOrExpression::Select(s) => BooleanExpression::Select(s),
            SelectOrExpression::Expression(u) => u,
        },
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
        BooleanExpression::UintEq(box e1, box e2) => {
            let e1 = f.fold_uint_expression(e1);
            let e2 = f.fold_uint_expression(e2);
            BooleanExpression::UintEq(box e1, box e2)
        }
        BooleanExpression::FieldLt(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            BooleanExpression::FieldLt(box e1, box e2)
        }
        BooleanExpression::UintLt(box e1, box e2) => {
            let e1 = f.fold_uint_expression(e1);
            let e2 = f.fold_uint_expression(e2);
            BooleanExpression::UintLt(box e1, box e2)
        }
        BooleanExpression::FieldLe(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            BooleanExpression::FieldLe(box e1, box e2)
        }
        BooleanExpression::UintLe(box e1, box e2) => {
            let e1 = f.fold_uint_expression(e1);
            let e2 = f.fold_uint_expression(e2);
            BooleanExpression::UintLe(box e1, box e2)
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
        BooleanExpression::Conditional(c) => match f.fold_conditional_expression(&Type::Boolean, c)
        {
            ConditionalOrExpression::Conditional(s) => BooleanExpression::Conditional(s),
            ConditionalOrExpression::Expression(u) => u,
        },
    }
}

pub fn fold_uint_expression<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    e: UExpression<I, T>,
) -> UExpression<I, T> {
    UExpression {
        inner: f.fold_uint_expression_inner(e.bitwidth, e.inner),
        ..e
    }
}

pub fn fold_uint_expression_inner<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    ty: UBitwidth,
    e: UExpressionInner<I, T>,
) -> UExpressionInner<I, T> {
    match e {
        UExpressionInner::Value(v) => UExpressionInner::Value(v),
        UExpressionInner::Identifier(id) => match f.fold_identifier_expression(&ty, id) {
            IdentifierOrExpression::Identifier(i) => UExpressionInner::Identifier(i),
            IdentifierOrExpression::Expression(e) => e,
        },
        UExpressionInner::Select(e) => match f.fold_select_expression(&ty, e) {
            SelectOrExpression::Select(s) => UExpressionInner::Select(s),
            SelectOrExpression::Expression(u) => u,
        },
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
        UExpressionInner::Div(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            UExpressionInner::Div(box left, box right)
        }
        UExpressionInner::Rem(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            UExpressionInner::Rem(box left, box right)
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
        UExpressionInner::LeftShift(box e, by) => {
            let e = f.fold_uint_expression(e);

            UExpressionInner::LeftShift(box e, by)
        }
        UExpressionInner::RightShift(box e, by) => {
            let e = f.fold_uint_expression(e);

            UExpressionInner::RightShift(box e, by)
        }
        UExpressionInner::Not(box e) => {
            let e = f.fold_uint_expression(e);

            UExpressionInner::Not(box e)
        }
        UExpressionInner::Conditional(c) => match f.fold_conditional_expression(&ty, c) {
            ConditionalOrExpression::Conditional(s) => UExpressionInner::Conditional(s),
            ConditionalOrExpression::Expression(u) => u,
        },
    }
}

pub fn fold_function<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    fun: ZirFunction<I, T>,
) -> ZirFunction<I, T> {
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

pub fn fold_program<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    p: ZirProgram<I, T>,
) -> ZirProgram<I, T> {
    ZirProgram {
        main: f.fold_function(p.main),
    }
}

pub fn fold_conditional_expression<
    I: IdTrait,
    T: Field,
    E: Expr<I, T> + Fold<I, T> + Conditional<I, T>,
    F: Folder<I, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: ConditionalExpression<I, T, E>,
) -> ConditionalOrExpression<I, T, E> {
    ConditionalOrExpression::Conditional(ConditionalExpression::new(
        f.fold_boolean_expression(*e.condition),
        e.consequence.fold(f),
        e.alternative.fold(f),
    ))
}

pub fn fold_select_expression<
    I: IdTrait,
    T: Field,
    E: Expr<I, T> + Fold<I, T> + Select<I, T>,
    F: Folder<I, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: SelectExpression<I, T, E>,
) -> SelectOrExpression<I, T, E> {
    SelectOrExpression::Select(SelectExpression::new(
        e.array.into_iter().map(|e| e.fold(f)).collect(),
        e.index.fold(f),
    ))
}
