// Generic walk through ZIR. Not mutating in place

use crate::common::expressions::{BinaryOrExpression, IdentifierOrExpression, UnaryOrExpression};
use crate::common::{Fold, WithSpan};
use crate::zir::types::UBitwidth;
use crate::zir::*;
use zokrates_field::Field;

impl<'ast, T: Field, F: Folder<'ast, T>> Fold<F> for FieldElementExpression<'ast, T> {
    fn fold(self, f: &mut F) -> Self {
        f.fold_field_expression(self)
    }
}

impl<'ast, T: Field, F: Folder<'ast, T>> Fold<F> for BooleanExpression<'ast, T> {
    fn fold(self, f: &mut F) -> Self {
        f.fold_boolean_expression(self)
    }
}

impl<'ast, T: Field, F: Folder<'ast, T>> Fold<F> for UExpression<'ast, T> {
    fn fold(self, f: &mut F) -> Self {
        f.fold_uint_expression(self)
    }
}
pub trait Folder<'ast, T: Field>: Sized {
    fn fold_program(&mut self, p: ZirProgram<'ast, T>) -> ZirProgram<'ast, T> {
        fold_program(self, p)
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

    fn fold_identifier_expression<E: Expr<'ast, T> + Id<'ast, T>>(
        &mut self,
        ty: &E::Ty,
        e: IdentifierExpression<'ast, E>,
    ) -> IdentifierOrExpression<Identifier<'ast>, E, E::Inner> {
        fold_identifier_expression(self, ty, e)
    }

    fn fold_conditional_expression<E: Expr<'ast, T> + Fold<Self> + Conditional<'ast, T>>(
        &mut self,
        ty: &E::Ty,
        e: ConditionalExpression<'ast, T, E>,
    ) -> ConditionalOrExpression<'ast, T, E> {
        fold_conditional_expression(self, ty, e)
    }

    fn fold_select_expression<E: Expr<'ast, T> + Fold<Self> + Select<'ast, T>>(
        &mut self,
        ty: &E::Ty,
        e: SelectExpression<'ast, T, E>,
    ) -> SelectOrExpression<'ast, T, E> {
        fold_select_expression(self, ty, e)
    }

    fn fold_binary_expression<
        L: Expr<'ast, T> + Fold<Self>,
        R: Expr<'ast, T> + Fold<Self>,
        E: Expr<'ast, T> + Fold<Self>,
        Op,
    >(
        &mut self,
        ty: &E::Ty,
        e: BinaryExpression<Op, L, R, E>,
    ) -> BinaryOrExpression<Op, L, R, E, E::Inner> {
        fold_binary_expression(self, ty, e)
    }

    fn fold_unary_expression<In: Expr<'ast, T> + Fold<Self>, E: Expr<'ast, T> + Fold<Self>, Op>(
        &mut self,
        ty: &E::Ty,
        e: UnaryExpression<Op, In, E>,
    ) -> UnaryOrExpression<Op, In, E, E::Inner> {
        fold_unary_expression(self, ty, e)
    }

    fn fold_expression(&mut self, e: ZirExpression<'ast, T>) -> ZirExpression<'ast, T> {
        match e {
            ZirExpression::FieldElement(e) => self.fold_field_expression(e).into(),
            ZirExpression::Boolean(e) => self.fold_boolean_expression(e).into(),
            ZirExpression::Uint(e) => self.fold_uint_expression(e).into(),
        }
    }

    fn fold_expression_list(
        &mut self,
        es: ZirExpressionList<'ast, T>,
    ) -> ZirExpressionList<'ast, T> {
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
    fn fold_uint_expression(&mut self, e: UExpression<'ast, T>) -> UExpression<'ast, T> {
        fold_uint_expression(self, e)
    }

    fn fold_uint_expression_inner(
        &mut self,
        bitwidth: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> UExpressionInner<'ast, T> {
        fold_uint_expression_inner(self, bitwidth, e)
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
    'ast,
    T: Field,
    E: Expr<'ast, T> + Id<'ast, T>,
    F: Folder<'ast, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: IdentifierExpression<'ast, E>,
) -> IdentifierOrExpression<Identifier<'ast>, E, E::Inner> {
    IdentifierOrExpression::Identifier(IdentifierExpression::new(f.fold_name(e.id)))
}

pub fn fold_field_expression<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: FieldElementExpression<'ast, T>,
) -> FieldElementExpression<'ast, T> {
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
        FieldElementExpression::Add(e) => match f.fold_binary_expression(&Type::FieldElement, e) {
            BinaryOrExpression::Binary(e) => FieldElementExpression::Add(e),
            BinaryOrExpression::Expression(e) => e,
        },
        FieldElementExpression::Sub(e) => match f.fold_binary_expression(&Type::FieldElement, e) {
            BinaryOrExpression::Binary(e) => FieldElementExpression::Sub(e),
            BinaryOrExpression::Expression(e) => e,
        },
        FieldElementExpression::Mult(e) => match f.fold_binary_expression(&Type::FieldElement, e) {
            BinaryOrExpression::Binary(e) => FieldElementExpression::Mult(e),
            BinaryOrExpression::Expression(e) => e,
        },
        FieldElementExpression::Div(e) => match f.fold_binary_expression(&Type::FieldElement, e) {
            BinaryOrExpression::Binary(e) => FieldElementExpression::Div(e),
            BinaryOrExpression::Expression(e) => e,
        },
        FieldElementExpression::Pow(e) => match f.fold_binary_expression(&Type::FieldElement, e) {
            BinaryOrExpression::Binary(e) => FieldElementExpression::Pow(e),
            BinaryOrExpression::Expression(e) => e,
        },
        FieldElementExpression::Conditional(c) => {
            match f.fold_conditional_expression(&Type::FieldElement, c) {
                ConditionalOrExpression::Conditional(s) => FieldElementExpression::Conditional(s),
                ConditionalOrExpression::Expression(u) => u,
            }
        }
    }
}

pub fn fold_boolean_expression<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: BooleanExpression<'ast, T>,
) -> BooleanExpression<'ast, T> {
    use BooleanExpression::*;

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
        FieldEq(e) => match f.fold_binary_expression(&Type::Boolean, e) {
            BinaryOrExpression::Binary(e) => FieldEq(e),
            BinaryOrExpression::Expression(u) => u,
        },
        BoolEq(e) => match f.fold_binary_expression(&Type::Boolean, e) {
            BinaryOrExpression::Binary(e) => BoolEq(e),
            BinaryOrExpression::Expression(u) => u,
        },
        UintEq(e) => match f.fold_binary_expression(&Type::Boolean, e) {
            BinaryOrExpression::Binary(e) => UintEq(e),
            BinaryOrExpression::Expression(u) => u,
        },
        FieldLt(e) => match f.fold_binary_expression(&Type::Boolean, e) {
            BinaryOrExpression::Binary(e) => FieldLt(e),
            BinaryOrExpression::Expression(u) => u,
        },
        FieldLe(e) => match f.fold_binary_expression(&Type::Boolean, e) {
            BinaryOrExpression::Binary(e) => FieldLe(e),
            BinaryOrExpression::Expression(u) => u,
        },
        UintLt(e) => match f.fold_binary_expression(&Type::Boolean, e) {
            BinaryOrExpression::Binary(e) => UintLt(e),
            BinaryOrExpression::Expression(u) => u,
        },
        UintLe(e) => match f.fold_binary_expression(&Type::Boolean, e) {
            BinaryOrExpression::Binary(e) => UintLe(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Or(e) => match f.fold_binary_expression(&Type::Boolean, e) {
            BinaryOrExpression::Binary(e) => Or(e),
            BinaryOrExpression::Expression(u) => u,
        },
        And(e) => match f.fold_binary_expression(&Type::Boolean, e) {
            BinaryOrExpression::Binary(e) => And(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Not(e) => match f.fold_unary_expression(&Type::Boolean, e) {
            UnaryOrExpression::Unary(e) => Not(e),
            UnaryOrExpression::Expression(u) => u,
        },
        BooleanExpression::Conditional(c) => match f.fold_conditional_expression(&Type::Boolean, c)
        {
            ConditionalOrExpression::Conditional(s) => BooleanExpression::Conditional(s),
            ConditionalOrExpression::Expression(u) => u,
        },
    }
}

pub fn fold_uint_expression<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: UExpression<'ast, T>,
) -> UExpression<'ast, T> {
    UExpression {
        inner: f.fold_uint_expression_inner(e.bitwidth, e.inner),
        ..e
    }
}

pub fn fold_uint_expression_inner<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    ty: UBitwidth,
    e: UExpressionInner<'ast, T>,
) -> UExpressionInner<'ast, T> {
    use UExpressionInner::*;

    match e {
        Value(v) => UExpressionInner::Value(v),
        Identifier(id) => match f.fold_identifier_expression(&ty, id) {
            IdentifierOrExpression::Identifier(i) => UExpressionInner::Identifier(i),
            IdentifierOrExpression::Expression(e) => e,
        },
        Select(e) => match f.fold_select_expression(&ty, e) {
            SelectOrExpression::Select(s) => UExpressionInner::Select(s),
            SelectOrExpression::Expression(u) => u,
        },
        Add(e) => match f.fold_binary_expression(&ty, e) {
            BinaryOrExpression::Binary(e) => Add(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Sub(e) => match f.fold_binary_expression(&ty, e) {
            BinaryOrExpression::Binary(e) => Sub(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Mult(e) => match f.fold_binary_expression(&ty, e) {
            BinaryOrExpression::Binary(e) => Mult(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Div(e) => match f.fold_binary_expression(&ty, e) {
            BinaryOrExpression::Binary(e) => Div(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Rem(e) => match f.fold_binary_expression(&ty, e) {
            BinaryOrExpression::Binary(e) => Rem(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Xor(e) => match f.fold_binary_expression(&ty, e) {
            BinaryOrExpression::Binary(e) => Xor(e),
            BinaryOrExpression::Expression(u) => u,
        },
        And(e) => match f.fold_binary_expression(&ty, e) {
            BinaryOrExpression::Binary(e) => And(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Or(e) => match f.fold_binary_expression(&ty, e) {
            BinaryOrExpression::Binary(e) => Or(e),
            BinaryOrExpression::Expression(u) => u,
        },
        LeftShift(e) => match f.fold_binary_expression(&ty, e) {
            BinaryOrExpression::Binary(e) => LeftShift(e),
            BinaryOrExpression::Expression(u) => u,
        },
        RightShift(e) => match f.fold_binary_expression(&ty, e) {
            BinaryOrExpression::Binary(e) => RightShift(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Not(e) => match f.fold_unary_expression(&ty, e) {
            UnaryOrExpression::Unary(e) => Not(e),
            UnaryOrExpression::Expression(u) => u,
        },
        UExpressionInner::Conditional(c) => match f.fold_conditional_expression(&ty, c) {
            ConditionalOrExpression::Conditional(s) => Conditional(s),
            ConditionalOrExpression::Expression(u) => u,
        },
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

pub fn fold_program<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    p: ZirProgram<'ast, T>,
) -> ZirProgram<'ast, T> {
    ZirProgram {
        main: f.fold_function(p.main),
    }
}

pub fn fold_conditional_expression<
    'ast,
    T: Field,
    E: Expr<'ast, T> + Fold<F> + Conditional<'ast, T>,
    F: Folder<'ast, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: ConditionalExpression<'ast, T, E>,
) -> ConditionalOrExpression<'ast, T, E> {
    ConditionalOrExpression::Conditional(ConditionalExpression::new(
        f.fold_boolean_expression(*e.condition),
        e.consequence.fold(f),
        e.alternative.fold(f),
    ))
}

pub fn fold_select_expression<
    'ast,
    T: Field,
    E: Expr<'ast, T> + Fold<F> + Select<'ast, T>,
    F: Folder<'ast, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: SelectExpression<'ast, T, E>,
) -> SelectOrExpression<'ast, T, E> {
    SelectOrExpression::Select(SelectExpression::new(
        e.array.into_iter().map(|e| e.fold(f)).collect(),
        e.index.fold(f),
    ))
}

pub fn fold_binary_expression<
    'ast,
    T: Field,
    L: Expr<'ast, T> + Fold<F> + From<ZirExpression<'ast, T>>,
    R: Expr<'ast, T> + Fold<F> + From<ZirExpression<'ast, T>>,
    E: Expr<'ast, T> + Fold<F> + From<ZirExpression<'ast, T>>,
    F: Folder<'ast, T>,
    Op,
>(
    f: &mut F,
    _: &E::Ty,
    e: BinaryExpression<Op, L, R, E>,
) -> BinaryOrExpression<Op, L, R, E, E::Inner> {
    BinaryOrExpression::Binary(BinaryExpression::new(e.left.fold(f), e.right.fold(f)).span(e.span))
}

pub fn fold_unary_expression<
    'ast,
    T: Field,
    In: Expr<'ast, T> + Fold<F> + From<ZirExpression<'ast, T>>,
    E: Expr<'ast, T> + Fold<F> + From<ZirExpression<'ast, T>>,
    F: Folder<'ast, T>,
    Op,
>(
    f: &mut F,
    _: &E::Ty,
    e: UnaryExpression<Op, In, E>,
) -> UnaryOrExpression<Op, In, E, E::Inner> {
    UnaryOrExpression::Unary(UnaryExpression::new(e.inner.fold(f)).span(e.span))
}
