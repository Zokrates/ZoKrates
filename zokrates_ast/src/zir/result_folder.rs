// Generic walk through ZIR. Not mutating in place

use crate::common::expressions::{BinaryOrExpression, IdentifierOrExpression, UnaryOrExpression};
use crate::common::ResultFold;
use crate::common::WithSpan;
use crate::zir::types::UBitwidth;
use crate::zir::*;
use zokrates_field::Field;

impl<'ast, T: Field, F: ResultFolder<'ast, T>> ResultFold<F, F::Error>
    for FieldElementExpression<'ast, T>
{
    fn fold(self, f: &mut F) -> Result<Self, F::Error> {
        f.fold_field_expression(self)
    }
}

impl<'ast, T: Field, F: ResultFolder<'ast, T>> ResultFold<F, F::Error>
    for BooleanExpression<'ast, T>
{
    fn fold(self, f: &mut F) -> Result<Self, F::Error> {
        f.fold_boolean_expression(self)
    }
}

impl<'ast, T: Field, F: ResultFolder<'ast, T>> ResultFold<F, F::Error> for UExpression<'ast, T> {
    fn fold(self, f: &mut F) -> Result<Self, F::Error> {
        f.fold_uint_expression(self)
    }
}
pub trait ResultFolder<'ast, T: Field>: Sized {
    type Error;

    fn fold_program(&mut self, p: ZirProgram<'ast, T>) -> Result<ZirProgram<'ast, T>, Self::Error> {
        fold_program(self, p)
    }

    fn fold_function(
        &mut self,
        f: ZirFunction<'ast, T>,
    ) -> Result<ZirFunction<'ast, T>, Self::Error> {
        fold_function(self, f)
    }

    fn fold_parameter(&mut self, p: Parameter<'ast>) -> Result<Parameter<'ast>, Self::Error> {
        Ok(Parameter {
            id: self.fold_variable(p.id)?,
            ..p
        })
    }

    fn fold_name(&mut self, n: Identifier<'ast>) -> Result<Identifier<'ast>, Self::Error> {
        Ok(n)
    }

    fn fold_variable(&mut self, v: Variable<'ast>) -> Result<Variable<'ast>, Self::Error> {
        Ok(Variable {
            id: self.fold_name(v.id)?,
            ..v
        })
    }

    fn fold_assignee(&mut self, a: ZirAssignee<'ast>) -> Result<ZirAssignee<'ast>, Self::Error> {
        self.fold_variable(a)
    }

    fn fold_statement(
        &mut self,
        s: ZirStatement<'ast, T>,
    ) -> Result<Vec<ZirStatement<'ast, T>>, Self::Error> {
        fold_statement(self, s)
    }

    fn fold_expression(
        &mut self,
        e: ZirExpression<'ast, T>,
    ) -> Result<ZirExpression<'ast, T>, Self::Error> {
        match e {
            ZirExpression::FieldElement(e) => Ok(self.fold_field_expression(e)?.into()),
            ZirExpression::Boolean(e) => Ok(self.fold_boolean_expression(e)?.into()),
            ZirExpression::Uint(e) => Ok(self.fold_uint_expression(e)?.into()),
        }
    }

    fn fold_expression_list(
        &mut self,
        es: ZirExpressionList<'ast, T>,
    ) -> Result<ZirExpressionList<'ast, T>, Self::Error> {
        match es {
            ZirExpressionList::EmbedCall(embed, generics, arguments) => {
                Ok(ZirExpressionList::EmbedCall(
                    embed,
                    generics,
                    arguments
                        .into_iter()
                        .map(|a| self.fold_expression(a))
                        .collect::<Result<_, _>>()?,
                ))
            }
        }
    }

    fn fold_identifier_expression<
        E: Expr<'ast, T> + Id<'ast, T> + ResultFold<Self, Self::Error>,
    >(
        &mut self,
        ty: &E::Ty,
        id: IdentifierExpression<'ast, E>,
    ) -> Result<IdentifierOrExpression<Identifier<'ast>, E, E::Inner>, Self::Error> {
        fold_identifier_expression(self, ty, id)
    }

    fn fold_conditional_expression<
        E: Expr<'ast, T> + ResultFold<Self, Self::Error> + Conditional<'ast, T>,
    >(
        &mut self,
        ty: &E::Ty,
        e: ConditionalExpression<'ast, T, E>,
    ) -> Result<ConditionalOrExpression<'ast, T, E>, Self::Error> {
        fold_conditional_expression(self, ty, e)
    }

    fn fold_binary_expression<
        L: Expr<'ast, T> + PartialEq + ResultFold<Self, Self::Error>,
        R: Expr<'ast, T> + PartialEq + ResultFold<Self, Self::Error>,
        E: Expr<'ast, T> + PartialEq + ResultFold<Self, Self::Error>,
        Op,
    >(
        &mut self,
        ty: &E::Ty,
        e: BinaryExpression<Op, L, R, E>,
    ) -> Result<BinaryOrExpression<Op, L, R, E, E::Inner>, Self::Error> {
        fold_binary_expression(self, ty, e)
    }

    fn fold_unary_expression<
        In: Expr<'ast, T> + PartialEq + ResultFold<Self, Self::Error>,
        E: Expr<'ast, T> + PartialEq + ResultFold<Self, Self::Error>,
        Op,
    >(
        &mut self,
        ty: &E::Ty,
        e: UnaryExpression<Op, In, E>,
    ) -> Result<UnaryOrExpression<Op, In, E, E::Inner>, Self::Error> {
        fold_unary_expression(self, ty, e)
    }

    fn fold_select_expression<
        E: Clone + Expr<'ast, T> + ResultFold<Self, Self::Error> + Select<'ast, T>,
    >(
        &mut self,
        ty: &E::Ty,
        e: SelectExpression<'ast, T, E>,
    ) -> Result<SelectOrExpression<'ast, T, E>, Self::Error> {
        fold_select_expression(self, ty, e)
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> Result<FieldElementExpression<'ast, T>, Self::Error> {
        fold_field_expression(self, e)
    }

    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> Result<BooleanExpression<'ast, T>, Self::Error> {
        fold_boolean_expression(self, e)
    }

    fn fold_uint_expression(
        &mut self,
        e: UExpression<'ast, T>,
    ) -> Result<UExpression<'ast, T>, Self::Error> {
        fold_uint_expression(self, e)
    }

    fn fold_uint_expression_inner(
        &mut self,
        bitwidth: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> Result<UExpressionInner<'ast, T>, Self::Error> {
        fold_uint_expression_inner(self, bitwidth, e)
    }
}

pub fn fold_statement<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    s: ZirStatement<'ast, T>,
) -> Result<Vec<ZirStatement<'ast, T>>, F::Error> {
    let res = match s {
        ZirStatement::Return(expressions) => ZirStatement::Return(
            expressions
                .into_iter()
                .map(|e| f.fold_expression(e))
                .collect::<Result<_, _>>()?,
        ),
        ZirStatement::Definition(a, e) => {
            ZirStatement::Definition(f.fold_assignee(a)?, f.fold_expression(e)?)
        }
        ZirStatement::IfElse(condition, consequence, alternative) => ZirStatement::IfElse(
            f.fold_boolean_expression(condition)?,
            consequence
                .into_iter()
                .map(|s| f.fold_statement(s))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .flatten()
                .collect(),
            alternative
                .into_iter()
                .map(|s| f.fold_statement(s))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .flatten()
                .collect(),
        ),
        ZirStatement::Assertion(e, error) => {
            ZirStatement::Assertion(f.fold_boolean_expression(e)?, error)
        }
        ZirStatement::MultipleDefinition(variables, elist) => ZirStatement::MultipleDefinition(
            variables
                .into_iter()
                .map(|v| f.fold_assignee(v))
                .collect::<Result<_, _>>()?,
            f.fold_expression_list(elist)?,
        ),
        ZirStatement::Log(l, e) => {
            let e = e
                .into_iter()
                .map(|(t, e)| {
                    e.into_iter()
                        .map(|e| f.fold_expression(e))
                        .collect::<Result<Vec<_>, _>>()
                        .map(|e| (t, e))
                })
                .collect::<Result<Vec<_>, _>>()?;

            ZirStatement::Log(l, e)
        }
    };
    Ok(vec![res])
}

pub fn fold_field_expression<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    e: FieldElementExpression<'ast, T>,
) -> Result<FieldElementExpression<'ast, T>, F::Error> {
    Ok(match e {
        FieldElementExpression::Number(n) => FieldElementExpression::Number(n),
        FieldElementExpression::Identifier(id) => {
            match f.fold_identifier_expression(&Type::FieldElement, id)? {
                IdentifierOrExpression::Identifier(i) => FieldElementExpression::Identifier(i),
                IdentifierOrExpression::Expression(e) => e,
            }
        }
        FieldElementExpression::Select(e) => {
            match f.fold_select_expression(&Type::FieldElement, e)? {
                SelectOrExpression::Select(s) => FieldElementExpression::Select(s),
                SelectOrExpression::Expression(u) => u,
            }
        }
        FieldElementExpression::Add(e) => {
            match f.fold_binary_expression(&Type::FieldElement, e)? {
                BinaryOrExpression::Binary(e) => FieldElementExpression::Add(e),
                BinaryOrExpression::Expression(e) => e,
            }
        }
        FieldElementExpression::Sub(e) => {
            match f.fold_binary_expression(&Type::FieldElement, e)? {
                BinaryOrExpression::Binary(e) => FieldElementExpression::Sub(e),
                BinaryOrExpression::Expression(e) => e,
            }
        }
        FieldElementExpression::Mult(e) => {
            match f.fold_binary_expression(&Type::FieldElement, e)? {
                BinaryOrExpression::Binary(e) => FieldElementExpression::Mult(e),
                BinaryOrExpression::Expression(e) => e,
            }
        }
        FieldElementExpression::Div(e) => {
            match f.fold_binary_expression(&Type::FieldElement, e)? {
                BinaryOrExpression::Binary(e) => FieldElementExpression::Div(e),
                BinaryOrExpression::Expression(e) => e,
            }
        }
        FieldElementExpression::Pow(e) => {
            match f.fold_binary_expression(&Type::FieldElement, e)? {
                BinaryOrExpression::Binary(e) => FieldElementExpression::Pow(e),
                BinaryOrExpression::Expression(e) => e,
            }
        }
        FieldElementExpression::Conditional(c) => {
            match f.fold_conditional_expression(&Type::FieldElement, c)? {
                ConditionalOrExpression::Conditional(s) => FieldElementExpression::Conditional(s),
                ConditionalOrExpression::Expression(u) => u,
            }
        }
    })
}

pub fn fold_boolean_expression<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    e: BooleanExpression<'ast, T>,
) -> Result<BooleanExpression<'ast, T>, F::Error> {
    use BooleanExpression::*;

    Ok(match e {
        BooleanExpression::Value(v) => BooleanExpression::Value(v),
        BooleanExpression::Identifier(id) => {
            match f.fold_identifier_expression(&Type::Boolean, id)? {
                IdentifierOrExpression::Identifier(i) => BooleanExpression::Identifier(i),
                IdentifierOrExpression::Expression(e) => e,
            }
        }
        BooleanExpression::Select(e) => match f.fold_select_expression(&Type::Boolean, e)? {
            SelectOrExpression::Select(s) => BooleanExpression::Select(s),
            SelectOrExpression::Expression(u) => u,
        },
        FieldEq(e) => match f.fold_binary_expression(&Type::Boolean, e)? {
            BinaryOrExpression::Binary(e) => FieldEq(e),
            BinaryOrExpression::Expression(u) => u,
        },
        BoolEq(e) => match f.fold_binary_expression(&Type::Boolean, e)? {
            BinaryOrExpression::Binary(e) => BoolEq(e),
            BinaryOrExpression::Expression(u) => u,
        },
        UintEq(e) => match f.fold_binary_expression(&Type::Boolean, e)? {
            BinaryOrExpression::Binary(e) => UintEq(e),
            BinaryOrExpression::Expression(u) => u,
        },
        FieldLt(e) => match f.fold_binary_expression(&Type::Boolean, e)? {
            BinaryOrExpression::Binary(e) => FieldLt(e),
            BinaryOrExpression::Expression(u) => u,
        },
        FieldLe(e) => match f.fold_binary_expression(&Type::Boolean, e)? {
            BinaryOrExpression::Binary(e) => FieldLe(e),
            BinaryOrExpression::Expression(u) => u,
        },
        UintLt(e) => match f.fold_binary_expression(&Type::Boolean, e)? {
            BinaryOrExpression::Binary(e) => UintLt(e),
            BinaryOrExpression::Expression(u) => u,
        },
        UintLe(e) => match f.fold_binary_expression(&Type::Boolean, e)? {
            BinaryOrExpression::Binary(e) => UintLe(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Or(e) => match f.fold_binary_expression(&Type::Boolean, e)? {
            BinaryOrExpression::Binary(e) => Or(e),
            BinaryOrExpression::Expression(u) => u,
        },
        And(e) => match f.fold_binary_expression(&Type::Boolean, e)? {
            BinaryOrExpression::Binary(e) => And(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Not(e) => match f.fold_unary_expression(&Type::Boolean, e)? {
            UnaryOrExpression::Unary(e) => Not(e),
            UnaryOrExpression::Expression(u) => u,
        },
        BooleanExpression::Conditional(c) => {
            match f.fold_conditional_expression(&Type::Boolean, c)? {
                ConditionalOrExpression::Conditional(s) => BooleanExpression::Conditional(s),
                ConditionalOrExpression::Expression(u) => u,
            }
        }
    })
}

pub fn fold_uint_expression<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    e: UExpression<'ast, T>,
) -> Result<UExpression<'ast, T>, F::Error> {
    Ok(UExpression {
        inner: f.fold_uint_expression_inner(e.bitwidth, e.inner)?,
        ..e
    })
}

pub fn fold_uint_expression_inner<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    ty: UBitwidth,
    e: UExpressionInner<'ast, T>,
) -> Result<UExpressionInner<'ast, T>, F::Error> {
    use UExpressionInner::*;

    Ok(match e {
        Value(v) => UExpressionInner::Value(v),
        Identifier(id) => match f.fold_identifier_expression(&ty, id)? {
            IdentifierOrExpression::Identifier(i) => UExpressionInner::Identifier(i),
            IdentifierOrExpression::Expression(e) => e,
        },
        Select(e) => match f.fold_select_expression(&ty, e)? {
            SelectOrExpression::Select(s) => UExpressionInner::Select(s),
            SelectOrExpression::Expression(u) => u,
        },
        Add(e) => match f.fold_binary_expression(&ty, e)? {
            BinaryOrExpression::Binary(e) => Add(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Sub(e) => match f.fold_binary_expression(&ty, e)? {
            BinaryOrExpression::Binary(e) => Sub(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Mult(e) => match f.fold_binary_expression(&ty, e)? {
            BinaryOrExpression::Binary(e) => Mult(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Div(e) => match f.fold_binary_expression(&ty, e)? {
            BinaryOrExpression::Binary(e) => Div(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Rem(e) => match f.fold_binary_expression(&ty, e)? {
            BinaryOrExpression::Binary(e) => Rem(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Xor(e) => match f.fold_binary_expression(&ty, e)? {
            BinaryOrExpression::Binary(e) => Xor(e),
            BinaryOrExpression::Expression(u) => u,
        },
        And(e) => match f.fold_binary_expression(&ty, e)? {
            BinaryOrExpression::Binary(e) => And(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Or(e) => match f.fold_binary_expression(&ty, e)? {
            BinaryOrExpression::Binary(e) => Or(e),
            BinaryOrExpression::Expression(u) => u,
        },
        LeftShift(e) => match f.fold_binary_expression(&ty, e)? {
            BinaryOrExpression::Binary(e) => LeftShift(e),
            BinaryOrExpression::Expression(u) => u,
        },
        RightShift(e) => match f.fold_binary_expression(&ty, e)? {
            BinaryOrExpression::Binary(e) => RightShift(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Not(e) => match f.fold_unary_expression(&ty, e)? {
            UnaryOrExpression::Unary(e) => Not(e),
            UnaryOrExpression::Expression(u) => u,
        },
        Conditional(c) => match f.fold_conditional_expression(&ty, c)? {
            ConditionalOrExpression::Conditional(s) => Conditional(s),
            ConditionalOrExpression::Expression(u) => u,
        },
    })
}

pub fn fold_function<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    fun: ZirFunction<'ast, T>,
) -> Result<ZirFunction<'ast, T>, F::Error> {
    Ok(ZirFunction {
        arguments: fun
            .arguments
            .into_iter()
            .map(|a| f.fold_parameter(a))
            .collect::<Result<_, _>>()?,
        statements: fun
            .statements
            .into_iter()
            .map(|s| f.fold_statement(s))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect(),
        ..fun
    })
}

pub fn fold_program<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    p: ZirProgram<'ast, T>,
) -> Result<ZirProgram<'ast, T>, F::Error> {
    Ok(ZirProgram {
        main: f.fold_function(p.main)?,
    })
}

pub fn fold_identifier_expression<
    'ast,
    T: Field,
    E: Expr<'ast, T> + Id<'ast, T>,
    F: ResultFolder<'ast, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: IdentifierExpression<'ast, E>,
) -> Result<IdentifierOrExpression<Identifier<'ast>, E, E::Inner>, F::Error> {
    Ok(IdentifierOrExpression::Identifier(
        IdentifierExpression::new(f.fold_name(e.id)?),
    ))
}

pub fn fold_conditional_expression<
    'ast,
    T: Field,
    E: Expr<'ast, T> + ResultFold<F, F::Error> + Conditional<'ast, T>,
    F: ResultFolder<'ast, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: ConditionalExpression<'ast, T, E>,
) -> Result<ConditionalOrExpression<'ast, T, E>, F::Error> {
    Ok(ConditionalOrExpression::Conditional(
        ConditionalExpression::new(
            f.fold_boolean_expression(*e.condition)?,
            e.consequence.fold(f)?,
            e.alternative.fold(f)?,
        ),
    ))
}

pub fn fold_select_expression<
    'ast,
    T: Field,
    E: Expr<'ast, T> + ResultFold<F, F::Error> + Select<'ast, T>,
    F: ResultFolder<'ast, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: SelectExpression<'ast, T, E>,
) -> Result<SelectOrExpression<'ast, T, E>, F::Error> {
    Ok(SelectOrExpression::Select(SelectExpression::new(
        e.array
            .into_iter()
            .map(|e| e.fold(f))
            .collect::<Result<Vec<_>, _>>()?,
        e.index.fold(f)?,
    )))
}

pub fn fold_binary_expression<
    'ast,
    T: Field,
    L: Expr<'ast, T> + PartialEq + ResultFold<F, F::Error> + From<ZirExpression<'ast, T>>,
    R: Expr<'ast, T> + PartialEq + ResultFold<F, F::Error> + From<ZirExpression<'ast, T>>,
    E: Expr<'ast, T> + PartialEq + ResultFold<F, F::Error> + From<ZirExpression<'ast, T>>,
    F: ResultFolder<'ast, T>,
    Op,
>(
    f: &mut F,
    _: &E::Ty,
    e: BinaryExpression<Op, L, R, E>,
) -> Result<BinaryOrExpression<Op, L, R, E, E::Inner>, F::Error> {
    Ok(BinaryOrExpression::Binary(
        BinaryExpression::new(e.left.fold(f)?, e.right.fold(f)?).span(e.span),
    ))
}

pub fn fold_unary_expression<
    'ast,
    T: Field,
    In: Expr<'ast, T> + PartialEq + ResultFold<F, F::Error> + From<ZirExpression<'ast, T>>,
    E: Expr<'ast, T> + PartialEq + ResultFold<F, F::Error> + From<ZirExpression<'ast, T>>,
    F: ResultFolder<'ast, T>,
    Op,
>(
    f: &mut F,
    _: &E::Ty,
    e: UnaryExpression<Op, In, E>,
) -> Result<UnaryOrExpression<Op, In, E, E::Inner>, F::Error> {
    Ok(UnaryOrExpression::Unary(
        UnaryExpression::new(e.inner.fold(f)?).span(e.span),
    ))
}
