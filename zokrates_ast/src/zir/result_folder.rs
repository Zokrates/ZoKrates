// Generic walk through ZIR. Not mutating in place

use crate::zir::types::UBitwidth;
use crate::zir::*;
use zokrates_field::Field;

pub trait ResultFold<'ast, T: Field>: Sized {
    fn fold<F: ResultFolder<'ast, T>>(self, f: &mut F) -> Result<Self, F::Error>;
}

impl<'ast, T: Field> ResultFold<'ast, T> for FieldElementExpression<'ast, T> {
    fn fold<F: ResultFolder<'ast, T>>(self, f: &mut F) -> Result<Self, F::Error> {
        f.fold_field_expression(self)
    }
}

impl<'ast, T: Field> ResultFold<'ast, T> for BooleanExpression<'ast, T> {
    fn fold<F: ResultFolder<'ast, T>>(self, f: &mut F) -> Result<Self, F::Error> {
        f.fold_boolean_expression(self)
    }
}

impl<'ast, T: Field> ResultFold<'ast, T> for UExpression<'ast, T> {
    fn fold<F: ResultFolder<'ast, T>>(self, f: &mut F) -> Result<Self, F::Error> {
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

    fn fold_conditional_expression<
        E: Expr<'ast, T> + ResultFold<'ast, T> + Conditional<'ast, T>,
    >(
        &mut self,
        ty: &E::Ty,
        e: ConditionalExpression<'ast, T, E>,
    ) -> Result<ConditionalOrExpression<'ast, T, E>, Self::Error> {
        fold_conditional_expression(self, ty, e)
    }

    fn fold_select_expression<E: Clone + Expr<'ast, T> + ResultFold<'ast, T> + Select<'ast, T>>(
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
            FieldElementExpression::Identifier(f.fold_name(id)?)
        }
        FieldElementExpression::Select(e) => {
            match f.fold_select_expression(&Type::FieldElement, e)? {
                SelectOrExpression::Select(s) => FieldElementExpression::Select(s),
                SelectOrExpression::Expression(u) => u,
            }
        }
        FieldElementExpression::Add(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1)?;
            let e2 = f.fold_field_expression(e2)?;
            FieldElementExpression::Add(box e1, box e2)
        }
        FieldElementExpression::Sub(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1)?;
            let e2 = f.fold_field_expression(e2)?;
            FieldElementExpression::Sub(box e1, box e2)
        }
        FieldElementExpression::Mult(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1)?;
            let e2 = f.fold_field_expression(e2)?;
            FieldElementExpression::Mult(box e1, box e2)
        }
        FieldElementExpression::Div(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1)?;
            let e2 = f.fold_field_expression(e2)?;
            FieldElementExpression::Div(box e1, box e2)
        }
        FieldElementExpression::Pow(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1)?;
            let e2 = f.fold_uint_expression(e2)?;
            FieldElementExpression::Pow(box e1, box e2)
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
    Ok(match e {
        BooleanExpression::Value(v) => BooleanExpression::Value(v),
        BooleanExpression::Identifier(id) => BooleanExpression::Identifier(f.fold_name(id)?),
        BooleanExpression::Select(e) => match f.fold_select_expression(&Type::Boolean, e)? {
            SelectOrExpression::Select(s) => BooleanExpression::Select(s),
            SelectOrExpression::Expression(u) => u,
        },
        BooleanExpression::FieldEq(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1)?;
            let e2 = f.fold_field_expression(e2)?;
            BooleanExpression::FieldEq(box e1, box e2)
        }
        BooleanExpression::BoolEq(box e1, box e2) => {
            let e1 = f.fold_boolean_expression(e1)?;
            let e2 = f.fold_boolean_expression(e2)?;
            BooleanExpression::BoolEq(box e1, box e2)
        }
        BooleanExpression::UintEq(box e1, box e2) => {
            let e1 = f.fold_uint_expression(e1)?;
            let e2 = f.fold_uint_expression(e2)?;
            BooleanExpression::UintEq(box e1, box e2)
        }
        BooleanExpression::FieldLt(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1)?;
            let e2 = f.fold_field_expression(e2)?;
            BooleanExpression::FieldLt(box e1, box e2)
        }
        BooleanExpression::UintLt(box e1, box e2) => {
            let e1 = f.fold_uint_expression(e1)?;
            let e2 = f.fold_uint_expression(e2)?;
            BooleanExpression::UintLt(box e1, box e2)
        }
        BooleanExpression::FieldLe(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1)?;
            let e2 = f.fold_field_expression(e2)?;
            BooleanExpression::FieldLe(box e1, box e2)
        }
        BooleanExpression::UintLe(box e1, box e2) => {
            let e1 = f.fold_uint_expression(e1)?;
            let e2 = f.fold_uint_expression(e2)?;
            BooleanExpression::UintLe(box e1, box e2)
        }
        BooleanExpression::Or(box e1, box e2) => {
            let e1 = f.fold_boolean_expression(e1)?;
            let e2 = f.fold_boolean_expression(e2)?;
            BooleanExpression::Or(box e1, box e2)
        }
        BooleanExpression::And(box e1, box e2) => {
            let e1 = f.fold_boolean_expression(e1)?;
            let e2 = f.fold_boolean_expression(e2)?;
            BooleanExpression::And(box e1, box e2)
        }
        BooleanExpression::Not(box e) => {
            let e = f.fold_boolean_expression(e)?;
            BooleanExpression::Not(box e)
        }
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
    Ok(match e {
        UExpressionInner::Value(v) => UExpressionInner::Value(v),
        UExpressionInner::Identifier(id) => UExpressionInner::Identifier(f.fold_name(id)?),
        UExpressionInner::Select(e) => match f.fold_select_expression(&ty, e)? {
            SelectOrExpression::Select(s) => UExpressionInner::Select(s),
            SelectOrExpression::Expression(u) => u,
        },
        UExpressionInner::Add(box left, box right) => {
            let left = f.fold_uint_expression(left)?;
            let right = f.fold_uint_expression(right)?;

            UExpressionInner::Add(box left, box right)
        }
        UExpressionInner::Sub(box left, box right) => {
            let left = f.fold_uint_expression(left)?;
            let right = f.fold_uint_expression(right)?;

            UExpressionInner::Sub(box left, box right)
        }
        UExpressionInner::Mult(box left, box right) => {
            let left = f.fold_uint_expression(left)?;
            let right = f.fold_uint_expression(right)?;

            UExpressionInner::Mult(box left, box right)
        }
        UExpressionInner::Div(box left, box right) => {
            let left = f.fold_uint_expression(left)?;
            let right = f.fold_uint_expression(right)?;

            UExpressionInner::Div(box left, box right)
        }
        UExpressionInner::Rem(box left, box right) => {
            let left = f.fold_uint_expression(left)?;
            let right = f.fold_uint_expression(right)?;

            UExpressionInner::Rem(box left, box right)
        }
        UExpressionInner::Xor(box left, box right) => {
            let left = f.fold_uint_expression(left)?;
            let right = f.fold_uint_expression(right)?;

            UExpressionInner::Xor(box left, box right)
        }
        UExpressionInner::And(box left, box right) => {
            let left = f.fold_uint_expression(left)?;
            let right = f.fold_uint_expression(right)?;

            UExpressionInner::And(box left, box right)
        }
        UExpressionInner::Or(box left, box right) => {
            let left = f.fold_uint_expression(left)?;
            let right = f.fold_uint_expression(right)?;

            UExpressionInner::Or(box left, box right)
        }
        UExpressionInner::LeftShift(box e, by) => {
            let e = f.fold_uint_expression(e)?;

            UExpressionInner::LeftShift(box e, by)
        }
        UExpressionInner::RightShift(box e, by) => {
            let e = f.fold_uint_expression(e)?;

            UExpressionInner::RightShift(box e, by)
        }
        UExpressionInner::Not(box e) => {
            let e = f.fold_uint_expression(e)?;

            UExpressionInner::Not(box e)
        }
        UExpressionInner::Conditional(c) => match f.fold_conditional_expression(&ty, c)? {
            ConditionalOrExpression::Conditional(s) => UExpressionInner::Conditional(s),
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

pub fn fold_conditional_expression<
    'ast,
    T: Field,
    E: Expr<'ast, T> + ResultFold<'ast, T> + Conditional<'ast, T>,
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
    E: Expr<'ast, T> + ResultFold<'ast, T> + Select<'ast, T>,
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
