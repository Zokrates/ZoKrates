use std::collections::HashMap;
use std::fmt;
use std::ops::*;
use zokrates_ast::common::{ResultFold, WithSpan};
use zokrates_ast::zir::types::UBitwidth;
use zokrates_ast::zir::{
    result_folder::*, Conditional, ConditionalExpression, ConditionalOrExpression, Expr, Id,
    IdentifierExpression, IdentifierOrExpression, SelectExpression, SelectOrExpression,
};
use zokrates_ast::zir::{
    BooleanExpression, FieldElementExpression, Identifier, RuntimeError, UExpression,
    UExpressionInner, ZirExpression, ZirProgram, ZirStatement,
};
use zokrates_field::Field;

type Constants<'ast, T> = HashMap<Identifier<'ast>, ZirExpression<'ast, T>>;

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    OutOfBounds(usize, usize),
    DivisionByZero,
    AssertionFailed(RuntimeError),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::OutOfBounds(index, size) => write!(
                f,
                "Out of bounds index ({} >= {}) found in zir during static analysis",
                index, size
            ),
            Error::DivisionByZero => {
                write!(f, "Division by zero detected in zir during static analysis",)
            }
            Error::AssertionFailed(err) => write!(f, "{}", err),
        }
    }
}

#[derive(Default)]
pub struct ZirPropagator<'ast, T> {
    constants: Constants<'ast, T>,
}

impl<'ast, T: Field> ZirPropagator<'ast, T> {
    pub fn propagate(p: ZirProgram<T>) -> Result<ZirProgram<T>, Error> {
        ZirPropagator::default().fold_program(p)
    }
}

impl<'ast, T: Field> ResultFolder<'ast, T> for ZirPropagator<'ast, T> {
    type Error = Error;

    fn fold_statement(
        &mut self,
        s: ZirStatement<'ast, T>,
    ) -> Result<Vec<ZirStatement<'ast, T>>, Self::Error> {
        match s {
            ZirStatement::Assertion(s) => match self.fold_boolean_expression(s.expression)? {
                BooleanExpression::Value(v) if v.value => Ok(vec![]),
                BooleanExpression::Value(v) if !v.value => Err(Error::AssertionFailed(s.error)),
                e => Ok(vec![ZirStatement::assertion(e, s.error)]),
            },
            ZirStatement::Definition(s) => {
                let e = self.fold_expression(s.rhs)?;
                match e {
                    ZirExpression::FieldElement(FieldElementExpression::Number(..))
                    | ZirExpression::Boolean(BooleanExpression::Value(..))
                    | ZirExpression::Uint(UExpression {
                        inner: UExpressionInner::Value(..),
                        ..
                    }) => {
                        self.constants.insert(s.assignee.id, e);
                        Ok(vec![])
                    }
                    _ => {
                        self.constants.remove(&s.assignee.id);
                        Ok(vec![ZirStatement::definition(s.assignee, e)])
                    }
                }
            }
            ZirStatement::IfElse(e, consequence, alternative) => {
                match self.fold_boolean_expression(e)? {
                    BooleanExpression::Value(v) if v.value => Ok(consequence
                        .into_iter()
                        .map(|s| self.fold_statement(s))
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .flatten()
                        .collect()),
                    BooleanExpression::Value(v) if !v.value => Ok(alternative
                        .into_iter()
                        .map(|s| self.fold_statement(s))
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .flatten()
                        .collect()),
                    e => Ok(vec![ZirStatement::IfElse(
                        e,
                        consequence
                            .into_iter()
                            .map(|s| self.fold_statement(s))
                            .collect::<Result<Vec<_>, _>>()?
                            .into_iter()
                            .flatten()
                            .collect(),
                        alternative
                            .into_iter()
                            .map(|s| self.fold_statement(s))
                            .collect::<Result<Vec<_>, _>>()?
                            .into_iter()
                            .flatten()
                            .collect(),
                    )]),
                }
            }
            ZirStatement::MultipleDefinition(assignees, list) => {
                for a in &assignees {
                    self.constants.remove(&a.id);
                }
                Ok(vec![ZirStatement::MultipleDefinition(
                    assignees,
                    self.fold_expression_list(list)?,
                )])
            }
            _ => fold_statement(self, s),
        }
    }

    fn fold_identifier_expression<
        E: Expr<'ast, T> + Id<'ast, T> + ResultFold<Self, Self::Error>,
    >(
        &mut self,
        _: &E::Ty,
        id: IdentifierExpression<'ast, E>,
    ) -> Result<IdentifierOrExpression<'ast, T, E>, Self::Error> {
        match self.constants.get(&id.id).cloned() {
            Some(e) => Ok(IdentifierOrExpression::Expression(E::from(e).into_inner())),
            None => Ok(IdentifierOrExpression::Identifier(id)),
        }
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> Result<FieldElementExpression<'ast, T>, Self::Error> {
        match e {
            FieldElementExpression::Number(n) => Ok(FieldElementExpression::Number(n)),
            FieldElementExpression::Add(e) => {
                let left = self.fold_field_expression(*e.left)?;
                let right = self.fold_field_expression(*e.right)?;

                Ok(match (left, right) {
                    (FieldElementExpression::Number(n), e)
                    | (e, FieldElementExpression::Number(n))
                        if n.value == T::from(0) =>
                    {
                        e
                    }
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        FieldElementExpression::number(n1.value + n2.value)
                    }
                    (e1, e2) => FieldElementExpression::add(e1, e2),
                }
                .span(e.span))
            }
            FieldElementExpression::Sub(e) => {
                let left = self.fold_field_expression(*e.left)?;
                let right = self.fold_field_expression(*e.right)?;

                Ok(match (left, right) {
                    (FieldElementExpression::Number(n), e)
                    | (e, FieldElementExpression::Number(n))
                        if n.value == T::from(0) =>
                    {
                        e
                    }
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        FieldElementExpression::number(n1.value - n2.value)
                    }
                    (e1, e2) => FieldElementExpression::sub(e1, e2),
                }
                .span(e.span))
            }
            FieldElementExpression::Mult(e) => {
                let left = self.fold_field_expression(*e.left)?;
                let right = self.fold_field_expression(*e.right)?;

                Ok(match (left, right) {
                    (FieldElementExpression::Number(n), _)
                    | (_, FieldElementExpression::Number(n))
                        if n.value == T::from(0) =>
                    {
                        FieldElementExpression::number(T::from(0))
                    }
                    (FieldElementExpression::Number(n), e)
                    | (e, FieldElementExpression::Number(n))
                        if n.value == T::from(1) =>
                    {
                        e
                    }
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        FieldElementExpression::number(n1.value * n2.value)
                    }
                    (e1, e2) => FieldElementExpression::mul(e1, e2),
                }
                .span(e.span))
            }
            FieldElementExpression::Div(e) => {
                let left = self.fold_field_expression(*e.left)?;
                let right = self.fold_field_expression(*e.right)?;

                match (left, right) {
                    (_, FieldElementExpression::Number(n)) if n.value == T::from(0) => {
                        Err(Error::DivisionByZero)
                    }
                    (e, FieldElementExpression::Number(n)) if n.value == T::from(1) => Ok(e),
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        Ok(FieldElementExpression::number(n1.value / n2.value).span(e.span))
                    }
                    (e1, e2) => Ok(FieldElementExpression::div(e1, e2).span(e.span)),
                }
            }
            FieldElementExpression::Pow(e) => {
                let exponent = self.fold_uint_expression(*e.right)?;
                match (self.fold_field_expression(*e.left)?, exponent.into_inner()) {
                    (_, UExpressionInner::Value(n2)) if n2.value == 0 => {
                        Ok(FieldElementExpression::number(T::from(1)))
                    }
                    (e, UExpressionInner::Value(n2)) if n2.value == 1 => Ok(e),
                    (FieldElementExpression::Number(n), UExpressionInner::Value(e)) => Ok(
                        FieldElementExpression::number(n.value.pow(e.value as usize)),
                    ),
                    (e, exp) => {
                        Ok(FieldElementExpression::pow(e, exp.annotate(UBitwidth::B32))
                            .into_inner())
                    }
                }
            }
            e => fold_field_expression(self, e),
        }
    }

    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> Result<BooleanExpression<'ast, T>, Error> {
        match e {
            BooleanExpression::Value(v) => Ok(BooleanExpression::Value(v)),
            BooleanExpression::FieldLt(e) => {
                match (
                    self.fold_field_expression(*e.left)?,
                    self.fold_field_expression(*e.right)?,
                ) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        Ok(BooleanExpression::from_value(n1 < n2))
                    }
                    (_, FieldElementExpression::Number(c)) if c.value == T::zero() => {
                        Ok(BooleanExpression::from_value(false))
                    }
                    (FieldElementExpression::Number(c), _) if c.value == T::max_value() => {
                        Ok(BooleanExpression::from_value(false))
                    }
                    (e1, e2) => Ok(BooleanExpression::field_lt(e1, e2)),
                }
            }
            BooleanExpression::FieldLe(e) => {
                match (
                    self.fold_field_expression(*e.left)?,
                    self.fold_field_expression(*e.right)?,
                ) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        Ok(BooleanExpression::from_value(n1 <= n2))
                    }
                    (e1, e2) => Ok(BooleanExpression::field_le(e1, e2)),
                }
            }
            BooleanExpression::FieldEq(e) => {
                match (
                    self.fold_field_expression(*e.left)?,
                    self.fold_field_expression(*e.right)?,
                ) {
                    (FieldElementExpression::Number(v1), FieldElementExpression::Number(v2)) => {
                        Ok(BooleanExpression::from_value(v1.eq(&v2)))
                    }
                    (e1, e2) => {
                        if e1.eq(&e2) {
                            Ok(BooleanExpression::from_value(true))
                        } else {
                            Ok(BooleanExpression::field_eq(e1, e2))
                        }
                    }
                }
            }
            BooleanExpression::UintLt(e) => {
                let e1 = self.fold_uint_expression(*e.left)?;
                let e2 = self.fold_uint_expression(*e.right)?;

                match (e1.as_inner(), e2.as_inner()) {
                    (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                        Ok(BooleanExpression::from_value(v1 < v2))
                    }
                    _ => Ok(BooleanExpression::uint_lt(e1, e2)),
                }
            }
            BooleanExpression::UintLe(e) => {
                let e1 = self.fold_uint_expression(*e.left)?;
                let e2 = self.fold_uint_expression(*e.right)?;

                match (e1.as_inner(), e2.as_inner()) {
                    (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                        Ok(BooleanExpression::from_value(v1 <= v2))
                    }
                    _ => Ok(BooleanExpression::uint_le(e1, e2)),
                }
            }
            BooleanExpression::UintEq(e) => {
                let e1 = self.fold_uint_expression(*e.left)?;
                let e2 = self.fold_uint_expression(*e.right)?;

                match (e1.as_inner(), e2.as_inner()) {
                    (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                        Ok(BooleanExpression::from_value(v1 == v2))
                    }
                    _ => {
                        if e1.eq(&e2) {
                            Ok(BooleanExpression::from_value(true))
                        } else {
                            Ok(BooleanExpression::uint_eq(e1, e2))
                        }
                    }
                }
            }
            BooleanExpression::BoolEq(e) => {
                match (
                    self.fold_boolean_expression(*e.left)?,
                    self.fold_boolean_expression(*e.right)?,
                ) {
                    (BooleanExpression::Value(v1), BooleanExpression::Value(v2)) => {
                        Ok(BooleanExpression::from_value(v1 == v2))
                    }
                    (e1, e2) => {
                        if e1.eq(&e2) {
                            Ok(BooleanExpression::from_value(true))
                        } else {
                            Ok(BooleanExpression::bool_eq(e1, e2))
                        }
                    }
                }
            }
            BooleanExpression::Or(e) => {
                match (
                    self.fold_boolean_expression(*e.left)?,
                    self.fold_boolean_expression(*e.right)?,
                ) {
                    (BooleanExpression::Value(v1), BooleanExpression::Value(v2)) => {
                        Ok(BooleanExpression::from_value(v1.value || v2.value))
                    }
                    (_, BooleanExpression::Value(v)) | (BooleanExpression::Value(v), _)
                        if v.value =>
                    {
                        Ok(BooleanExpression::from_value(true))
                    }
                    (e, BooleanExpression::Value(v)) | (BooleanExpression::Value(v), e)
                        if !v.value =>
                    {
                        Ok(e)
                    }
                    (e1, e2) => Ok(BooleanExpression::or(e1, e2)),
                }
            }
            BooleanExpression::And(e) => {
                match (
                    self.fold_boolean_expression(*e.left)?,
                    self.fold_boolean_expression(*e.right)?,
                ) {
                    (BooleanExpression::Value(v), e) | (e, BooleanExpression::Value(v))
                        if v.value =>
                    {
                        Ok(e)
                    }
                    (BooleanExpression::Value(v), _) | (_, BooleanExpression::Value(v))
                        if !v.value =>
                    {
                        Ok(BooleanExpression::from_value(false))
                    }
                    (e1, e2) => Ok(BooleanExpression::and(e1, e2)),
                }
            }
            BooleanExpression::Not(e) => match self.fold_boolean_expression(*e.inner)? {
                BooleanExpression::Value(v) => Ok(BooleanExpression::from_value(!v.value)),
                e => Ok(BooleanExpression::not(e)),
            },
            e => fold_boolean_expression(self, e),
        }
    }

    fn fold_select_expression<
        E: Clone + Expr<'ast, T> + ResultFold<Self, Self::Error> + zokrates_ast::zir::Select<'ast, T>,
    >(
        &mut self,
        _: &E::Ty,
        e: SelectExpression<'ast, T, E>,
    ) -> Result<zokrates_ast::zir::SelectOrExpression<'ast, T, E>, Self::Error> {
        let index = self.fold_uint_expression(*e.index)?;
        let array = e
            .array
            .into_iter()
            .map(|e| e.fold(self))
            .collect::<Result<Vec<_>, _>>()?;

        match index.as_inner() {
            UExpressionInner::Value(v) => array
                .get(v.value as usize)
                .cloned()
                .ok_or(Error::OutOfBounds(v.value as usize, array.len()))
                .map(|e| SelectOrExpression::Expression(e.into_inner())),
            _ => Ok(SelectOrExpression::Expression(
                E::select(array, index).into_inner(),
            )),
        }
    }

    fn fold_uint_expression_inner(
        &mut self,
        bitwidth: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> Result<UExpressionInner<'ast, T>, Self::Error> {
        match e {
            UExpressionInner::Value(v) => Ok(UExpressionInner::Value(v)),
            UExpressionInner::Add(e) => {
                let e1 = self.fold_uint_expression(*e.left)?;
                let e2 = self.fold_uint_expression(*e.right)?;

                match (e1.into_inner(), e2.into_inner()) {
                    (UExpressionInner::Value(v), e) | (e, UExpressionInner::Value(v))
                        if v.value == 0 =>
                    {
                        Ok(e)
                    }
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        Ok(UExpression::from_value(
                            (n1.value + n2.value) % 2_u128.pow(bitwidth.to_usize() as u32),
                        ))
                    }
                    (e1, e2) => Ok(
                        UExpression::add(e1.annotate(bitwidth), e2.annotate(bitwidth)).into_inner(),
                    ),
                }
            }
            UExpressionInner::Sub(e) => {
                let e1 = self.fold_uint_expression(*e.left)?;
                let e2 = self.fold_uint_expression(*e.right)?;

                match (e1.into_inner(), e2.into_inner()) {
                    (e, UExpressionInner::Value(v)) if v.value == 0 => Ok(e),
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        Ok(UExpression::from_value(
                            n1.value.wrapping_sub(n2.value)
                                % 2_u128.pow(bitwidth.to_usize() as u32),
                        ))
                    }
                    (e1, e2) => Ok(
                        UExpression::sub(e1.annotate(bitwidth), e2.annotate(bitwidth)).into_inner(),
                    ),
                }
            }
            UExpressionInner::Mult(e) => {
                let e1 = self.fold_uint_expression(*e.left)?;
                let e2 = self.fold_uint_expression(*e.right)?;

                match (e1.into_inner(), e2.into_inner()) {
                    (_, UExpressionInner::Value(v)) | (UExpressionInner::Value(v), _)
                        if v.value == 0 =>
                    {
                        Ok(UExpression::from_value(0))
                    }
                    (e, UExpressionInner::Value(v)) | (UExpressionInner::Value(v), e)
                        if v.value == 1 =>
                    {
                        Ok(e)
                    }
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        Ok(UExpression::from_value(
                            (n1.value * n2.value) % 2_u128.pow(bitwidth.to_usize() as u32),
                        ))
                    }
                    (e1, e2) => Ok(
                        UExpression::mult(e1.annotate(bitwidth), e2.annotate(bitwidth))
                            .into_inner(),
                    ),
                }
            }
            UExpressionInner::Div(e) => {
                let e1 = self.fold_uint_expression(*e.left)?;
                let e2 = self.fold_uint_expression(*e.right)?;

                match (e1.into_inner(), e2.into_inner()) {
                    (_, UExpressionInner::Value(n)) if n.value == 0 => Err(Error::DivisionByZero),
                    (e, UExpressionInner::Value(n)) if n.value == 1 => Ok(e),
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        Ok(UExpression::from_value(
                            (n1.value / n2.value) % 2_u128.pow(bitwidth.to_usize() as u32),
                        ))
                    }
                    (e1, e2) => Ok(
                        UExpression::div(e1.annotate(bitwidth), e2.annotate(bitwidth)).into_inner(),
                    ),
                }
            }
            UExpressionInner::Rem(e) => {
                let e1 = self.fold_uint_expression(*e.left)?;
                let e2 = self.fold_uint_expression(*e.right)?;

                match (e1.into_inner(), e2.into_inner()) {
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        Ok(UExpression::from_value(
                            (n1.value % n2.value) % 2_u128.pow(bitwidth.to_usize() as u32),
                        ))
                    }
                    (e1, e2) => Ok(
                        UExpression::rem(e1.annotate(bitwidth), e2.annotate(bitwidth)).into_inner(),
                    ),
                }
            }
            UExpressionInner::Xor(e) => {
                let e1 = self.fold_uint_expression(*e.left)?;
                let e2 = self.fold_uint_expression(*e.right)?;

                match (e1.into_inner(), e2.into_inner()) {
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        Ok(UExpression::from_value(n1.value ^ n2.value))
                    }
                    (e1, e2) if e1.eq(&e2) => Ok(UExpression::from_value(0)),
                    (e1, e2) => Ok(
                        UExpression::xor(e1.annotate(bitwidth), e2.annotate(bitwidth)).into_inner(),
                    ),
                }
            }
            UExpressionInner::And(e) => {
                let e1 = self.fold_uint_expression(*e.left)?;
                let e2 = self.fold_uint_expression(*e.right)?;

                match (e1.into_inner(), e2.into_inner()) {
                    (e, UExpressionInner::Value(n)) | (UExpressionInner::Value(n), e)
                        if n.value == 2_u128.pow(bitwidth.to_usize() as u32) - 1 =>
                    {
                        Ok(e)
                    }
                    (_, UExpressionInner::Value(v)) | (UExpressionInner::Value(v), _)
                        if v.value == 0 =>
                    {
                        Ok(UExpression::from_value(0))
                    }
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        Ok(UExpression::from_value(n1.value & n2.value))
                    }
                    (e1, e2) => Ok(
                        UExpression::and(e1.annotate(bitwidth), e2.annotate(bitwidth)).into_inner(),
                    ),
                }
            }
            UExpressionInner::Or(e) => {
                let e1 = self.fold_uint_expression(*e.left)?;
                let e2 = self.fold_uint_expression(*e.right)?;

                match (e1.into_inner(), e2.into_inner()) {
                    (e, UExpressionInner::Value(v)) | (UExpressionInner::Value(v), e)
                        if v.value == 0 =>
                    {
                        Ok(e)
                    }
                    (_, UExpressionInner::Value(n)) | (UExpressionInner::Value(n), _)
                        if n.value == 2_u128.pow(bitwidth.to_usize() as u32) - 1 =>
                    {
                        Ok(UExpression::from_value(n.value))
                    }
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        Ok(UExpression::from_value(n1.value | n2.value))
                    }
                    (e1, e2) => Ok(
                        UExpression::or(e1.annotate(bitwidth), e2.annotate(bitwidth)).into_inner(),
                    ),
                }
            }
            UExpressionInner::LeftShift(e) => {
                let left = self.fold_uint_expression(*e.left)?;
                let right = self.fold_uint_expression(*e.right)?;
                match (left.into_inner(), right.into_inner()) {
                    (e, UExpressionInner::Value(by)) if by.value == 0 => Ok(e),
                    (_, UExpressionInner::Value(by)) if by.value as u32 >= bitwidth as u32 => {
                        Ok(UExpression::from_value(0))
                    }
                    (UExpressionInner::Value(n), UExpressionInner::Value(by)) => {
                        Ok(UExpression::from_value(
                            (n.value << by.value) & (2_u128.pow(bitwidth as u32) - 1),
                        ))
                    }
                    (e, by) => Ok(UExpression::left_shift(
                        e.annotate(bitwidth),
                        by.annotate(UBitwidth::B32),
                    )
                    .into_inner()),
                }
            }
            UExpressionInner::RightShift(e) => {
                let left = self.fold_uint_expression(*e.left)?;
                let right = self.fold_uint_expression(*e.right)?;
                match (left.into_inner(), right.into_inner()) {
                    (e, UExpressionInner::Value(by)) if by.value == 0 => Ok(e),
                    (_, UExpressionInner::Value(by)) if by.value as u32 >= bitwidth as u32 => {
                        Ok(UExpression::from_value(0))
                    }
                    (UExpressionInner::Value(n), UExpressionInner::Value(by)) => {
                        Ok(UExpression::from_value(n.value >> by.value))
                    }
                    (e, by) => Ok(UExpression::right_shift(
                        e.annotate(bitwidth),
                        by.annotate(UBitwidth::B32),
                    )
                    .into_inner()),
                }
            }
            UExpressionInner::Not(e) => {
                let e = self.fold_uint_expression(*e.inner)?;
                match e.into_inner() {
                    UExpressionInner::Value(n) => Ok(UExpression::from_value(
                        !n.value & (2_u128.pow(bitwidth as u32) - 1),
                    )),
                    e => Ok(UExpression::not(e.annotate(bitwidth)).into_inner()),
                }
            }
            e => fold_uint_expression_inner(self, bitwidth, e),
        }
    }

    fn fold_conditional_expression<
        E: Expr<'ast, T> + ResultFold<Self, Self::Error> + Conditional<'ast, T>,
    >(
        &mut self,
        _: &E::Ty,
        e: ConditionalExpression<'ast, T, E>,
    ) -> Result<ConditionalOrExpression<'ast, T, E>, Self::Error> {
        let condition = self.fold_boolean_expression(*e.condition)?;
        let consequence = e.consequence.fold(self)?;
        let alternative = e.alternative.fold(self)?;

        match (condition, consequence, alternative) {
            (_, consequence, alternative) if consequence == alternative => Ok(
                ConditionalOrExpression::Expression(consequence.into_inner()),
            ),
            (BooleanExpression::Value(v), consequence, _) if v.value => Ok(
                ConditionalOrExpression::Expression(consequence.into_inner()),
            ),
            (BooleanExpression::Value(v), _, alternative) if !v.value => Ok(
                ConditionalOrExpression::Expression(alternative.into_inner()),
            ),
            (condition, consequence, alternative) => Ok(ConditionalOrExpression::Conditional(
                ConditionalExpression::new(condition, consequence, alternative),
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_ast::zir::{Id, RuntimeError};
    use zokrates_field::Bn128Field;

    #[test]
    fn propagation() {
        // assert([x, 1] == [y, 1])
        let statements = vec![ZirStatement::Assertion(
            BooleanExpression::And(
                box BooleanExpression::FieldEq(
                    box FieldElementExpression::identifier("x".into()),
                    box FieldElementExpression::identifier("y".into()),
                ),
                box BooleanExpression::FieldEq(
                    box FieldElementExpression::Number(Bn128Field::from(1)),
                    box FieldElementExpression::Number(Bn128Field::from(1)),
                ),
            ),
            RuntimeError::mock(),
        )];

        let mut propagator = ZirPropagator::default();
        let statements: Vec<ZirStatement<_>> = statements
            .into_iter()
            .map(|s| propagator.fold_statement(s))
            .collect::<Result<Vec<_>, _>>()
            .unwrap()
            .into_iter()
            .flatten()
            .collect();

        assert_eq!(
            statements,
            vec![ZirStatement::Assertion(
                BooleanExpression::FieldEq(
                    box FieldElementExpression::identifier("x".into()),
                    box FieldElementExpression::identifier("y".into()),
                ),
                RuntimeError::mock()
            )]
        );
    }

    #[cfg(test)]
    mod field {
        use zokrates_ast::zir::Conditional;
        use zokrates_ast::zir::Select;

        use super::*;

        #[test]
        fn select() {
            let mut propagator = ZirPropagator::default();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::select(
                    vec![
                        FieldElementExpression::Number(Bn128Field::from(1)),
                        FieldElementExpression::Number(Bn128Field::from(2)),
                    ],
                    UExpressionInner::Value(1).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(2)))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::select(
                    vec![
                        FieldElementExpression::Number(Bn128Field::from(1)),
                        FieldElementExpression::Number(Bn128Field::from(2)),
                    ],
                    UExpressionInner::Value(3).annotate(UBitwidth::B32),
                )),
                Err(Error::OutOfBounds(3, 2))
            );
        }

        #[test]
        fn add() {
            let mut propagator = ZirPropagator::default();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Add(
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(5)))
            );

            // a + 0 = a
            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Add(
                    box FieldElementExpression::identifier("a".into()),
                    box FieldElementExpression::Number(Bn128Field::from(0)),
                )),
                Ok(FieldElementExpression::identifier("a".into()))
            );
        }

        #[test]
        fn sub() {
            let mut propagator = ZirPropagator::default();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Sub(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(1)))
            );

            // a - 0 = a
            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Sub(
                    box FieldElementExpression::identifier("a".into()),
                    box FieldElementExpression::Number(Bn128Field::from(0)),
                )),
                Ok(FieldElementExpression::identifier("a".into()))
            );
        }

        #[test]
        fn mult() {
            let mut propagator = ZirPropagator::default();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Mult(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(6)))
            );

            // a * 0 = 0
            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Mult(
                    box FieldElementExpression::identifier("a".into()),
                    box FieldElementExpression::Number(Bn128Field::from(0)),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(0)))
            );

            // a * 1 = a
            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Mult(
                    box FieldElementExpression::identifier("a".into()),
                    box FieldElementExpression::Number(Bn128Field::from(1)),
                )),
                Ok(FieldElementExpression::identifier("a".into()))
            );
        }

        #[test]
        fn div() {
            let mut propagator = ZirPropagator::default();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Div(
                    box FieldElementExpression::Number(Bn128Field::from(6)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(3)))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Div(
                    box FieldElementExpression::identifier("a".into()),
                    box FieldElementExpression::Number(Bn128Field::from(1)),
                )),
                Ok(FieldElementExpression::identifier("a".into()))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Div(
                    box FieldElementExpression::identifier("a".into()),
                    box FieldElementExpression::Number(Bn128Field::from(0)),
                )),
                Err(Error::DivisionByZero)
            );
        }

        #[test]
        fn pow() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Pow(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(9)))
            );

            // a ** 0 = 1
            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Pow(
                    box FieldElementExpression::identifier("a".into()),
                    box UExpressionInner::Value(0).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(1)))
            );

            // a ** 1 = a
            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Pow(
                    box FieldElementExpression::identifier("a".into()),
                    box UExpressionInner::Value(1).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::identifier("a".into()))
            );
        }

        #[test]
        fn if_else() {
            let mut propagator = ZirPropagator::default();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::conditional(
                    BooleanExpression::Value(true),
                    FieldElementExpression::Number(Bn128Field::from(1)),
                    FieldElementExpression::Number(Bn128Field::from(2)),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(1)))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::conditional(
                    BooleanExpression::Value(false),
                    FieldElementExpression::Number(Bn128Field::from(1)),
                    FieldElementExpression::Number(Bn128Field::from(2)),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(2)))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::conditional(
                    BooleanExpression::identifier("a".into()),
                    FieldElementExpression::Number(Bn128Field::from(2)),
                    FieldElementExpression::Number(Bn128Field::from(2)),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(2)))
            );
        }
    }

    #[cfg(test)]
    mod bool {
        use zokrates_ast::zir::Conditional;
        use zokrates_ast::zir::Select;

        use super::*;

        #[test]
        fn select() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::select(
                    vec![
                        BooleanExpression::Value(false),
                        BooleanExpression::Value(true),
                    ],
                    UExpressionInner::Value(1).annotate(UBitwidth::B32),
                )),
                Ok(BooleanExpression::from_value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::select(
                    vec![
                        BooleanExpression::Value(false),
                        BooleanExpression::Value(true),
                    ],
                    UExpressionInner::Value(3).annotate(UBitwidth::B32),
                )),
                Err(Error::OutOfBounds(3, 2))
            );
        }

        #[test]
        fn field_lt() {
            let mut propagator = ZirPropagator::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldLt(
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                )),
                Ok(BooleanExpression::from_value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldLt(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                )),
                Ok(BooleanExpression::from_value(false))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldLt(
                    box FieldElementExpression::identifier("a".into()),
                    box FieldElementExpression::Number(Bn128Field::from(0)),
                )),
                Ok(BooleanExpression::from_value(false))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldLt(
                    box FieldElementExpression::Number(Bn128Field::max_value()),
                    box FieldElementExpression::identifier("a".into()),
                )),
                Ok(BooleanExpression::from_value(false))
            );
        }

        #[test]
        fn field_le() {
            let mut propagator = ZirPropagator::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldLe(
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                )),
                Ok(BooleanExpression::from_value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldLe(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                )),
                Ok(BooleanExpression::from_value(true))
            );
        }

        #[test]
        fn field_eq() {
            let mut propagator = ZirPropagator::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldEq(
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                )),
                Ok(BooleanExpression::from_value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldEq(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                )),
                Ok(BooleanExpression::from_value(false))
            );
        }

        #[test]
        fn uint_lt() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::UintLt(
                    box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                )),
                Ok(BooleanExpression::from_value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::UintLt(
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                )),
                Ok(BooleanExpression::from_value(false))
            );
        }

        #[test]
        fn uint_le() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::UintLe(
                    box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                )),
                Ok(BooleanExpression::from_value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::UintLe(
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                )),
                Ok(BooleanExpression::from_value(true))
            );
        }

        #[test]
        fn uint_eq() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::UintEq(
                    box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                )),
                Ok(BooleanExpression::from_value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::UintEq(
                    box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                )),
                Ok(BooleanExpression::from_value(false))
            );
        }

        #[test]
        fn bool_eq() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::BoolEq(
                    box BooleanExpression::Value(true),
                    box BooleanExpression::Value(true),
                )),
                Ok(BooleanExpression::from_value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::BoolEq(
                    box BooleanExpression::Value(true),
                    box BooleanExpression::Value(false),
                )),
                Ok(BooleanExpression::from_value(false))
            );
        }

        #[test]
        fn and() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::And(
                    box BooleanExpression::Value(true),
                    box BooleanExpression::Value(true),
                )),
                Ok(BooleanExpression::from_value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::And(
                    box BooleanExpression::Value(true),
                    box BooleanExpression::Value(false),
                )),
                Ok(BooleanExpression::from_value(false))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::And(
                    box BooleanExpression::identifier("a".into()),
                    box BooleanExpression::Value(true),
                )),
                Ok(BooleanExpression::identifier("a".into()))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::And(
                    box BooleanExpression::identifier("a".into()),
                    box BooleanExpression::Value(false),
                )),
                Ok(BooleanExpression::from_value(false))
            );
        }

        #[test]
        fn or() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::Or(
                    box BooleanExpression::Value(true),
                    box BooleanExpression::Value(true),
                )),
                Ok(BooleanExpression::from_value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::Or(
                    box BooleanExpression::Value(true),
                    box BooleanExpression::Value(false),
                )),
                Ok(BooleanExpression::from_value(true))
            );
        }

        #[test]
        fn not() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::Not(
                    box BooleanExpression::Value(true),
                )),
                Ok(BooleanExpression::from_value(false))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::Not(
                    box BooleanExpression::Value(false),
                )),
                Ok(BooleanExpression::from_value(true))
            );
        }

        #[test]
        fn if_else() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::conditional(
                    BooleanExpression::Value(true),
                    BooleanExpression::Value(true),
                    BooleanExpression::Value(false)
                )),
                Ok(BooleanExpression::from_value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::conditional(
                    BooleanExpression::Value(false),
                    BooleanExpression::Value(true),
                    BooleanExpression::Value(false)
                )),
                Ok(BooleanExpression::from_value(false))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::conditional(
                    BooleanExpression::identifier("a".into()),
                    BooleanExpression::Value(true),
                    BooleanExpression::Value(true)
                )),
                Ok(BooleanExpression::from_value(true))
            );
        }
    }

    #[cfg(test)]
    mod uint {
        use zokrates_ast::zir::Conditional;

        use super::*;

        #[test]
        fn select() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::select(
                        vec![
                            UExpressionInner::Value(1).annotate(UBitwidth::B32),
                            UExpressionInner::Value(2).annotate(UBitwidth::B32),
                        ],
                        UExpressionInner::Value(1).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpressionInner::Value(2))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::select(
                        vec![
                            UExpressionInner::Value(1).annotate(UBitwidth::B32),
                            UExpressionInner::Value(2).annotate(UBitwidth::B32),
                        ],
                        UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Err(Error::OutOfBounds(3, 2))
            );
        }

        #[test]
        fn add() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Add(
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Value(5))
            );

            // a + 0 = a
            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Add(
                        box UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(0).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpression::identifier("a".into()))
            );
        }

        #[test]
        fn sub() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Sub(
                        box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Value(1))
            );

            // a - 0 = a
            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Sub(
                        box UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(0).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpression::identifier("a".into()))
            );
        }

        #[test]
        fn mult() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Mult(
                        box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Value(6))
            );

            // a * 1 = a
            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Mult(
                        box UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(1).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpression::identifier("a".into()))
            );

            // a * 0 = 0
            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Mult(
                        box UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(0).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Value(0))
            );
        }

        #[test]
        fn div() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Div(
                        box UExpressionInner::Value(6).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Value(3))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Div(
                        box UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(1).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpression::identifier("a".into()))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Div(
                        box UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(0).annotate(UBitwidth::B32),
                    )
                ),
                Err(Error::DivisionByZero)
            );
        }

        #[test]
        fn rem() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Rem(
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Value(2))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Rem(
                        box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Value(1))
            );
        }

        #[test]
        fn xor() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Xor(
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Value(1))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Xor(
                        box UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                        box UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Value(0))
            );
        }

        #[test]
        fn and() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::And(
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Value(2))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::And(
                        box UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(0).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Value(0))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::And(
                        box UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(u32::MAX as u128).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpression::identifier("a".into()))
            );
        }

        #[test]
        fn or() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Or(
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Value(3))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Or(
                        box UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(0).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpression::identifier("a".into()))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Or(
                        box UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(u32::MAX as u128).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Value(u32::MAX as u128))
            );
        }

        #[test]
        fn left_shift() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::LeftShift(
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                        3,
                    )
                ),
                Ok(UExpressionInner::Value(16))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::LeftShift(
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                        0,
                    )
                ),
                Ok(UExpressionInner::Value(2))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::LeftShift(
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                        32,
                    )
                ),
                Ok(UExpressionInner::Value(0))
            );
        }

        #[test]
        fn right_shift() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::RightShift(
                        box UExpressionInner::Value(4).annotate(UBitwidth::B32),
                        2,
                    )
                ),
                Ok(UExpressionInner::Value(1))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::RightShift(
                        box UExpressionInner::Value(4).annotate(UBitwidth::B32),
                        0,
                    )
                ),
                Ok(UExpressionInner::Value(4))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::RightShift(
                        box UExpressionInner::Value(4).annotate(UBitwidth::B32),
                        32,
                    )
                ),
                Ok(UExpressionInner::Value(0))
            );
        }

        #[test]
        fn not() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Not(box UExpressionInner::Value(2).annotate(UBitwidth::B32),)
                ),
                Ok(UExpressionInner::Value(4294967293))
            );
        }

        #[test]
        fn if_else() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::conditional(
                        BooleanExpression::Value(true),
                        UExpressionInner::Value(1).annotate(UBitwidth::B32),
                        UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpressionInner::Value(1))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::conditional(
                        BooleanExpression::Value(false),
                        UExpressionInner::Value(1).annotate(UBitwidth::B32),
                        UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpressionInner::Value(2))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::conditional(
                        BooleanExpression::identifier("a".into()),
                        UExpressionInner::Value(2).annotate(UBitwidth::B32),
                        UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpressionInner::Value(2))
            );
        }
    }
}
