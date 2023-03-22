use num::traits::Pow;
use num_bigint::BigUint;
use std::collections::HashMap;
use std::fmt;
use std::ops::*;
use zokrates_ast::common::{ResultFold, WithSpan};
use zokrates_ast::zir::types::UBitwidth;
use zokrates_ast::zir::AssertionStatement;
use zokrates_ast::zir::IfElseStatement;
use zokrates_ast::zir::{
    result_folder::*, Conditional, ConditionalExpression, ConditionalOrExpression, Constant, Expr,
    Id, IdentifierExpression, IdentifierOrExpression, SelectExpression, SelectOrExpression,
    ZirAssemblyStatement, ZirFunction,
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
            Error::AssertionFailed(err) => write!(f, "Assertion failed ({})", err),
        }
    }
}

#[derive(Default)]
pub struct ZirPropagator<'ast, T> {
    constants: Constants<'ast, T>,
}

impl<'ast, T: Field> ZirPropagator<'ast, T> {
    pub fn with_constants(constants: Constants<'ast, T>) -> Self {
        Self { constants }
    }
    pub fn propagate(p: ZirProgram<T>) -> Result<ZirProgram<T>, Error> {
        ZirPropagator::default().fold_program(p)
    }
}

impl<'ast, T: Field> ResultFolder<'ast, T> for ZirPropagator<'ast, T> {
    type Error = Error;

    fn fold_function(
        &mut self,
        f: ZirFunction<'ast, T>,
    ) -> Result<ZirFunction<'ast, T>, Self::Error> {
        Ok(ZirFunction {
            arguments: f
                .arguments
                .into_iter()
                .filter(|p| !self.constants.contains_key(&p.id.id))
                .collect(),
            statements: f
                .statements
                .into_iter()
                .map(|s| self.fold_statement(s))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .flatten()
                .collect(),
            ..f
        })
    }

    fn fold_assembly_assignment(
        &mut self,
        s: zokrates_ast::zir::AssemblyAssignment<'ast, T>,
    ) -> Result<Vec<ZirAssemblyStatement<'ast, T>>, Self::Error> {
        let assignees: Vec<_> = s
            .assignee
            .into_iter()
            .map(|a| self.fold_assignee(a))
            .collect::<Result<_, _>>()?;

        let function = self.fold_function(s.expression)?;

        match &function.statements.last().unwrap() {
            ZirStatement::Return(s) => {
                if s.inner.iter().all(|v| v.is_constant()) {
                    self.constants.extend(
                        assignees
                            .into_iter()
                            .zip(s.inner.iter())
                            .map(|(a, v)| (a.id, v.clone())),
                    );
                    Ok(vec![])
                } else {
                    assignees.iter().for_each(|a| {
                        self.constants.remove(&a.id);
                    });
                    Ok(vec![ZirAssemblyStatement::assignment(assignees, function)])
                }
            }
            _ => {
                assignees.iter().for_each(|a| {
                    self.constants.remove(&a.id);
                });
                Ok(vec![ZirAssemblyStatement::assignment(assignees, function)])
            }
        }
    }

    fn fold_assembly_constraint(
        &mut self,
        s: zokrates_ast::zir::AssemblyConstraint<'ast, T>,
    ) -> Result<Vec<ZirAssemblyStatement<'ast, T>>, Self::Error> {
        let left = self.fold_field_expression(s.left)?;
        let right = self.fold_field_expression(s.right)?;

        // a bit hacky, but we use a fake boolean expression to check this
        let is_equal = BooleanExpression::field_eq(left.clone(), right.clone());
        let is_equal = self.fold_boolean_expression(is_equal)?;

        match is_equal {
            BooleanExpression::Value(v) if v.value => Ok(vec![]),
            BooleanExpression::Value(v) if !v.value => {
                Err(Error::AssertionFailed(RuntimeError::SourceAssertion(
                    s.metadata
                        .message(Some(format!("In asm block: `{} !== {}`", left, right))),
                )))
            }
            _ => Ok(vec![ZirAssemblyStatement::constraint(
                left, right, s.metadata,
            )]),
        }
    }

    fn fold_assertion_statement(
        &mut self,
        s: AssertionStatement<'ast, T>,
    ) -> Result<Vec<ZirStatement<'ast, T>>, Self::Error> {
        match self.fold_boolean_expression(s.expression)? {
            BooleanExpression::Value(v) if v.value => Ok(vec![]),
            BooleanExpression::Value(v) if !v.value => Err(Error::AssertionFailed(s.error)),
            e => Ok(vec![ZirStatement::assertion(e, s.error)]),
        }
    }

    fn fold_definition_statement(
        &mut self,
        s: zokrates_ast::zir::DefinitionStatement<'ast, T>,
    ) -> Result<Vec<ZirStatement<'ast, T>>, Self::Error> {
        let e = self.fold_expression(s.rhs)?;
        match e {
            ZirExpression::FieldElement(FieldElementExpression::Value(..))
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

    fn fold_if_else_statement(
        &mut self,
        s: zokrates_ast::zir::IfElseStatement<'ast, T>,
    ) -> Result<Vec<ZirStatement<'ast, T>>, Self::Error> {
        {
            match self.fold_boolean_expression(s.condition)? {
                BooleanExpression::Value(v) if v.value => Ok(s
                    .consequence
                    .into_iter()
                    .map(|s| self.fold_statement(s))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .flatten()
                    .collect()),
                BooleanExpression::Value(v) if !v.value => Ok(s
                    .alternative
                    .into_iter()
                    .map(|s| self.fold_statement(s))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .flatten()
                    .collect()),
                e => Ok(vec![ZirStatement::IfElse(IfElseStatement::new(
                    e,
                    s.consequence
                        .into_iter()
                        .map(|s| self.fold_statement(s))
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .flatten()
                        .collect(),
                    s.alternative
                        .into_iter()
                        .map(|s| self.fold_statement(s))
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .flatten()
                        .collect(),
                ))]),
            }
        }
    }

    fn fold_multiple_definition_statement(
        &mut self,
        s: zokrates_ast::zir::MultipleDefinitionStatement<'ast, T>,
    ) -> Result<Vec<ZirStatement<'ast, T>>, Self::Error> {
        for a in &s.assignees {
            self.constants.remove(&a.id);
        }
        fold_multiple_definition_statement(self, s)
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

    fn fold_field_expression_cases(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> Result<FieldElementExpression<'ast, T>, Self::Error> {
        match e {
            FieldElementExpression::Value(n) => Ok(FieldElementExpression::Value(n)),
            FieldElementExpression::Add(e) => {
                let left = self.fold_field_expression(*e.left)?;
                let right = self.fold_field_expression(*e.right)?;

                Ok(match (left, right) {
                    (FieldElementExpression::Value(n), e)
                    | (e, FieldElementExpression::Value(n))
                        if n.value == T::from(0) =>
                    {
                        e
                    }
                    (FieldElementExpression::Value(n1), FieldElementExpression::Value(n2)) => {
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
                    (e, FieldElementExpression::Value(n)) if n.value == T::from(0) => e,
                    (FieldElementExpression::Value(n1), FieldElementExpression::Value(n2)) => {
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
                    (FieldElementExpression::Value(n), _)
                    | (_, FieldElementExpression::Value(n))
                        if n.value == T::from(0) =>
                    {
                        FieldElementExpression::number(T::from(0))
                    }
                    (FieldElementExpression::Value(n), e)
                    | (e, FieldElementExpression::Value(n))
                        if n.value == T::from(1) =>
                    {
                        e
                    }
                    (FieldElementExpression::Value(n1), FieldElementExpression::Value(n2)) => {
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
                    (_, FieldElementExpression::Value(n)) if n.value == T::from(0) => {
                        Err(Error::DivisionByZero)
                    }
                    (e, FieldElementExpression::Value(n)) if n.value == T::from(1) => Ok(e),
                    (FieldElementExpression::Value(n1), FieldElementExpression::Value(n2)) => {
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
                    (FieldElementExpression::Value(n), UExpressionInner::Value(e)) => Ok(
                        FieldElementExpression::number(n.value.pow(e.value as usize)),
                    ),
                    (e, exp) => {
                        Ok(FieldElementExpression::pow(e, exp.annotate(UBitwidth::B32))
                            .into_inner())
                    }
                }
            }
            FieldElementExpression::Xor(e) => {
                let e1 = self.fold_field_expression(*e.right)?;
                let e2 = self.fold_field_expression(*e.left)?;

                match (e1, e2) {
                    (FieldElementExpression::Value(n1), FieldElementExpression::Value(n2)) => {
                        Ok(FieldElementExpression::value(
                            T::try_from(n1.value.to_biguint().bitxor(n2.value.to_biguint()))
                                .unwrap(),
                        ))
                    }
                    (e1, e2) if e1.eq(&e2) => Ok(FieldElementExpression::value(T::from(0))),
                    (e1, e2) => Ok(FieldElementExpression::bitxor(e1, e2)),
                }
            }
            FieldElementExpression::And(e) => {
                let e1 = self.fold_field_expression(*e.left)?;
                let e2 = self.fold_field_expression(*e.right)?;

                match (e1, e2) {
                    (_, FieldElementExpression::Value(n))
                    | (FieldElementExpression::Value(n), _)
                        if n.value == T::from(0) =>
                    {
                        Ok(FieldElementExpression::Value(n))
                    }
                    (FieldElementExpression::Value(n1), FieldElementExpression::Value(n2)) => {
                        Ok(FieldElementExpression::value(
                            T::try_from(n1.value.to_biguint().bitand(n2.value.to_biguint()))
                                .unwrap(),
                        ))
                    }
                    (e1, e2) => Ok(FieldElementExpression::bitand(e1, e2)),
                }
            }
            FieldElementExpression::Or(e) => {
                let e1 = self.fold_field_expression(*e.left)?;
                let e2 = self.fold_field_expression(*e.right)?;

                match (e1, e2) {
                    (e, FieldElementExpression::Value(n))
                    | (FieldElementExpression::Value(n), e)
                        if n.value == T::from(0) =>
                    {
                        Ok(e)
                    }
                    (FieldElementExpression::Value(n1), FieldElementExpression::Value(n2)) => {
                        Ok(FieldElementExpression::value(
                            T::try_from(n1.value.to_biguint().bitor(n2.value.to_biguint()))
                                .unwrap(),
                        ))
                    }
                    (e1, e2) => Ok(FieldElementExpression::bitor(e1, e2)),
                }
            }
            FieldElementExpression::LeftShift(e) => {
                let expr = self.fold_field_expression(*e.left)?;
                let by = self.fold_uint_expression(*e.right)?;
                match (expr, by) {
                    (
                        e,
                        UExpression {
                            inner: UExpressionInner::Value(by),
                            ..
                        },
                    ) if by.value == 0 => Ok(e),
                    (
                        _,
                        UExpression {
                            inner: UExpressionInner::Value(by),
                            ..
                        },
                    ) if by.value as usize >= T::get_required_bits() => {
                        Ok(FieldElementExpression::value(T::from(0)))
                    }
                    (
                        FieldElementExpression::Value(n),
                        UExpression {
                            inner: UExpressionInner::Value(by),
                            ..
                        },
                    ) => {
                        let two = BigUint::from(2usize);
                        let mask: BigUint = two.pow(T::get_required_bits()).sub(1usize);

                        Ok(FieldElementExpression::value(
                            T::try_from(n.value.to_biguint().shl(by.value as usize).bitand(mask))
                                .unwrap(),
                        ))
                    }
                    (expr, by) => Ok(FieldElementExpression::left_shift(expr, by)),
                }
            }
            FieldElementExpression::RightShift(e) => {
                let expr = self.fold_field_expression(*e.left)?;
                let by = self.fold_uint_expression(*e.right)?;
                match (expr, by) {
                    (
                        e,
                        UExpression {
                            inner: UExpressionInner::Value(by),
                            ..
                        },
                    ) if by.value == 0 => Ok(e),
                    (
                        _,
                        UExpression {
                            inner: UExpressionInner::Value(by),
                            ..
                        },
                    ) if by.value as usize >= T::get_required_bits() => {
                        Ok(FieldElementExpression::value(T::from(0)))
                    }
                    (
                        FieldElementExpression::Value(n),
                        UExpression {
                            inner: UExpressionInner::Value(by),
                            ..
                        },
                    ) => Ok(FieldElementExpression::value(
                        T::try_from(n.value.to_biguint().shr(by.value as usize)).unwrap(),
                    )),
                    (expr, by) => Ok(FieldElementExpression::right_shift(expr, by)),
                }
            }
            e => fold_field_expression_cases(self, e),
        }
    }

    fn fold_boolean_expression_cases(
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
                    (FieldElementExpression::Value(n1), FieldElementExpression::Value(n2)) => {
                        Ok(BooleanExpression::value(n1 < n2))
                    }
                    (_, FieldElementExpression::Value(c)) if c.value == T::zero() => {
                        Ok(BooleanExpression::value(false))
                    }
                    (FieldElementExpression::Value(c), _) if c.value == T::max_value() => {
                        Ok(BooleanExpression::value(false))
                    }
                    (e1, e2) => Ok(BooleanExpression::field_lt(e1, e2)),
                }
            }
            BooleanExpression::FieldLe(e) => {
                match (
                    self.fold_field_expression(*e.left)?,
                    self.fold_field_expression(*e.right)?,
                ) {
                    (FieldElementExpression::Value(n1), FieldElementExpression::Value(n2)) => {
                        Ok(BooleanExpression::value(n1 <= n2))
                    }
                    (e1, e2) => Ok(BooleanExpression::field_le(e1, e2)),
                }
            }
            BooleanExpression::FieldEq(e) => {
                match (
                    self.fold_field_expression(*e.left)?,
                    self.fold_field_expression(*e.right)?,
                ) {
                    (FieldElementExpression::Value(v1), FieldElementExpression::Value(v2)) => {
                        Ok(BooleanExpression::value(v1.eq(&v2)))
                    }
                    (e1, e2) => {
                        if e1.eq(&e2) {
                            Ok(BooleanExpression::value(true))
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
                        Ok(BooleanExpression::value(v1 < v2))
                    }
                    _ => Ok(BooleanExpression::uint_lt(e1, e2)),
                }
            }
            BooleanExpression::UintLe(e) => {
                let e1 = self.fold_uint_expression(*e.left)?;
                let e2 = self.fold_uint_expression(*e.right)?;

                match (e1.as_inner(), e2.as_inner()) {
                    (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                        Ok(BooleanExpression::value(v1 <= v2))
                    }
                    _ => Ok(BooleanExpression::uint_le(e1, e2)),
                }
            }
            BooleanExpression::UintEq(e) => {
                let e1 = self.fold_uint_expression(*e.left)?;
                let e2 = self.fold_uint_expression(*e.right)?;

                match (e1.as_inner(), e2.as_inner()) {
                    (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                        Ok(BooleanExpression::value(v1 == v2))
                    }
                    _ => {
                        if e1.eq(&e2) {
                            Ok(BooleanExpression::value(true))
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
                        Ok(BooleanExpression::value(v1 == v2))
                    }
                    (e1, e2) => {
                        if e1.eq(&e2) {
                            Ok(BooleanExpression::value(true))
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
                        Ok(BooleanExpression::value(v1.value || v2.value))
                    }
                    (_, BooleanExpression::Value(v)) | (BooleanExpression::Value(v), _)
                        if v.value =>
                    {
                        Ok(BooleanExpression::value(true))
                    }
                    (e, BooleanExpression::Value(v)) | (BooleanExpression::Value(v), e)
                        if !v.value =>
                    {
                        Ok(e)
                    }
                    (e1, e2) => Ok(BooleanExpression::bitor(e1, e2)),
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
                        Ok(BooleanExpression::value(false))
                    }
                    (e1, e2) => Ok(BooleanExpression::bitand(e1, e2)),
                }
            }
            BooleanExpression::Not(e) => match self.fold_boolean_expression(*e.inner)? {
                BooleanExpression::Value(v) => Ok(BooleanExpression::value(!v.value)),
                e => Ok(BooleanExpression::not(e)),
            },
            e => fold_boolean_expression_cases(self, e),
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

    fn fold_uint_expression_cases(
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
                        Ok(UExpression::value(
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
                        Ok(UExpression::value(
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
                        Ok(UExpression::value(0))
                    }
                    (e, UExpressionInner::Value(v)) | (UExpressionInner::Value(v), e)
                        if v.value == 1 =>
                    {
                        Ok(e)
                    }
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        Ok(UExpression::value(
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
                        Ok(UExpression::value(
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
                        Ok(UExpression::value(
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
                        Ok(UExpression::value(n1.value ^ n2.value))
                    }
                    (e1, e2) if e1.eq(&e2) => Ok(UExpression::value(0)),
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
                        Ok(UExpression::value(0))
                    }
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        Ok(UExpression::value(n1.value & n2.value))
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
                        Ok(UExpression::value(n.value))
                    }
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        Ok(UExpression::value(n1.value | n2.value))
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
                        Ok(UExpression::value(0))
                    }
                    (UExpressionInner::Value(n), UExpressionInner::Value(by)) => {
                        Ok(UExpression::value(
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
                        Ok(UExpression::value(0))
                    }
                    (UExpressionInner::Value(n), UExpressionInner::Value(by)) => {
                        Ok(UExpression::value(n.value >> by.value))
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
                    UExpressionInner::Value(n) => Ok(UExpression::value(
                        !n.value & (2_u128.pow(bitwidth as u32) - 1),
                    )),
                    e => Ok(UExpression::not(e.annotate(bitwidth)).into_inner()),
                }
            }
            e => fold_uint_expression_cases(self, bitwidth, e),
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

        match condition {
            BooleanExpression::Value(v) if v.value => Ok(ConditionalOrExpression::Expression(
                e.consequence.fold(self)?.into_inner(),
            )),
            BooleanExpression::Value(v) if !v.value => Ok(ConditionalOrExpression::Expression(
                e.alternative.fold(self)?.into_inner(),
            )),
            condition => {
                let consequence = e.consequence.fold(self)?;
                let alternative = e.alternative.fold(self)?;

                if consequence == alternative {
                    Ok(ConditionalOrExpression::Expression(
                        consequence.into_inner(),
                    ))
                } else {
                    Ok(ConditionalOrExpression::Conditional(
                        ConditionalExpression::new(condition, consequence, alternative),
                    ))
                }
            }
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
        let statements = vec![ZirStatement::assertion(
            BooleanExpression::bitand(
                BooleanExpression::field_eq(
                    FieldElementExpression::identifier("x".into()),
                    FieldElementExpression::identifier("y".into()),
                ),
                BooleanExpression::field_eq(
                    FieldElementExpression::value(Bn128Field::from(1)),
                    FieldElementExpression::value(Bn128Field::from(1)),
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
            vec![ZirStatement::assertion(
                BooleanExpression::field_eq(
                    FieldElementExpression::identifier("x".into()),
                    FieldElementExpression::identifier("y".into()),
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
                        FieldElementExpression::value(Bn128Field::from(1)),
                        FieldElementExpression::value(Bn128Field::from(2)),
                    ],
                    UExpression::value(1).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::value(Bn128Field::from(2)))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::select(
                    vec![
                        FieldElementExpression::value(Bn128Field::from(1)),
                        FieldElementExpression::value(Bn128Field::from(2)),
                    ],
                    UExpression::value(3).annotate(UBitwidth::B32),
                )),
                Err(Error::OutOfBounds(3, 2))
            );
        }

        #[test]
        fn add() {
            let mut propagator = ZirPropagator::default();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::add(
                    FieldElementExpression::value(Bn128Field::from(2)),
                    FieldElementExpression::value(Bn128Field::from(3)),
                )),
                Ok(FieldElementExpression::value(Bn128Field::from(5)))
            );

            // a + 0 = a
            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::add(
                    FieldElementExpression::identifier("a".into()),
                    FieldElementExpression::value(Bn128Field::from(0)),
                )),
                Ok(FieldElementExpression::identifier("a".into()))
            );
        }

        #[test]
        fn sub() {
            let mut propagator = ZirPropagator::default();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::sub(
                    FieldElementExpression::value(Bn128Field::from(3)),
                    FieldElementExpression::value(Bn128Field::from(2)),
                )),
                Ok(FieldElementExpression::value(Bn128Field::from(1)))
            );

            // a - 0 = a
            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::sub(
                    FieldElementExpression::identifier("a".into()),
                    FieldElementExpression::value(Bn128Field::from(0)),
                )),
                Ok(FieldElementExpression::identifier("a".into()))
            );
        }

        #[test]
        fn mult() {
            let mut propagator = ZirPropagator::default();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::mul(
                    FieldElementExpression::value(Bn128Field::from(3)),
                    FieldElementExpression::value(Bn128Field::from(2)),
                )),
                Ok(FieldElementExpression::value(Bn128Field::from(6)))
            );

            // a * 0 = 0
            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::mul(
                    FieldElementExpression::identifier("a".into()),
                    FieldElementExpression::value(Bn128Field::from(0)),
                )),
                Ok(FieldElementExpression::value(Bn128Field::from(0)))
            );

            // a * 1 = a
            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::mul(
                    FieldElementExpression::identifier("a".into()),
                    FieldElementExpression::value(Bn128Field::from(1)),
                )),
                Ok(FieldElementExpression::identifier("a".into()))
            );
        }

        #[test]
        fn div() {
            let mut propagator = ZirPropagator::default();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::div(
                    FieldElementExpression::value(Bn128Field::from(6)),
                    FieldElementExpression::value(Bn128Field::from(2)),
                )),
                Ok(FieldElementExpression::value(Bn128Field::from(3)))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::div(
                    FieldElementExpression::identifier("a".into()),
                    FieldElementExpression::value(Bn128Field::from(1)),
                )),
                Ok(FieldElementExpression::identifier("a".into()))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::div(
                    FieldElementExpression::identifier("a".into()),
                    FieldElementExpression::value(Bn128Field::from(0)),
                )),
                Err(Error::DivisionByZero)
            );
        }

        #[test]
        fn pow() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::pow(
                    FieldElementExpression::value(Bn128Field::from(3)),
                    UExpression::value(2).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::value(Bn128Field::from(9)))
            );

            // a ** 0 = 1
            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::pow(
                    FieldElementExpression::identifier("a".into()),
                    UExpression::value(0).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::value(Bn128Field::from(1)))
            );

            // a ** 1 = a
            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::pow(
                    FieldElementExpression::identifier("a".into()),
                    UExpression::value(1).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::identifier("a".into()))
            );
        }

        #[test]
        fn left_shift() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::left_shift(
                    FieldElementExpression::identifier("a".into()),
                    UExpression::value(0).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::identifier("a".into()))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::left_shift(
                    FieldElementExpression::value(Bn128Field::from(2)),
                    UExpression::value(2_u128).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::value(Bn128Field::from(8)))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::left_shift(
                     FieldElementExpression::value(Bn128Field::from(1)),
                     UExpression::value((Bn128Field::get_required_bits() - 1) as u128).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::value(Bn128Field::try_from_dec_str("14474011154664524427946373126085988481658748083205070504932198000989141204992").unwrap()))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::left_shift(
                     FieldElementExpression::value(Bn128Field::from(3)),
                     UExpression::value((Bn128Field::get_required_bits() - 3) as u128).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::value(Bn128Field::try_from_dec_str("10855508365998393320959779844564491361244061062403802878699148500741855903744").unwrap()))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::left_shift(
                    FieldElementExpression::value(Bn128Field::from(1)),
                    UExpression::value((Bn128Field::get_required_bits()) as u128)
                        .annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::value(Bn128Field::from(0)))
            );
        }

        #[test]
        fn right_shift() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::right_shift(
                    FieldElementExpression::identifier("a".into()),
                    UExpression::value(0).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::identifier("a".into()))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::right_shift(
                    FieldElementExpression::identifier("a".into()),
                    UExpression::value(Bn128Field::get_required_bits() as u128)
                        .annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::value(Bn128Field::from(0)))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::right_shift(
                    FieldElementExpression::value(Bn128Field::from(3)),
                    UExpression::value(1_u128).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::value(Bn128Field::from(1)))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::right_shift(
                    FieldElementExpression::value(Bn128Field::from(2)),
                    UExpression::value(2_u128).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::value(Bn128Field::from(0)))
            );
            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::right_shift(
                    FieldElementExpression::value(Bn128Field::from(2)),
                    UExpression::value(4_u128).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::value(Bn128Field::from(0)))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::right_shift(
                    FieldElementExpression::value(Bn128Field::max_value()),
                    UExpression::value((Bn128Field::get_required_bits() - 1) as u128)
                        .annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::value(Bn128Field::from(1)))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::right_shift(
                    FieldElementExpression::value(Bn128Field::max_value()),
                    UExpression::value(Bn128Field::get_required_bits() as u128)
                        .annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::value(Bn128Field::from(0)))
            );
        }

        #[test]
        fn if_else() {
            let mut propagator = ZirPropagator::default();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::conditional(
                    BooleanExpression::value(true),
                    FieldElementExpression::value(Bn128Field::from(1)),
                    FieldElementExpression::value(Bn128Field::from(2)),
                )),
                Ok(FieldElementExpression::value(Bn128Field::from(1)))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::conditional(
                    BooleanExpression::value(false),
                    FieldElementExpression::value(Bn128Field::from(1)),
                    FieldElementExpression::value(Bn128Field::from(2)),
                )),
                Ok(FieldElementExpression::value(Bn128Field::from(2)))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::conditional(
                    BooleanExpression::identifier("a".into()),
                    FieldElementExpression::value(Bn128Field::from(2)),
                    FieldElementExpression::value(Bn128Field::from(2)),
                )),
                Ok(FieldElementExpression::value(Bn128Field::from(2)))
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
                        BooleanExpression::value(false),
                        BooleanExpression::value(true)
                    ],
                    UExpression::value(1).annotate(UBitwidth::B32),
                )),
                Ok(BooleanExpression::value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::select(
                    vec![
                        BooleanExpression::value(false),
                        BooleanExpression::value(true)
                    ],
                    UExpression::value(3).annotate(UBitwidth::B32),
                )),
                Err(Error::OutOfBounds(3, 2))
            );
        }

        #[test]
        fn field_lt() {
            let mut propagator = ZirPropagator::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::field_lt(
                    FieldElementExpression::value(Bn128Field::from(2)),
                    FieldElementExpression::value(Bn128Field::from(3)),
                )),
                Ok(BooleanExpression::value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::field_lt(
                    FieldElementExpression::value(Bn128Field::from(3)),
                    FieldElementExpression::value(Bn128Field::from(3)),
                )),
                Ok(BooleanExpression::value(false))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::field_lt(
                    FieldElementExpression::identifier("a".into()),
                    FieldElementExpression::value(Bn128Field::from(0)),
                )),
                Ok(BooleanExpression::value(false))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::field_lt(
                    FieldElementExpression::value(Bn128Field::max_value()),
                    FieldElementExpression::identifier("a".into()),
                )),
                Ok(BooleanExpression::value(false))
            );
        }

        #[test]
        fn field_le() {
            let mut propagator = ZirPropagator::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::field_le(
                    FieldElementExpression::value(Bn128Field::from(2)),
                    FieldElementExpression::value(Bn128Field::from(3)),
                )),
                Ok(BooleanExpression::value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::field_le(
                    FieldElementExpression::value(Bn128Field::from(3)),
                    FieldElementExpression::value(Bn128Field::from(3)),
                )),
                Ok(BooleanExpression::value(true))
            );
        }

        #[test]
        fn field_eq() {
            let mut propagator = ZirPropagator::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::field_eq(
                    FieldElementExpression::value(Bn128Field::from(2)),
                    FieldElementExpression::value(Bn128Field::from(2)),
                )),
                Ok(BooleanExpression::value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::field_eq(
                    FieldElementExpression::value(Bn128Field::from(3)),
                    FieldElementExpression::value(Bn128Field::from(2)),
                )),
                Ok(BooleanExpression::value(false))
            );
        }

        #[test]
        fn uint_lt() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::uint_lt(
                    UExpression::value(2).annotate(UBitwidth::B32),
                    UExpression::value(3).annotate(UBitwidth::B32),
                )),
                Ok(BooleanExpression::value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::uint_lt(
                    UExpression::value(3).annotate(UBitwidth::B32),
                    UExpression::value(3).annotate(UBitwidth::B32),
                )),
                Ok(BooleanExpression::value(false))
            );
        }

        #[test]
        fn uint_le() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::uint_le(
                    UExpression::value(2).annotate(UBitwidth::B32),
                    UExpression::value(3).annotate(UBitwidth::B32),
                )),
                Ok(BooleanExpression::value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::uint_le(
                    UExpression::value(3).annotate(UBitwidth::B32),
                    UExpression::value(3).annotate(UBitwidth::B32),
                )),
                Ok(BooleanExpression::value(true))
            );
        }

        #[test]
        fn uint_eq() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::uint_eq(
                    UExpression::value(2).annotate(UBitwidth::B32),
                    UExpression::value(2).annotate(UBitwidth::B32),
                )),
                Ok(BooleanExpression::value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::uint_eq(
                    UExpression::value(2).annotate(UBitwidth::B32),
                    UExpression::value(3).annotate(UBitwidth::B32),
                )),
                Ok(BooleanExpression::value(false))
            );
        }

        #[test]
        fn bool_eq() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::bool_eq(
                    BooleanExpression::value(true),
                    BooleanExpression::value(true),
                )),
                Ok(BooleanExpression::value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::bool_eq(
                    BooleanExpression::value(true),
                    BooleanExpression::value(false),
                )),
                Ok(BooleanExpression::value(false))
            );
        }

        #[test]
        fn and() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::bitand(
                    BooleanExpression::value(true),
                    BooleanExpression::value(true),
                )),
                Ok(BooleanExpression::value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::bitand(
                    BooleanExpression::value(true),
                    BooleanExpression::value(false),
                )),
                Ok(BooleanExpression::value(false))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::bitand(
                    BooleanExpression::identifier("a".into()),
                    BooleanExpression::value(true)
                )),
                Ok(BooleanExpression::identifier("a".into()))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::bitand(
                    BooleanExpression::identifier("a".into()),
                    BooleanExpression::value(false),
                )),
                Ok(BooleanExpression::value(false))
            );
        }

        #[test]
        fn or() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::bitor(
                    BooleanExpression::value(true),
                    BooleanExpression::value(true),
                )),
                Ok(BooleanExpression::value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::bitor(
                    BooleanExpression::value(true),
                    BooleanExpression::value(false),
                )),
                Ok(BooleanExpression::value(true))
            );
        }

        #[test]
        fn not() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::not(
                    BooleanExpression::value(true)
                )),
                Ok(BooleanExpression::value(false))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::not(
                    BooleanExpression::value(false),
                )),
                Ok(BooleanExpression::value(true))
            );
        }

        #[test]
        fn if_else() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::conditional(
                    BooleanExpression::value(true),
                    BooleanExpression::value(true),
                    BooleanExpression::value(false)
                )),
                Ok(BooleanExpression::value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::conditional(
                    BooleanExpression::value(false),
                    BooleanExpression::value(true),
                    BooleanExpression::value(false),
                )),
                Ok(BooleanExpression::value(false))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::conditional(
                    BooleanExpression::identifier("a".into()),
                    BooleanExpression::value(true),
                    BooleanExpression::value(true),
                )),
                Ok(BooleanExpression::value(true))
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
                            UExpression::value(1).annotate(UBitwidth::B32),
                            UExpression::value(2).annotate(UBitwidth::B32),
                        ],
                        UExpression::value(1).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpression::value(2))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::select(
                        vec![
                            UExpression::value(1).annotate(UBitwidth::B32),
                            UExpression::value(2).annotate(UBitwidth::B32),
                        ],
                        UExpression::value(3).annotate(UBitwidth::B32),
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
                    UExpression::add(
                        UExpression::value(2).annotate(UBitwidth::B32),
                        UExpression::value(3).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpression::value(5))
            );

            // a + 0 = a
            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::add(
                        UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                        UExpression::value(0).annotate(UBitwidth::B32),
                    )
                    .into_inner()
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
                    UExpression::sub(
                        UExpression::value(3).annotate(UBitwidth::B32),
                        UExpression::value(2).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpression::value(1))
            );

            // a - 0 = a
            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::sub(
                        UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                        UExpression::value(0).annotate(UBitwidth::B32),
                    )
                    .into_inner()
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
                    UExpression::mult(
                        UExpression::value(3).annotate(UBitwidth::B32),
                        UExpression::value(2).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpression::value(6))
            );

            // a * 1 = a
            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::mult(
                        UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                        UExpression::value(1).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpression::identifier("a".into()))
            );

            // a * 0 = 0
            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::mult(
                        UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                        UExpression::value(0).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpression::value(0))
            );
        }

        #[test]
        fn div() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::div(
                        UExpression::value(6).annotate(UBitwidth::B32),
                        UExpression::value(2).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpression::value(3))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::div(
                        UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                        UExpression::value(1).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpression::identifier("a".into()))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::div(
                        UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                        UExpression::value(0).annotate(UBitwidth::B32),
                    )
                    .into_inner()
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
                    UExpression::rem(
                        UExpression::value(2).annotate(UBitwidth::B32),
                        UExpression::value(3).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpression::value(2))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::rem(
                        UExpression::value(3).annotate(UBitwidth::B32),
                        UExpression::value(2).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpression::value(1))
            );
        }

        #[test]
        fn xor() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::xor(
                        UExpression::value(2).annotate(UBitwidth::B32),
                        UExpression::value(3).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpression::value(1))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::xor(
                        UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                        UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpression::value(0))
            );
        }

        #[test]
        fn and() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::and(
                        UExpression::value(2).annotate(UBitwidth::B32),
                        UExpression::value(3).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpression::value(2))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::and(
                        UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                        UExpression::value(0).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpression::value(0))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::and(
                        UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                        UExpression::value(u32::MAX as u128).annotate(UBitwidth::B32),
                    )
                    .into_inner()
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
                    UExpression::or(
                        UExpression::value(2).annotate(UBitwidth::B32),
                        UExpression::value(3).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpression::value(3))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::or(
                        UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                        UExpression::value(0).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpression::identifier("a".into()))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::or(
                        UExpression::identifier("a".into()).annotate(UBitwidth::B32),
                        UExpression::value(u32::MAX as u128).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpression::value(u32::MAX as u128))
            );
        }

        #[test]
        fn left_shift() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::left_shift(
                        UExpression::value(2).annotate(UBitwidth::B32),
                        3.into(),
                    )
                    .into_inner()
                ),
                Ok(UExpression::value(16))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::left_shift(
                        UExpression::value(2).annotate(UBitwidth::B32),
                        0.into(),
                    )
                    .into_inner()
                ),
                Ok(UExpression::value(2))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::left_shift(
                        UExpression::value(2).annotate(UBitwidth::B32),
                        32.into(),
                    )
                    .into_inner()
                ),
                Ok(UExpression::value(0))
            );
        }

        #[test]
        fn right_shift() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::right_shift(
                        UExpression::value(4).annotate(UBitwidth::B32),
                        2.into(),
                    )
                    .into_inner()
                ),
                Ok(UExpression::value(1))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::right_shift(
                        UExpression::value(4).annotate(UBitwidth::B32),
                        0.into(),
                    )
                    .into_inner()
                ),
                Ok(UExpression::value(4))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::right_shift(
                        UExpression::value(4).annotate(UBitwidth::B32),
                        32.into(),
                    )
                    .into_inner()
                ),
                Ok(UExpression::value(0))
            );
        }

        #[test]
        fn not() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::not(UExpression::value(2).annotate(UBitwidth::B32),).into_inner()
                ),
                Ok(UExpression::value(4294967293))
            );
        }

        #[test]
        fn if_else() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::conditional(
                        BooleanExpression::value(true),
                        UExpression::value(1).annotate(UBitwidth::B32),
                        UExpression::value(2).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpression::value(1))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::conditional(
                        BooleanExpression::value(false),
                        UExpression::value(1).annotate(UBitwidth::B32),
                        UExpression::value(2).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpression::value(2))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpression::conditional(
                        BooleanExpression::identifier("a".into()),
                        UExpression::value(2).annotate(UBitwidth::B32),
                        UExpression::value(2).annotate(UBitwidth::B32),
                    )
                    .into_inner()
                ),
                Ok(UExpression::value(2))
            );
        }
    }
}
