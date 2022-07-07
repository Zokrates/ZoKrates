use std::collections::HashMap;
use std::fmt;
use zokrates_ast::zir::result_folder::fold_statement;
use zokrates_ast::zir::result_folder::ResultFolder;
use zokrates_ast::zir::types::UBitwidth;
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
            ZirStatement::Assertion(e, error) => match self.fold_boolean_expression(e)? {
                BooleanExpression::Value(true) => Ok(vec![]),
                BooleanExpression::Value(false) => Err(Error::AssertionFailed(error)),
                e => Ok(vec![ZirStatement::Assertion(e, error)]),
            },
            ZirStatement::Definition(a, e) => {
                let e = self.fold_expression(e)?;
                match e {
                    ZirExpression::FieldElement(FieldElementExpression::Number(..))
                    | ZirExpression::Boolean(BooleanExpression::Value(..))
                    | ZirExpression::Uint(UExpression {
                        inner: UExpressionInner::Value(..),
                        ..
                    }) => {
                        self.constants.insert(a.id, e);
                        Ok(vec![])
                    }
                    _ => {
                        self.constants.remove(&a.id);
                        Ok(vec![ZirStatement::Definition(a, e)])
                    }
                }
            }
            ZirStatement::IfElse(e, consequence, alternative) => {
                match self.fold_boolean_expression(e)? {
                    BooleanExpression::Value(true) => Ok(consequence
                        .into_iter()
                        .map(|s| self.fold_statement(s))
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .flatten()
                        .collect()),
                    BooleanExpression::Value(false) => Ok(alternative
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

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> Result<FieldElementExpression<'ast, T>, Self::Error> {
        match e {
            FieldElementExpression::Number(n) => Ok(FieldElementExpression::Number(n)),
            FieldElementExpression::Identifier(id) => match self.constants.get(&id) {
                Some(ZirExpression::FieldElement(FieldElementExpression::Number(v))) => {
                    Ok(FieldElementExpression::Number(v.clone()))
                }
                _ => Ok(FieldElementExpression::Identifier(id)),
            },
            FieldElementExpression::Select(e, box index) => {
                let index = self.fold_uint_expression(index)?;
                let e: Vec<FieldElementExpression<'ast, T>> = e
                    .into_iter()
                    .map(|e| self.fold_field_expression(e))
                    .collect::<Result<_, _>>()?;

                match index.into_inner() {
                    UExpressionInner::Value(v) => e
                        .get(v as usize)
                        .cloned()
                        .ok_or(Error::OutOfBounds(v as usize, e.len())),
                    i => Ok(FieldElementExpression::Select(
                        e,
                        box i.annotate(UBitwidth::B32),
                    )),
                }
            }
            FieldElementExpression::Add(box e1, box e2) => {
                match (
                    self.fold_field_expression(e1)?,
                    self.fold_field_expression(e2)?,
                ) {
                    (FieldElementExpression::Number(n), e)
                    | (e, FieldElementExpression::Number(n))
                        if n == T::from(0) =>
                    {
                        Ok(e)
                    }
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        Ok(FieldElementExpression::Number(n1 + n2))
                    }
                    (e1, e2) => Ok(FieldElementExpression::Add(box e1, box e2)),
                }
            }
            FieldElementExpression::Sub(box e1, box e2) => {
                match (
                    self.fold_field_expression(e1)?,
                    self.fold_field_expression(e2)?,
                ) {
                    (e, FieldElementExpression::Number(n)) if n == T::from(0) => Ok(e),
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        Ok(FieldElementExpression::Number(n1 - n2))
                    }
                    (e1, e2) => Ok(FieldElementExpression::Sub(box e1, box e2)),
                }
            }
            FieldElementExpression::Mult(box e1, box e2) => {
                match (
                    self.fold_field_expression(e1)?,
                    self.fold_field_expression(e2)?,
                ) {
                    (FieldElementExpression::Number(n), _)
                    | (_, FieldElementExpression::Number(n))
                        if n == T::from(0) =>
                    {
                        Ok(FieldElementExpression::Number(T::from(0)))
                    }
                    (FieldElementExpression::Number(n), e)
                    | (e, FieldElementExpression::Number(n))
                        if n == T::from(1) =>
                    {
                        Ok(e)
                    }
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        Ok(FieldElementExpression::Number(n1 * n2))
                    }
                    (e1, e2) => Ok(FieldElementExpression::Mult(box e1, box e2)),
                }
            }
            FieldElementExpression::Div(box e1, box e2) => {
                match (
                    self.fold_field_expression(e1)?,
                    self.fold_field_expression(e2)?,
                ) {
                    (_, FieldElementExpression::Number(n)) if n == T::from(0) => {
                        Err(Error::DivisionByZero)
                    }
                    (e, FieldElementExpression::Number(n)) if n == T::from(1) => Ok(e),
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        Ok(FieldElementExpression::Number(n1 / n2))
                    }
                    (e1, e2) => Ok(FieldElementExpression::Div(box e1, box e2)),
                }
            }
            FieldElementExpression::Pow(box e, box exponent) => {
                let exponent = self.fold_uint_expression(exponent)?;
                match (self.fold_field_expression(e)?, exponent.into_inner()) {
                    (_, UExpressionInner::Value(n2)) if n2 == 0 => {
                        Ok(FieldElementExpression::Number(T::from(1)))
                    }
                    (e, UExpressionInner::Value(n2)) if n2 == 1 => Ok(e),
                    (FieldElementExpression::Number(n), UExpressionInner::Value(e)) => {
                        Ok(FieldElementExpression::Number(n.pow(e as usize)))
                    }
                    (e, exp) => Ok(FieldElementExpression::Pow(
                        box e,
                        box exp.annotate(UBitwidth::B32),
                    )),
                }
            }
            FieldElementExpression::Conditional(
                box condition,
                box consequence,
                box alternative,
            ) => {
                let condition = self.fold_boolean_expression(condition)?;
                let consequence = self.fold_field_expression(consequence)?;
                let alternative = self.fold_field_expression(alternative)?;

                match (condition, consequence, alternative) {
                    (_, consequence, alternative) if consequence == alternative => Ok(consequence),
                    (BooleanExpression::Value(true), consequence, _) => Ok(consequence),
                    (BooleanExpression::Value(false), _, alternative) => Ok(alternative),
                    (condition, consequence, alternative) => {
                        Ok(FieldElementExpression::Conditional(
                            box condition,
                            box consequence,
                            box alternative,
                        ))
                    }
                }
            }
        }
    }

    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> Result<BooleanExpression<'ast, T>, Error> {
        match e {
            BooleanExpression::Value(v) => Ok(BooleanExpression::Value(v)),
            BooleanExpression::Identifier(id) => match self.constants.get(&id) {
                Some(ZirExpression::Boolean(BooleanExpression::Value(v))) => {
                    Ok(BooleanExpression::Value(*v))
                }
                _ => Ok(BooleanExpression::Identifier(id)),
            },
            BooleanExpression::Select(e, box index) => {
                let index = self.fold_uint_expression(index)?;
                let e: Vec<BooleanExpression<'ast, T>> = e
                    .into_iter()
                    .map(|e| self.fold_boolean_expression(e))
                    .collect::<Result<_, _>>()?;

                match index.as_inner() {
                    UExpressionInner::Value(v) => e
                        .get(*v as usize)
                        .cloned()
                        .ok_or(Error::OutOfBounds(*v as usize, e.len())),
                    _ => Ok(BooleanExpression::Select(e, box index)),
                }
            }
            BooleanExpression::FieldLt(box e1, box e2) => {
                match (
                    self.fold_field_expression(e1)?,
                    self.fold_field_expression(e2)?,
                ) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        Ok(BooleanExpression::Value(n1 < n2))
                    }
                    (_, FieldElementExpression::Number(c)) if c == T::zero() => {
                        Ok(BooleanExpression::Value(false))
                    }
                    (FieldElementExpression::Number(c), _) if c == T::max_value() => {
                        Ok(BooleanExpression::Value(false))
                    }
                    (e1, e2) => Ok(BooleanExpression::FieldLt(box e1, box e2)),
                }
            }
            BooleanExpression::FieldLe(box e1, box e2) => {
                match (
                    self.fold_field_expression(e1)?,
                    self.fold_field_expression(e2)?,
                ) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        Ok(BooleanExpression::Value(n1 <= n2))
                    }
                    (e1, e2) => Ok(BooleanExpression::FieldLe(box e1, box e2)),
                }
            }
            BooleanExpression::FieldGe(box e1, box e2) => {
                match (
                    self.fold_field_expression(e1)?,
                    self.fold_field_expression(e2)?,
                ) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        Ok(BooleanExpression::Value(n1 >= n2))
                    }
                    (e1, e2) => Ok(BooleanExpression::FieldGe(box e1, box e2)),
                }
            }
            BooleanExpression::FieldGt(box e1, box e2) => {
                match (
                    self.fold_field_expression(e1)?,
                    self.fold_field_expression(e2)?,
                ) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        Ok(BooleanExpression::Value(n1 > n2))
                    }
                    (_, FieldElementExpression::Number(c)) if c == T::max_value() => {
                        Ok(BooleanExpression::Value(false))
                    }
                    (FieldElementExpression::Number(c), _) if c == T::zero() => {
                        Ok(BooleanExpression::Value(false))
                    }
                    (e1, e2) => Ok(BooleanExpression::FieldGt(box e1, box e2)),
                }
            }
            BooleanExpression::FieldEq(box e1, box e2) => {
                match (
                    self.fold_field_expression(e1)?,
                    self.fold_field_expression(e2)?,
                ) {
                    (FieldElementExpression::Number(v1), FieldElementExpression::Number(v2)) => {
                        Ok(BooleanExpression::Value(v1.eq(&v2)))
                    }
                    (e1, e2) => {
                        if e1.eq(&e2) {
                            Ok(BooleanExpression::Value(true))
                        } else {
                            Ok(BooleanExpression::FieldEq(box e1, box e2))
                        }
                    }
                }
            }
            BooleanExpression::UintLt(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1)?;
                let e2 = self.fold_uint_expression(e2)?;

                match (e1.as_inner(), e2.as_inner()) {
                    (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                        Ok(BooleanExpression::Value(v1 < v2))
                    }
                    _ => Ok(BooleanExpression::UintLt(box e1, box e2)),
                }
            }
            BooleanExpression::UintLe(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1)?;
                let e2 = self.fold_uint_expression(e2)?;

                match (e1.as_inner(), e2.as_inner()) {
                    (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                        Ok(BooleanExpression::Value(v1 <= v2))
                    }
                    _ => Ok(BooleanExpression::UintLe(box e1, box e2)),
                }
            }
            BooleanExpression::UintGe(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1)?;
                let e2 = self.fold_uint_expression(e2)?;

                match (e1.as_inner(), e2.as_inner()) {
                    (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                        Ok(BooleanExpression::Value(v1 >= v2))
                    }
                    _ => Ok(BooleanExpression::UintGe(box e1, box e2)),
                }
            }
            BooleanExpression::UintGt(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1)?;
                let e2 = self.fold_uint_expression(e2)?;

                match (e1.as_inner(), e2.as_inner()) {
                    (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                        Ok(BooleanExpression::Value(v1 > v2))
                    }
                    _ => Ok(BooleanExpression::UintGt(box e1, box e2)),
                }
            }
            BooleanExpression::UintEq(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1)?;
                let e2 = self.fold_uint_expression(e2)?;

                match (e1.as_inner(), e2.as_inner()) {
                    (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                        Ok(BooleanExpression::Value(v1 == v2))
                    }
                    _ => {
                        if e1.eq(&e2) {
                            Ok(BooleanExpression::Value(true))
                        } else {
                            Ok(BooleanExpression::UintEq(box e1, box e2))
                        }
                    }
                }
            }
            BooleanExpression::BoolEq(box e1, box e2) => {
                match (
                    self.fold_boolean_expression(e1)?,
                    self.fold_boolean_expression(e2)?,
                ) {
                    (BooleanExpression::Value(v1), BooleanExpression::Value(v2)) => {
                        Ok(BooleanExpression::Value(v1 == v2))
                    }
                    (e1, e2) => {
                        if e1.eq(&e2) {
                            Ok(BooleanExpression::Value(true))
                        } else {
                            Ok(BooleanExpression::BoolEq(box e1, box e2))
                        }
                    }
                }
            }
            BooleanExpression::Or(box e1, box e2) => {
                match (
                    self.fold_boolean_expression(e1)?,
                    self.fold_boolean_expression(e2)?,
                ) {
                    (BooleanExpression::Value(v1), BooleanExpression::Value(v2)) => {
                        Ok(BooleanExpression::Value(v1 || v2))
                    }
                    (_, BooleanExpression::Value(true)) | (BooleanExpression::Value(true), _) => {
                        Ok(BooleanExpression::Value(true))
                    }
                    (e, BooleanExpression::Value(false)) | (BooleanExpression::Value(false), e) => {
                        Ok(e)
                    }
                    (e1, e2) => Ok(BooleanExpression::Or(box e1, box e2)),
                }
            }
            BooleanExpression::And(box e1, box e2) => {
                match (
                    self.fold_boolean_expression(e1)?,
                    self.fold_boolean_expression(e2)?,
                ) {
                    (BooleanExpression::Value(true), e) | (e, BooleanExpression::Value(true)) => {
                        Ok(e)
                    }
                    (BooleanExpression::Value(false), _) | (_, BooleanExpression::Value(false)) => {
                        Ok(BooleanExpression::Value(false))
                    }
                    (e1, e2) => Ok(BooleanExpression::And(box e1, box e2)),
                }
            }
            BooleanExpression::Not(box e) => match self.fold_boolean_expression(e)? {
                BooleanExpression::Value(v) => Ok(BooleanExpression::Value(!v)),
                e => Ok(BooleanExpression::Not(box e)),
            },
            BooleanExpression::Conditional(box condition, box consequence, box alternative) => {
                let condition = self.fold_boolean_expression(condition)?;
                let consequence = self.fold_boolean_expression(consequence)?;
                let alternative = self.fold_boolean_expression(alternative)?;

                match (condition, consequence, alternative) {
                    (_, consequence, alternative) if consequence == alternative => Ok(consequence),
                    (BooleanExpression::Value(true), consequence, _) => Ok(consequence),
                    (BooleanExpression::Value(false), _, alternative) => Ok(alternative),
                    (condition, consequence, alternative) => Ok(BooleanExpression::Conditional(
                        box condition,
                        box consequence,
                        box alternative,
                    )),
                }
            }
        }
    }

    fn fold_uint_expression_inner(
        &mut self,
        bitwidth: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> Result<UExpressionInner<'ast, T>, Self::Error> {
        match e {
            UExpressionInner::Value(v) => Ok(UExpressionInner::Value(v)),
            UExpressionInner::Identifier(id) => match self.constants.get(&id) {
                Some(ZirExpression::Uint(e)) => Ok(e.as_inner().clone()),
                _ => Ok(UExpressionInner::Identifier(id)),
            },
            UExpressionInner::Select(e, box index) => {
                let index = self.fold_uint_expression(index)?;
                let e: Vec<UExpression<'ast, T>> = e
                    .into_iter()
                    .map(|e| self.fold_uint_expression(e))
                    .collect::<Result<_, _>>()?;

                match index.into_inner() {
                    UExpressionInner::Value(v) => e
                        .get(v as usize)
                        .cloned()
                        .ok_or(Error::OutOfBounds(v as usize, e.len()))
                        .map(|e| e.into_inner()),
                    i => Ok(UExpressionInner::Select(e, box i.annotate(UBitwidth::B32))),
                }
            }
            UExpressionInner::Add(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1)?;
                let e2 = self.fold_uint_expression(e2)?;

                match (e1.into_inner(), e2.into_inner()) {
                    (UExpressionInner::Value(0), e) | (e, UExpressionInner::Value(0)) => Ok(e),
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => Ok(
                        UExpressionInner::Value((n1 + n2) % 2_u128.pow(bitwidth.to_usize() as u32)),
                    ),
                    (e1, e2) => Ok(UExpressionInner::Add(
                        box e1.annotate(bitwidth),
                        box e2.annotate(bitwidth),
                    )),
                }
            }
            UExpressionInner::Sub(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1)?;
                let e2 = self.fold_uint_expression(e2)?;

                match (e1.into_inner(), e2.into_inner()) {
                    (e, UExpressionInner::Value(0)) => Ok(e),
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        Ok(UExpressionInner::Value(
                            n1.wrapping_sub(n2) % 2_u128.pow(bitwidth.to_usize() as u32),
                        ))
                    }
                    (e1, e2) => Ok(UExpressionInner::Sub(
                        box e1.annotate(bitwidth),
                        box e2.annotate(bitwidth),
                    )),
                }
            }
            UExpressionInner::Mult(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1)?;
                let e2 = self.fold_uint_expression(e2)?;

                match (e1.into_inner(), e2.into_inner()) {
                    (_, UExpressionInner::Value(0)) | (UExpressionInner::Value(0), _) => {
                        Ok(UExpressionInner::Value(0))
                    }
                    (e, UExpressionInner::Value(1)) | (UExpressionInner::Value(1), e) => Ok(e),
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => Ok(
                        UExpressionInner::Value((n1 * n2) % 2_u128.pow(bitwidth.to_usize() as u32)),
                    ),
                    (e1, e2) => Ok(UExpressionInner::Mult(
                        box e1.annotate(bitwidth),
                        box e2.annotate(bitwidth),
                    )),
                }
            }
            UExpressionInner::Div(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1)?;
                let e2 = self.fold_uint_expression(e2)?;

                match (e1.into_inner(), e2.into_inner()) {
                    (_, UExpressionInner::Value(n)) if n == 0 => Err(Error::DivisionByZero),
                    (e, UExpressionInner::Value(n)) if n == 1 => Ok(e),
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => Ok(
                        UExpressionInner::Value((n1 / n2) % 2_u128.pow(bitwidth.to_usize() as u32)),
                    ),
                    (e1, e2) => Ok(UExpressionInner::Div(
                        box e1.annotate(bitwidth),
                        box e2.annotate(bitwidth),
                    )),
                }
            }
            UExpressionInner::Rem(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1)?;
                let e2 = self.fold_uint_expression(e2)?;

                match (e1.into_inner(), e2.into_inner()) {
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => Ok(
                        UExpressionInner::Value((n1 % n2) % 2_u128.pow(bitwidth.to_usize() as u32)),
                    ),
                    (e1, e2) => Ok(UExpressionInner::Rem(
                        box e1.annotate(bitwidth),
                        box e2.annotate(bitwidth),
                    )),
                }
            }
            UExpressionInner::Xor(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1)?;
                let e2 = self.fold_uint_expression(e2)?;

                match (e1.into_inner(), e2.into_inner()) {
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        Ok(UExpressionInner::Value(n1 ^ n2))
                    }
                    (e1, e2) if e1.eq(&e2) => Ok(UExpressionInner::Value(0)),
                    (e1, e2) => Ok(UExpressionInner::Xor(
                        box e1.annotate(bitwidth),
                        box e2.annotate(bitwidth),
                    )),
                }
            }
            UExpressionInner::And(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1)?;
                let e2 = self.fold_uint_expression(e2)?;

                match (e1.into_inner(), e2.into_inner()) {
                    (e, UExpressionInner::Value(n)) | (UExpressionInner::Value(n), e)
                        if n == 2_u128.pow(bitwidth.to_usize() as u32) - 1 =>
                    {
                        Ok(e)
                    }
                    (_, UExpressionInner::Value(0)) | (UExpressionInner::Value(0), _) => {
                        Ok(UExpressionInner::Value(0))
                    }
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        Ok(UExpressionInner::Value(n1 & n2))
                    }
                    (e1, e2) => Ok(UExpressionInner::And(
                        box e1.annotate(bitwidth),
                        box e2.annotate(bitwidth),
                    )),
                }
            }
            UExpressionInner::Or(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1)?;
                let e2 = self.fold_uint_expression(e2)?;

                match (e1.into_inner(), e2.into_inner()) {
                    (e, UExpressionInner::Value(0)) | (UExpressionInner::Value(0), e) => Ok(e),
                    (_, UExpressionInner::Value(n)) | (UExpressionInner::Value(n), _)
                        if n == 2_u128.pow(bitwidth.to_usize() as u32) - 1 =>
                    {
                        Ok(UExpressionInner::Value(n))
                    }
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        Ok(UExpressionInner::Value(n1 | n2))
                    }
                    (e1, e2) => Ok(UExpressionInner::Or(
                        box e1.annotate(bitwidth),
                        box e2.annotate(bitwidth),
                    )),
                }
            }
            UExpressionInner::LeftShift(box e, by) => {
                let e = self.fold_uint_expression(e)?;
                match (e.into_inner(), by) {
                    (e, 0) => Ok(e),
                    (_, by) if by >= bitwidth as u32 => Ok(UExpressionInner::Value(0)),
                    (UExpressionInner::Value(n), by) => Ok(UExpressionInner::Value(
                        (n << by) & (2_u128.pow(bitwidth as u32) - 1),
                    )),
                    (e, by) => Ok(UExpressionInner::LeftShift(box e.annotate(bitwidth), by)),
                }
            }
            UExpressionInner::RightShift(box e, by) => {
                let e = self.fold_uint_expression(e)?;
                match (e.into_inner(), by) {
                    (e, 0) => Ok(e),
                    (_, by) if by >= bitwidth as u32 => Ok(UExpressionInner::Value(0)),
                    (UExpressionInner::Value(n), by) => Ok(UExpressionInner::Value(n >> by)),
                    (e, by) => Ok(UExpressionInner::RightShift(box e.annotate(bitwidth), by)),
                }
            }
            UExpressionInner::Not(box e) => {
                let e = self.fold_uint_expression(e)?;
                match e.into_inner() {
                    UExpressionInner::Value(n) => Ok(UExpressionInner::Value(
                        !n & (2_u128.pow(bitwidth as u32) - 1),
                    )),
                    e => Ok(UExpressionInner::Not(box e.annotate(bitwidth))),
                }
            }
            UExpressionInner::Conditional(box condition, box consequence, box alternative) => {
                let condition = self.fold_boolean_expression(condition)?;
                let consequence = self.fold_uint_expression(consequence)?.into_inner();
                let alternative = self.fold_uint_expression(alternative)?.into_inner();

                match (condition, consequence, alternative) {
                    (_, consequence, alternative) if consequence == alternative => Ok(consequence),
                    (BooleanExpression::Value(true), consequence, _) => Ok(consequence),
                    (BooleanExpression::Value(false), _, alternative) => Ok(alternative),
                    (condition, consequence, alternative) => Ok(UExpressionInner::Conditional(
                        box condition,
                        box consequence.annotate(bitwidth),
                        box alternative.annotate(bitwidth),
                    )),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_ast::zir::RuntimeError;
    use zokrates_field::Bn128Field;

    #[test]
    fn propagation() {
        // assert([x, 1] == [y, 1])
        let statements = vec![ZirStatement::Assertion(
            BooleanExpression::And(
                box BooleanExpression::FieldEq(
                    box FieldElementExpression::Identifier("x".into()),
                    box FieldElementExpression::Identifier("y".into()),
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
                    box FieldElementExpression::Identifier("x".into()),
                    box FieldElementExpression::Identifier("y".into()),
                ),
                RuntimeError::mock()
            )]
        );
    }

    #[cfg(test)]
    mod field {
        use super::*;

        #[test]
        fn select() {
            let mut propagator = ZirPropagator::default();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Select(
                    vec![
                        FieldElementExpression::Number(Bn128Field::from(1)),
                        FieldElementExpression::Number(Bn128Field::from(2)),
                    ],
                    box UExpressionInner::Value(1).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(2)))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Select(
                    vec![
                        FieldElementExpression::Number(Bn128Field::from(1)),
                        FieldElementExpression::Number(Bn128Field::from(2)),
                    ],
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
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
                    box FieldElementExpression::Identifier("a".into()),
                    box FieldElementExpression::Number(Bn128Field::from(0)),
                )),
                Ok(FieldElementExpression::Identifier("a".into()))
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
                    box FieldElementExpression::Identifier("a".into()),
                    box FieldElementExpression::Number(Bn128Field::from(0)),
                )),
                Ok(FieldElementExpression::Identifier("a".into()))
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
                    box FieldElementExpression::Identifier("a".into()),
                    box FieldElementExpression::Number(Bn128Field::from(0)),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(0)))
            );

            // a * 1 = a
            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Mult(
                    box FieldElementExpression::Identifier("a".into()),
                    box FieldElementExpression::Number(Bn128Field::from(1)),
                )),
                Ok(FieldElementExpression::Identifier("a".into()))
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
                    box FieldElementExpression::Identifier("a".into()),
                    box FieldElementExpression::Number(Bn128Field::from(1)),
                )),
                Ok(FieldElementExpression::Identifier("a".into()))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Div(
                    box FieldElementExpression::Identifier("a".into()),
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
                    box FieldElementExpression::Identifier("a".into()),
                    box UExpressionInner::Value(0).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(1)))
            );

            // a ** 1 = a
            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Pow(
                    box FieldElementExpression::Identifier("a".into()),
                    box UExpressionInner::Value(1).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::Identifier("a".into()))
            );
        }

        #[test]
        fn if_else() {
            let mut propagator = ZirPropagator::default();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Conditional(
                    box BooleanExpression::Value(true),
                    box FieldElementExpression::Number(Bn128Field::from(1)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(1)))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Conditional(
                    box BooleanExpression::Value(false),
                    box FieldElementExpression::Number(Bn128Field::from(1)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(2)))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Conditional(
                    box BooleanExpression::Identifier("a".into()),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(2)))
            );
        }
    }

    #[cfg(test)]
    mod bool {
        use super::*;

        #[test]
        fn select() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::Select(
                    vec![
                        BooleanExpression::Value(false),
                        BooleanExpression::Value(true),
                    ],
                    box UExpressionInner::Value(1).annotate(UBitwidth::B32),
                )),
                Ok(BooleanExpression::Value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::Select(
                    vec![
                        BooleanExpression::Value(false),
                        BooleanExpression::Value(true),
                    ],
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
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
                Ok(BooleanExpression::Value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldLt(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                )),
                Ok(BooleanExpression::Value(false))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldLt(
                    box FieldElementExpression::Identifier("a".into()),
                    box FieldElementExpression::Number(Bn128Field::from(0)),
                )),
                Ok(BooleanExpression::Value(false))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldLt(
                    box FieldElementExpression::Number(Bn128Field::max_value()),
                    box FieldElementExpression::Identifier("a".into()),
                )),
                Ok(BooleanExpression::Value(false))
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
                Ok(BooleanExpression::Value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldLe(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                )),
                Ok(BooleanExpression::Value(true))
            );
        }

        #[test]
        fn field_ge() {
            let mut propagator = ZirPropagator::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldGe(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                )),
                Ok(BooleanExpression::Value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldGe(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                )),
                Ok(BooleanExpression::Value(true))
            );
        }

        #[test]
        fn field_gt() {
            let mut propagator = ZirPropagator::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldGt(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                )),
                Ok(BooleanExpression::Value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldGt(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                )),
                Ok(BooleanExpression::Value(false))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldGt(
                    box FieldElementExpression::Number(Bn128Field::from(0)),
                    box FieldElementExpression::Identifier("a".into()),
                )),
                Ok(BooleanExpression::Value(false))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldGt(
                    box FieldElementExpression::Identifier("a".into()),
                    box FieldElementExpression::Number(Bn128Field::max_value()),
                )),
                Ok(BooleanExpression::Value(false))
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
                Ok(BooleanExpression::Value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldEq(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                )),
                Ok(BooleanExpression::Value(false))
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
                Ok(BooleanExpression::Value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::UintLt(
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                )),
                Ok(BooleanExpression::Value(false))
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
                Ok(BooleanExpression::Value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::UintLe(
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                )),
                Ok(BooleanExpression::Value(true))
            );
        }

        #[test]
        fn uint_ge() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::UintGe(
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                )),
                Ok(BooleanExpression::Value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::UintGe(
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                )),
                Ok(BooleanExpression::Value(true))
            );
        }

        #[test]
        fn uint_gt() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::UintGt(
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                )),
                Ok(BooleanExpression::Value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::UintGt(
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                )),
                Ok(BooleanExpression::Value(false))
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
                Ok(BooleanExpression::Value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::UintEq(
                    box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                )),
                Ok(BooleanExpression::Value(false))
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
                Ok(BooleanExpression::Value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::BoolEq(
                    box BooleanExpression::Value(true),
                    box BooleanExpression::Value(false),
                )),
                Ok(BooleanExpression::Value(false))
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
                Ok(BooleanExpression::Value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::And(
                    box BooleanExpression::Value(true),
                    box BooleanExpression::Value(false),
                )),
                Ok(BooleanExpression::Value(false))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::And(
                    box BooleanExpression::Identifier("a".into()),
                    box BooleanExpression::Value(true),
                )),
                Ok(BooleanExpression::Identifier("a".into()))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::And(
                    box BooleanExpression::Identifier("a".into()),
                    box BooleanExpression::Value(false),
                )),
                Ok(BooleanExpression::Value(false))
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
                Ok(BooleanExpression::Value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::Or(
                    box BooleanExpression::Value(true),
                    box BooleanExpression::Value(false),
                )),
                Ok(BooleanExpression::Value(true))
            );
        }

        #[test]
        fn not() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::Not(
                    box BooleanExpression::Value(true),
                )),
                Ok(BooleanExpression::Value(false))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::Not(
                    box BooleanExpression::Value(false),
                )),
                Ok(BooleanExpression::Value(true))
            );
        }

        #[test]
        fn if_else() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::Conditional(
                    box BooleanExpression::Value(true),
                    box BooleanExpression::Value(true),
                    box BooleanExpression::Value(false)
                )),
                Ok(BooleanExpression::Value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::Conditional(
                    box BooleanExpression::Value(false),
                    box BooleanExpression::Value(true),
                    box BooleanExpression::Value(false)
                )),
                Ok(BooleanExpression::Value(false))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::Conditional(
                    box BooleanExpression::Identifier("a".into()),
                    box BooleanExpression::Value(true),
                    box BooleanExpression::Value(true)
                )),
                Ok(BooleanExpression::Value(true))
            );
        }
    }

    #[cfg(test)]
    mod uint {
        use super::*;

        #[test]
        fn select() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Select(
                        vec![
                            UExpressionInner::Value(1).annotate(UBitwidth::B32),
                            UExpressionInner::Value(2).annotate(UBitwidth::B32),
                        ],
                        box UExpressionInner::Value(1).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Value(2))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Select(
                        vec![
                            UExpressionInner::Value(1).annotate(UBitwidth::B32),
                            UExpressionInner::Value(2).annotate(UBitwidth::B32),
                        ],
                        box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    )
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
                        box UExpressionInner::Identifier("a".into()).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(0).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Identifier("a".into()))
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
                        box UExpressionInner::Identifier("a".into()).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(0).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Identifier("a".into()))
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
                        box UExpressionInner::Identifier("a".into()).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(1).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Identifier("a".into()))
            );

            // a * 0 = 0
            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Mult(
                        box UExpressionInner::Identifier("a".into()).annotate(UBitwidth::B32),
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
                        box UExpressionInner::Identifier("a".into()).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(1).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Identifier("a".into()))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Div(
                        box UExpressionInner::Identifier("a".into()).annotate(UBitwidth::B32),
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
                        box UExpressionInner::Identifier("a".into()).annotate(UBitwidth::B32),
                        box UExpressionInner::Identifier("a".into()).annotate(UBitwidth::B32),
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
                        box UExpressionInner::Identifier("a".into()).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(0).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Value(0))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::And(
                        box UExpressionInner::Identifier("a".into()).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(u32::MAX as u128).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Identifier("a".into()))
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
                        box UExpressionInner::Identifier("a".into()).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(0).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Identifier("a".into()))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Or(
                        box UExpressionInner::Identifier("a".into()).annotate(UBitwidth::B32),
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
                    UExpressionInner::Conditional(
                        box BooleanExpression::Value(true),
                        box UExpressionInner::Value(1).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Value(1))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Conditional(
                        box BooleanExpression::Value(false),
                        box UExpressionInner::Value(1).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Value(2))
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Conditional(
                        box BooleanExpression::Identifier("a".into()),
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    )
                ),
                Ok(UExpressionInner::Value(2))
            );
        }
    }
}
