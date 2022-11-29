use num::traits::Pow;
use num_bigint::BigUint;
use std::collections::HashMap;
use std::fmt;
use std::ops::{BitAnd, BitOr, BitXor, Shl, Shr, Sub};
use zokrates_ast::zir::types::UBitwidth;
use zokrates_ast::zir::{
    result_folder::*, Conditional, ConditionalExpression, ConditionalOrExpression, Expr, Id,
    IdentifierExpression, IdentifierOrExpression, SelectExpression, SelectOrExpression,
    ZirAssemblyStatement,
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
            Error::AssertionFailed(err) => write!(f, "Assertion failed: `{}`", err),
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

    fn fold_assembly_statement(
        &mut self,
        s: ZirAssemblyStatement<'ast, T>,
    ) -> Result<Vec<ZirAssemblyStatement<'ast, T>>, Self::Error> {
        match s {
            ZirAssemblyStatement::Assignment(assignee, function) => {
                let function = self.fold_function(function)?;

                if function.statements.len() == 1 {
                    let value = match &function.statements.last().unwrap() {
                        ZirStatement::Return(values) => {
                            assert_eq!(values.len(), 1);
                            match values[0].clone() {
                                ZirExpression::FieldElement(FieldElementExpression::Number(v)) => {
                                    Some(v)
                                }
                                _ => None,
                            }
                        }
                        _ => None,
                    };

                    match value {
                        Some(v) => {
                            self.constants
                                .insert(assignee.id, FieldElementExpression::Number(v).into());
                            Ok(vec![])
                        }
                        None => Ok(vec![ZirAssemblyStatement::Assignment(assignee, function)]),
                    }
                } else {
                    Ok(vec![ZirAssemblyStatement::Assignment(assignee, function)])
                }
            }
            ZirAssemblyStatement::Constraint(left, right) => {
                let left = self.fold_field_expression(left)?;
                let right = self.fold_field_expression(right)?;

                // a bit hacky, but we use a fake boolean expression to check this
                let is_equal = BooleanExpression::FieldEq(box left.clone(), box right.clone());
                let is_equal = self.fold_boolean_expression(is_equal)?;

                match is_equal {
                    BooleanExpression::Value(true) => Ok(vec![]),
                    BooleanExpression::Value(false) => {
                        Err(Error::AssertionFailed(RuntimeError::SourceAssertion(
                            format!("In asm block: `{} !== {}`", left, right),
                        )))
                    }
                    _ => Ok(vec![ZirAssemblyStatement::Constraint(left, right)]),
                }
            }
        }
    }

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
            ZirStatement::Assembly(statements) => {
                let statements: Vec<_> = statements
                    .into_iter()
                    .map(|s| self.fold_assembly_statement(s))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .flatten()
                    .collect();
                match statements.len() {
                    0 => Ok(vec![]),
                    _ => Ok(vec![ZirStatement::Assembly(statements)]),
                }
            }
            _ => fold_statement(self, s),
        }
    }

    fn fold_identifier_expression<E: Expr<'ast, T> + Id<'ast, T> + ResultFold<'ast, T>>(
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
            FieldElementExpression::Xor(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1)?;
                let e2 = self.fold_field_expression(e2)?;

                match (e1, e2) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        Ok(FieldElementExpression::Number(
                            T::try_from(n1.to_biguint().bitxor(n2.to_biguint())).unwrap(),
                        ))
                    }
                    (e1, e2) if e1.eq(&e2) => Ok(FieldElementExpression::Number(T::from(0))),
                    (e1, e2) => Ok(FieldElementExpression::Xor(box e1, box e2)),
                }
            }
            FieldElementExpression::And(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1)?;
                let e2 = self.fold_field_expression(e2)?;

                match (e1, e2) {
                    (_, FieldElementExpression::Number(n))
                    | (FieldElementExpression::Number(n), _)
                        if n == T::from(0) =>
                    {
                        Ok(FieldElementExpression::Number(n))
                    }
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        Ok(FieldElementExpression::Number(
                            T::try_from(n1.to_biguint().bitand(n2.to_biguint())).unwrap(),
                        ))
                    }
                    (e1, e2) => Ok(FieldElementExpression::And(box e1, box e2)),
                }
            }
            FieldElementExpression::Or(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1)?;
                let e2 = self.fold_field_expression(e2)?;

                match (e1, e2) {
                    (e, FieldElementExpression::Number(n))
                    | (FieldElementExpression::Number(n), e)
                        if n == T::from(0) =>
                    {
                        Ok(e)
                    }
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        Ok(FieldElementExpression::Number(
                            T::try_from(n1.to_biguint().bitor(n2.to_biguint())).unwrap(),
                        ))
                    }
                    (e1, e2) => Ok(FieldElementExpression::Or(box e1, box e2)),
                }
            }
            FieldElementExpression::LeftShift(box e, box by) => {
                let e = self.fold_field_expression(e)?;
                let by = self.fold_uint_expression(by)?;
                match (e, by) {
                    (
                        e,
                        UExpression {
                            inner: UExpressionInner::Value(by),
                            ..
                        },
                    ) if by == 0 => Ok(e),
                    (
                        _,
                        UExpression {
                            inner: UExpressionInner::Value(by),
                            ..
                        },
                    ) if by as usize >= T::get_required_bits() => {
                        Ok(FieldElementExpression::Number(T::from(0)))
                    }
                    (
                        FieldElementExpression::Number(n),
                        UExpression {
                            inner: UExpressionInner::Value(by),
                            ..
                        },
                    ) => {
                        let two = BigUint::from(2usize);
                        let mask: BigUint = two.pow(T::get_required_bits()).sub(1usize);

                        Ok(FieldElementExpression::Number(
                            T::try_from(n.to_biguint().shl(by as usize).bitand(mask)).unwrap(),
                        ))
                    }
                    (e, by) => Ok(FieldElementExpression::LeftShift(box e, box by)),
                }
            }
            FieldElementExpression::RightShift(box e, box by) => {
                let e = self.fold_field_expression(e)?;
                let by = self.fold_uint_expression(by)?;
                match (e, by) {
                    (
                        e,
                        UExpression {
                            inner: UExpressionInner::Value(by),
                            ..
                        },
                    ) if by == 0 => Ok(e),
                    (
                        _,
                        UExpression {
                            inner: UExpressionInner::Value(by),
                            ..
                        },
                    ) if by as usize >= T::get_required_bits() => {
                        Ok(FieldElementExpression::Number(T::from(0)))
                    }
                    (
                        FieldElementExpression::Number(n),
                        UExpression {
                            inner: UExpressionInner::Value(by),
                            ..
                        },
                    ) => Ok(FieldElementExpression::Number(
                        T::try_from(n.to_biguint().shr(by as usize)).unwrap(),
                    )),
                    (e, by) => Ok(FieldElementExpression::RightShift(box e, box by)),
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
            e => fold_boolean_expression(self, e),
        }
    }

    fn fold_select_expression<
        E: Clone + Expr<'ast, T> + ResultFold<'ast, T> + zokrates_ast::zir::Select<'ast, T>,
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
                .get(*v as usize)
                .cloned()
                .ok_or(Error::OutOfBounds(*v as usize, array.len()))
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
            e => fold_uint_expression_inner(self, bitwidth, e),
        }
    }

    fn fold_conditional_expression<
        E: Expr<'ast, T> + ResultFold<'ast, T> + Conditional<'ast, T>,
    >(
        &mut self,
        _: &E::Ty,
        e: ConditionalExpression<'ast, T, E>,
    ) -> Result<ConditionalOrExpression<'ast, T, E>, Self::Error> {
        let condition = self.fold_boolean_expression(*e.condition)?;

        match condition {
            BooleanExpression::Value(true) => Ok(ConditionalOrExpression::Expression(
                e.consequence.fold(self)?.into_inner(),
            )),
            BooleanExpression::Value(false) => Ok(ConditionalOrExpression::Expression(
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
        fn left_shift() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::LeftShift(
                    box FieldElementExpression::identifier("a".into()),
                    box UExpressionInner::Value(0).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::identifier("a".into()))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::LeftShift(
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                    box UExpressionInner::Value(2 as u128).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(8)))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::LeftShift(
                    box FieldElementExpression::Number(Bn128Field::from(1)),
                    box UExpressionInner::Value((Bn128Field::get_required_bits() - 1) as u128).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::try_from_dec_str("14474011154664524427946373126085988481658748083205070504932198000989141204992").unwrap()))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::LeftShift(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box UExpressionInner::Value((Bn128Field::get_required_bits() - 3) as u128).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::try_from_dec_str("10855508365998393320959779844564491361244061062403802878699148500741855903744").unwrap()))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::LeftShift(
                    box FieldElementExpression::Number(Bn128Field::from(1)),
                    box UExpressionInner::Value((Bn128Field::get_required_bits()) as u128)
                        .annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(0)))
            );
        }

        #[test]
        fn right_shift() {
            let mut propagator = ZirPropagator::<Bn128Field>::default();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::RightShift(
                    box FieldElementExpression::identifier("a".into()),
                    box UExpressionInner::Value(0).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::identifier("a".into()))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::RightShift(
                    box FieldElementExpression::identifier("a".into()),
                    box UExpressionInner::Value(Bn128Field::get_required_bits() as u128)
                        .annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(0)))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::RightShift(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box UExpressionInner::Value(1 as u128).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(1)))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::RightShift(
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                    box UExpressionInner::Value(2 as u128).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(0)))
            );
            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::RightShift(
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                    box UExpressionInner::Value(4 as u128).annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(0)))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::RightShift(
                    box FieldElementExpression::Number(Bn128Field::max_value()),
                    box UExpressionInner::Value((Bn128Field::get_required_bits() - 1) as u128)
                        .annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(1)))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::RightShift(
                    box FieldElementExpression::Number(Bn128Field::max_value()),
                    box UExpressionInner::Value(Bn128Field::get_required_bits() as u128)
                        .annotate(UBitwidth::B32),
                )),
                Ok(FieldElementExpression::Number(Bn128Field::from(0)))
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
                Ok(BooleanExpression::Value(true))
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
                    box FieldElementExpression::identifier("a".into()),
                    box FieldElementExpression::Number(Bn128Field::from(0)),
                )),
                Ok(BooleanExpression::Value(false))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldLt(
                    box FieldElementExpression::Number(Bn128Field::max_value()),
                    box FieldElementExpression::identifier("a".into()),
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
                propagator.fold_boolean_expression(BooleanExpression::conditional(
                    BooleanExpression::Value(true),
                    BooleanExpression::Value(true),
                    BooleanExpression::Value(false)
                )),
                Ok(BooleanExpression::Value(true))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::conditional(
                    BooleanExpression::Value(false),
                    BooleanExpression::Value(true),
                    BooleanExpression::Value(false)
                )),
                Ok(BooleanExpression::Value(false))
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::conditional(
                    BooleanExpression::identifier("a".into()),
                    BooleanExpression::Value(true),
                    BooleanExpression::Value(true)
                )),
                Ok(BooleanExpression::Value(true))
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
