use crate::zir::folder::fold_statement;
use crate::zir::types::UBitwidth;
use crate::zir::{
    BooleanExpression, FieldElementExpression, Folder, UExpression, UExpressionInner, Variable,
    ZirExpression, ZirProgram, ZirStatement,
};
use std::collections::HashMap;
use zokrates_field::Field;

type Constants<'ast, T> = HashMap<Variable<'ast>, ZirExpression<'ast, T>>;

#[derive(Default)]
pub struct ZirPropagator<'ast, T> {
    constants: Constants<'ast, T>,
}

impl<'ast, T: Field> ZirPropagator<'ast, T> {
    pub fn new() -> Self {
        ZirPropagator::default()
    }
    pub fn propagate(p: ZirProgram<T>) -> ZirProgram<T> {
        ZirPropagator::new().fold_program(p)
    }
}

impl<'ast, T: Field> Folder<'ast, T> for ZirPropagator<'ast, T> {
    fn fold_statement(&mut self, s: ZirStatement<'ast, T>) -> Vec<ZirStatement<'ast, T>> {
        match s {
            ZirStatement::Assertion(e) => match self.fold_boolean_expression(e) {
                BooleanExpression::Value(true) => vec![],
                e => vec![ZirStatement::Assertion(e)],
            },
            ZirStatement::Definition(a, e) => {
                let e = self.fold_expression(e);
                match e {
                    ZirExpression::FieldElement(FieldElementExpression::Number(..))
                    | ZirExpression::Boolean(BooleanExpression::Value(..))
                    | ZirExpression::Uint(UExpression {
                        inner: UExpressionInner::Value(..),
                        ..
                    }) => {
                        self.constants.insert(a, e);
                        vec![]
                    }
                    _ => {
                        self.constants.remove(&a);
                        vec![ZirStatement::Definition(a, e)]
                    }
                }
            }
            ZirStatement::MultipleDefinition(assignees, list) => {
                for a in &assignees {
                    self.constants.remove(a);
                }
                vec![ZirStatement::MultipleDefinition(
                    assignees,
                    self.fold_expression_list(list),
                )]
            }
            _ => fold_statement(self, s),
        }
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        match e {
            FieldElementExpression::Number(n) => FieldElementExpression::Number(n),
            FieldElementExpression::Identifier(id) => {
                match self.constants.get(&Variable::field_element(id.clone())) {
                    Some(ZirExpression::FieldElement(FieldElementExpression::Number(v))) => {
                        FieldElementExpression::Number(v.clone())
                    }
                    _ => FieldElementExpression::Identifier(id),
                }
            }
            FieldElementExpression::Select(e, box index) => {
                let index = self.fold_uint_expression(index);
                let e: Vec<FieldElementExpression<'ast, T>> = e
                    .into_iter()
                    .map(|e| self.fold_field_expression(e))
                    .collect();

                match index.into_inner() {
                    UExpressionInner::Value(v) => {
                        e.get(v as usize).cloned().expect("index out of bounds")
                    }
                    i => FieldElementExpression::Select(e, box i.annotate(UBitwidth::B32)),
                }
            }
            FieldElementExpression::Add(box e1, box e2) => {
                match (
                    self.fold_field_expression(e1),
                    self.fold_field_expression(e2),
                ) {
                    (FieldElementExpression::Number(n), e)
                    | (e, FieldElementExpression::Number(n))
                        if n == T::from(0) =>
                    {
                        e
                    }
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        FieldElementExpression::Number(n1 + n2)
                    }
                    (e1, e2) => FieldElementExpression::Add(box e1, box e2),
                }
            }
            FieldElementExpression::Sub(box e1, box e2) => {
                match (
                    self.fold_field_expression(e1),
                    self.fold_field_expression(e2),
                ) {
                    (e, FieldElementExpression::Number(n)) if n == T::from(0) => e,
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        FieldElementExpression::Number(n1 - n2)
                    }
                    (e1, e2) => FieldElementExpression::Sub(box e1, box e2),
                }
            }
            FieldElementExpression::Mult(box e1, box e2) => {
                match (
                    self.fold_field_expression(e1),
                    self.fold_field_expression(e2),
                ) {
                    (FieldElementExpression::Number(n), _)
                    | (_, FieldElementExpression::Number(n))
                        if n == T::from(0) =>
                    {
                        FieldElementExpression::Number(T::from(0))
                    }
                    (FieldElementExpression::Number(n), e)
                    | (e, FieldElementExpression::Number(n))
                        if n == T::from(1) =>
                    {
                        e
                    }
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        FieldElementExpression::Number(n1 * n2)
                    }
                    (e1, e2) => FieldElementExpression::Mult(box e1, box e2),
                }
            }
            FieldElementExpression::Div(box e1, box e2) => {
                match (
                    self.fold_field_expression(e1),
                    self.fold_field_expression(e2),
                ) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        FieldElementExpression::Number(n1 / n2)
                    }
                    (e1, e2) => FieldElementExpression::Div(box e1, box e2),
                }
            }
            FieldElementExpression::Pow(box e, box exponent) => {
                let exponent = self.fold_uint_expression(exponent);
                match (self.fold_field_expression(e), exponent.into_inner()) {
                    (_, UExpressionInner::Value(n2)) if n2 == 0 => {
                        FieldElementExpression::Number(T::from(1))
                    }
                    (e, UExpressionInner::Value(n2)) if n2 == 1 => e,
                    (FieldElementExpression::Number(n), UExpressionInner::Value(e)) => {
                        FieldElementExpression::Number(n.pow(e as usize))
                    }
                    (e, exp) => {
                        FieldElementExpression::Pow(box e, box exp.annotate(UBitwidth::B32))
                    }
                }
            }
            FieldElementExpression::IfElse(box condition, box consequence, box alternative) => {
                let condition = self.fold_boolean_expression(condition);
                let consequence = self.fold_field_expression(consequence);
                let alternative = self.fold_field_expression(alternative);

                match condition {
                    BooleanExpression::Value(true) => consequence,
                    BooleanExpression::Value(false) => alternative,
                    _ => FieldElementExpression::IfElse(
                        box condition,
                        box consequence,
                        box alternative,
                    ),
                }
            }
        }
    }

    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> BooleanExpression<'ast, T> {
        match e {
            BooleanExpression::Value(v) => BooleanExpression::Value(v),
            BooleanExpression::Identifier(id) => {
                match self.constants.get(&Variable::boolean(id.clone())) {
                    Some(ZirExpression::Boolean(BooleanExpression::Value(v))) => {
                        BooleanExpression::Value(*v)
                    }
                    _ => BooleanExpression::Identifier(id),
                }
            }
            BooleanExpression::Select(e, box index) => {
                let index = self.fold_uint_expression(index);
                let e: Vec<BooleanExpression<'ast, T>> = e
                    .into_iter()
                    .map(|e| self.fold_boolean_expression(e))
                    .collect();

                match index.as_inner() {
                    UExpressionInner::Value(v) => {
                        e.get(*v as usize).cloned().expect("index out of bounds")
                    }
                    _ => BooleanExpression::Select(e, box index),
                }
            }
            BooleanExpression::FieldLt(box e1, box e2) => {
                match (
                    self.fold_field_expression(e1),
                    self.fold_field_expression(e2),
                ) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        BooleanExpression::Value(n1 < n2)
                    }
                    (e1, e2) => BooleanExpression::FieldLt(box e1, box e2),
                }
            }
            BooleanExpression::FieldLe(box e1, box e2) => {
                match (
                    self.fold_field_expression(e1),
                    self.fold_field_expression(e2),
                ) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        BooleanExpression::Value(n1 <= n2)
                    }
                    (e1, e2) => BooleanExpression::FieldLe(box e1, box e2),
                }
            }
            BooleanExpression::FieldGe(box e1, box e2) => {
                match (
                    self.fold_field_expression(e1),
                    self.fold_field_expression(e2),
                ) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        BooleanExpression::Value(n1 >= n2)
                    }
                    (e1, e2) => BooleanExpression::FieldGe(box e1, box e2),
                }
            }
            BooleanExpression::FieldGt(box e1, box e2) => {
                match (
                    self.fold_field_expression(e1),
                    self.fold_field_expression(e2),
                ) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        BooleanExpression::Value(n1 > n2)
                    }
                    (e1, e2) => BooleanExpression::FieldGt(box e1, box e2),
                }
            }
            BooleanExpression::FieldEq(box e1, box e2) => {
                match (
                    self.fold_field_expression(e1),
                    self.fold_field_expression(e2),
                ) {
                    (FieldElementExpression::Number(v1), FieldElementExpression::Number(v2)) => {
                        BooleanExpression::Value(v1.eq(&v2))
                    }
                    (e1, e2) => {
                        if e1.eq(&e2) {
                            BooleanExpression::Value(true)
                        } else {
                            BooleanExpression::FieldEq(box e1, box e2)
                        }
                    }
                }
            }
            BooleanExpression::UintLt(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1);
                let e2 = self.fold_uint_expression(e2);

                match (e1.as_inner(), e2.as_inner()) {
                    (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                        BooleanExpression::Value(v1 < v2)
                    }
                    _ => BooleanExpression::UintLt(box e1, box e2),
                }
            }
            BooleanExpression::UintLe(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1);
                let e2 = self.fold_uint_expression(e2);

                match (e1.as_inner(), e2.as_inner()) {
                    (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                        BooleanExpression::Value(v1 <= v2)
                    }
                    _ => BooleanExpression::UintLe(box e1, box e2),
                }
            }
            BooleanExpression::UintGe(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1);
                let e2 = self.fold_uint_expression(e2);

                match (e1.as_inner(), e2.as_inner()) {
                    (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                        BooleanExpression::Value(v1 >= v2)
                    }
                    _ => BooleanExpression::UintGe(box e1, box e2),
                }
            }
            BooleanExpression::UintGt(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1);
                let e2 = self.fold_uint_expression(e2);

                match (e1.as_inner(), e2.as_inner()) {
                    (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                        BooleanExpression::Value(v1 > v2)
                    }
                    _ => BooleanExpression::UintGt(box e1, box e2),
                }
            }
            BooleanExpression::UintEq(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1);
                let e2 = self.fold_uint_expression(e2);

                match (e1.as_inner(), e2.as_inner()) {
                    (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                        BooleanExpression::Value(v1 == v2)
                    }
                    _ => {
                        if e1.eq(&e2) {
                            BooleanExpression::Value(true)
                        } else {
                            BooleanExpression::UintEq(box e1, box e2)
                        }
                    }
                }
            }
            BooleanExpression::BoolEq(box e1, box e2) => {
                match (
                    self.fold_boolean_expression(e1),
                    self.fold_boolean_expression(e2),
                ) {
                    (BooleanExpression::Value(v1), BooleanExpression::Value(v2)) => {
                        BooleanExpression::Value(v1 == v2)
                    }
                    (e1, e2) => {
                        if e1.eq(&e2) {
                            BooleanExpression::Value(true)
                        } else {
                            BooleanExpression::BoolEq(box e1, box e2)
                        }
                    }
                }
            }
            BooleanExpression::Or(box e1, box e2) => {
                match (
                    self.fold_boolean_expression(e1),
                    self.fold_boolean_expression(e2),
                ) {
                    (BooleanExpression::Value(v1), BooleanExpression::Value(v2)) => {
                        BooleanExpression::Value(v1 || v2)
                    }
                    (_, BooleanExpression::Value(true)) | (BooleanExpression::Value(true), _) => {
                        BooleanExpression::Value(true)
                    }
                    (e, BooleanExpression::Value(false)) | (BooleanExpression::Value(false), e) => {
                        e
                    }
                    (e1, e2) => BooleanExpression::Or(box e1, box e2),
                }
            }
            BooleanExpression::And(box e1, box e2) => {
                match (
                    self.fold_boolean_expression(e1),
                    self.fold_boolean_expression(e2),
                ) {
                    (BooleanExpression::Value(true), e) | (e, BooleanExpression::Value(true)) => e,
                    (BooleanExpression::Value(false), _) | (_, BooleanExpression::Value(false)) => {
                        BooleanExpression::Value(false)
                    }
                    (e1, e2) => BooleanExpression::And(box e1, box e2),
                }
            }
            BooleanExpression::Not(box e) => match self.fold_boolean_expression(e) {
                BooleanExpression::Value(v) => BooleanExpression::Value(!v),
                e => BooleanExpression::Not(box e),
            },
            BooleanExpression::IfElse(box condition, box consequence, box alternative) => {
                let condition = self.fold_boolean_expression(condition);
                let consequence = self.fold_boolean_expression(consequence);
                let alternative = self.fold_boolean_expression(alternative);

                match condition {
                    BooleanExpression::Value(true) => consequence,
                    BooleanExpression::Value(false) => alternative,
                    _ => BooleanExpression::IfElse(box condition, box consequence, box alternative),
                }
            }
        }
    }

    fn fold_uint_expression_inner(
        &mut self,
        bitwidth: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> UExpressionInner<'ast, T> {
        match e {
            UExpressionInner::Value(v) => UExpressionInner::Value(v),
            UExpressionInner::Identifier(id) => {
                match self.constants.get(&Variable::uint(id.clone(), bitwidth)) {
                    Some(ZirExpression::Uint(e)) => e.as_inner().clone(),
                    _ => UExpressionInner::Identifier(id),
                }
            }
            UExpressionInner::Select(e, box index) => {
                let index = self.fold_uint_expression(index);
                let e: Vec<UExpression<'ast, T>> = e
                    .into_iter()
                    .map(|e| self.fold_uint_expression(e))
                    .collect();

                match index.into_inner() {
                    UExpressionInner::Value(v) => e
                        .get(v as usize)
                        .cloned()
                        .expect("index out of bounds")
                        .into_inner(),
                    i => UExpressionInner::Select(e, box i.annotate(bitwidth)),
                }
            }
            UExpressionInner::Add(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1);
                let e2 = self.fold_uint_expression(e2);

                match (e1.into_inner(), e2.into_inner()) {
                    (UExpressionInner::Value(0), e) | (e, UExpressionInner::Value(0)) => e,
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        UExpressionInner::Value((n1 + n2) % 2_u128.pow(bitwidth.to_usize() as u32))
                    }
                    (e1, e2) => {
                        UExpressionInner::Add(box e1.annotate(bitwidth), box e2.annotate(bitwidth))
                    }
                }
            }
            UExpressionInner::Sub(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1);
                let e2 = self.fold_uint_expression(e2);

                match (e1.into_inner(), e2.into_inner()) {
                    (e, UExpressionInner::Value(0)) => e,
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        UExpressionInner::Value(
                            n1.wrapping_sub(n2) % 2_u128.pow(bitwidth.to_usize() as u32),
                        )
                    }
                    (e1, e2) => {
                        UExpressionInner::Sub(box e1.annotate(bitwidth), box e2.annotate(bitwidth))
                    }
                }
            }
            UExpressionInner::Mult(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1);
                let e2 = self.fold_uint_expression(e2);

                match (e1.into_inner(), e2.into_inner()) {
                    (_, UExpressionInner::Value(0)) | (UExpressionInner::Value(0), _) => {
                        UExpressionInner::Value(0)
                    }
                    (e, UExpressionInner::Value(1)) | (UExpressionInner::Value(1), e) => e,
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        UExpressionInner::Value((n1 * n2) % 2_u128.pow(bitwidth.to_usize() as u32))
                    }
                    (e1, e2) => {
                        UExpressionInner::Mult(box e1.annotate(bitwidth), box e2.annotate(bitwidth))
                    }
                }
            }
            UExpressionInner::Div(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1);
                let e2 = self.fold_uint_expression(e2);

                match (e1.into_inner(), e2.into_inner()) {
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        UExpressionInner::Value((n1 / n2) % 2_u128.pow(bitwidth.to_usize() as u32))
                    }
                    (e1, e2) => {
                        UExpressionInner::Div(box e1.annotate(bitwidth), box e2.annotate(bitwidth))
                    }
                }
            }
            UExpressionInner::Rem(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1);
                let e2 = self.fold_uint_expression(e2);

                match (e1.into_inner(), e2.into_inner()) {
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        UExpressionInner::Value((n1 % n2) % 2_u128.pow(bitwidth.to_usize() as u32))
                    }
                    (e1, e2) => {
                        UExpressionInner::Rem(box e1.annotate(bitwidth), box e2.annotate(bitwidth))
                    }
                }
            }
            UExpressionInner::Xor(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1);
                let e2 = self.fold_uint_expression(e2);

                match (e1.into_inner(), e2.into_inner()) {
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        UExpressionInner::Value(n1 ^ n2)
                    }
                    (e1, e2) => {
                        UExpressionInner::Xor(box e1.annotate(bitwidth), box e2.annotate(bitwidth))
                    }
                }
            }
            UExpressionInner::And(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1);
                let e2 = self.fold_uint_expression(e2);

                match (e1.into_inner(), e2.into_inner()) {
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        UExpressionInner::Value(n1 & n2)
                    }
                    (e1, e2) => {
                        UExpressionInner::And(box e1.annotate(bitwidth), box e2.annotate(bitwidth))
                    }
                }
            }
            UExpressionInner::Or(box e1, box e2) => {
                let e1 = self.fold_uint_expression(e1);
                let e2 = self.fold_uint_expression(e2);

                match (e1.into_inner(), e2.into_inner()) {
                    (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                        UExpressionInner::Value(n1 | n2)
                    }
                    (e1, e2) => {
                        UExpressionInner::Or(box e1.annotate(bitwidth), box e2.annotate(bitwidth))
                    }
                }
            }
            UExpressionInner::LeftShift(box e, v) => {
                let e = self.fold_uint_expression(e);
                match e.into_inner() {
                    UExpressionInner::Value(n) => {
                        UExpressionInner::Value((n << v) & (2_u128.pow(bitwidth as u32) - 1))
                    }
                    e => UExpressionInner::LeftShift(box e.annotate(bitwidth), v),
                }
            }
            UExpressionInner::RightShift(box e, v) => {
                let e = self.fold_uint_expression(e);
                match e.into_inner() {
                    UExpressionInner::Value(n) => UExpressionInner::Value(n >> v),
                    e => UExpressionInner::RightShift(box e.annotate(bitwidth), v),
                }
            }
            UExpressionInner::Not(box e) => {
                let e = self.fold_uint_expression(e);
                match e.into_inner() {
                    UExpressionInner::Value(n) => {
                        UExpressionInner::Value(!n & (2_u128.pow(bitwidth as u32) - 1))
                    }
                    e => UExpressionInner::Not(box e.annotate(bitwidth)),
                }
            }
            UExpressionInner::IfElse(box condition, box consequence, box alternative) => {
                let condition = self.fold_boolean_expression(condition);
                let consequence = self.fold_uint_expression(consequence).into_inner();
                let alternative = self.fold_uint_expression(alternative).into_inner();

                match condition {
                    BooleanExpression::Value(true) => consequence,
                    BooleanExpression::Value(false) => alternative,
                    _ => UExpressionInner::IfElse(
                        box condition,
                        box consequence.annotate(bitwidth),
                        box alternative.annotate(bitwidth),
                    ),
                }
            }
        }
    }
}
