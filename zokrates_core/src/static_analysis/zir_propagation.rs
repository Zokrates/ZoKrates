use crate::zir::folder::fold_statement;
use crate::zir::types::UBitwidth;
use crate::zir::{
    BooleanExpression, FieldElementExpression, Folder, Identifier, UExpression, UExpressionInner,
    ZirExpression, ZirProgram, ZirStatement,
};
use std::collections::HashMap;
use zokrates_field::Field;

type Constants<'ast, T> = HashMap<Identifier<'ast>, ZirExpression<'ast, T>>;

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
                        self.constants.insert(a.id, e);
                        vec![]
                    }
                    _ => {
                        self.constants.remove(&a.id);
                        vec![ZirStatement::Definition(a, e)]
                    }
                }
            }
            ZirStatement::MultipleDefinition(assignees, list) => {
                for a in &assignees {
                    self.constants.remove(&a.id);
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
            FieldElementExpression::Identifier(id) => match self.constants.get(&id) {
                Some(ZirExpression::FieldElement(FieldElementExpression::Number(v))) => {
                    FieldElementExpression::Number(v.clone())
                }
                _ => FieldElementExpression::Identifier(id),
            },
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
            BooleanExpression::Identifier(id) => match self.constants.get(&id) {
                Some(ZirExpression::Boolean(BooleanExpression::Value(v))) => {
                    BooleanExpression::Value(*v)
                }
                _ => BooleanExpression::Identifier(id),
            },
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
            UExpressionInner::Identifier(id) => match self.constants.get(&id) {
                Some(ZirExpression::Uint(e)) => e.as_inner().clone(),
                _ => UExpressionInner::Identifier(id),
            },
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

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::Bn128Field;

    #[test]
    fn propagation() {
        // assert([x, 1] == [y, 1])
        let statements = vec![ZirStatement::Assertion(BooleanExpression::And(
            box BooleanExpression::FieldEq(
                box FieldElementExpression::Identifier("x".into()),
                box FieldElementExpression::Identifier("y".into()),
            ),
            box BooleanExpression::FieldEq(
                box FieldElementExpression::Number(Bn128Field::from(1)),
                box FieldElementExpression::Number(Bn128Field::from(1)),
            ),
        ))];

        let mut propagator = ZirPropagator::new();
        let statements: Vec<ZirStatement<_>> = statements
            .into_iter()
            .flat_map(|s| propagator.fold_statement(s))
            .collect();

        assert_eq!(
            statements,
            vec![ZirStatement::Assertion(BooleanExpression::FieldEq(
                box FieldElementExpression::Identifier("x".into()),
                box FieldElementExpression::Identifier("y".into()),
            ))]
        );
    }

    #[cfg(test)]
    mod field {
        use super::*;

        #[test]
        fn select() {
            let mut propagator = ZirPropagator::new();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Select(
                    vec![
                        FieldElementExpression::Number(Bn128Field::from(1)),
                        FieldElementExpression::Number(Bn128Field::from(2)),
                    ],
                    box UExpressionInner::Value(1).annotate(UBitwidth::B32),
                )),
                FieldElementExpression::Number(Bn128Field::from(2))
            );
        }

        #[test]
        fn add() {
            let mut propagator = ZirPropagator::new();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Add(
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                )),
                FieldElementExpression::Number(Bn128Field::from(5))
            );

            // a + 0 = a
            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Add(
                    box FieldElementExpression::Identifier("a".into()),
                    box FieldElementExpression::Number(Bn128Field::from(0)),
                )),
                FieldElementExpression::Identifier("a".into())
            );
        }

        #[test]
        fn sub() {
            let mut propagator = ZirPropagator::new();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Sub(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                )),
                FieldElementExpression::Number(Bn128Field::from(1))
            );

            // a - 0 = a
            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Sub(
                    box FieldElementExpression::Identifier("a".into()),
                    box FieldElementExpression::Number(Bn128Field::from(0)),
                )),
                FieldElementExpression::Identifier("a".into())
            );
        }

        #[test]
        fn mult() {
            let mut propagator = ZirPropagator::new();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Mult(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                )),
                FieldElementExpression::Number(Bn128Field::from(6))
            );

            // a * 0 = 0
            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Mult(
                    box FieldElementExpression::Identifier("a".into()),
                    box FieldElementExpression::Number(Bn128Field::from(0)),
                )),
                FieldElementExpression::Number(Bn128Field::from(0))
            );

            // a * 1 = a
            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Mult(
                    box FieldElementExpression::Identifier("a".into()),
                    box FieldElementExpression::Number(Bn128Field::from(1)),
                )),
                FieldElementExpression::Identifier("a".into())
            );
        }

        #[test]
        fn div() {
            let mut propagator = ZirPropagator::new();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Div(
                    box FieldElementExpression::Number(Bn128Field::from(6)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                )),
                FieldElementExpression::Number(Bn128Field::from(3))
            );
        }

        #[test]
        fn pow() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Pow(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                )),
                FieldElementExpression::Number(Bn128Field::from(9))
            );

            // a ** 0 = 1
            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Pow(
                    box FieldElementExpression::Identifier("a".into()),
                    box UExpressionInner::Value(0).annotate(UBitwidth::B32),
                )),
                FieldElementExpression::Number(Bn128Field::from(1))
            );

            // a ** 1 = a
            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::Pow(
                    box FieldElementExpression::Identifier("a".into()),
                    box UExpressionInner::Value(1).annotate(UBitwidth::B32),
                )),
                FieldElementExpression::Identifier("a".into())
            );
        }

        #[test]
        fn if_else() {
            let mut propagator = ZirPropagator::new();

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::IfElse(
                    box BooleanExpression::Value(true),
                    box FieldElementExpression::Number(Bn128Field::from(1)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                )),
                FieldElementExpression::Number(Bn128Field::from(1))
            );

            assert_eq!(
                propagator.fold_field_expression(FieldElementExpression::IfElse(
                    box BooleanExpression::Value(false),
                    box FieldElementExpression::Number(Bn128Field::from(1)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                )),
                FieldElementExpression::Number(Bn128Field::from(2))
            );
        }
    }

    #[cfg(test)]
    mod bool {
        use super::*;

        #[test]
        fn select() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::Select(
                    vec![
                        BooleanExpression::Value(false),
                        BooleanExpression::Value(true),
                    ],
                    box UExpressionInner::Value(1).annotate(UBitwidth::B32),
                )),
                BooleanExpression::Value(true)
            );
        }

        #[test]
        fn field_lt() {
            let mut propagator = ZirPropagator::new();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldLt(
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                )),
                BooleanExpression::Value(true)
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldLt(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                )),
                BooleanExpression::Value(false)
            );
        }

        #[test]
        fn field_le() {
            let mut propagator = ZirPropagator::new();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldLe(
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                )),
                BooleanExpression::Value(true)
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldLe(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                )),
                BooleanExpression::Value(true)
            );
        }

        #[test]
        fn field_ge() {
            let mut propagator = ZirPropagator::new();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldGe(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                )),
                BooleanExpression::Value(true)
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldGe(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                )),
                BooleanExpression::Value(true)
            );
        }

        #[test]
        fn field_gt() {
            let mut propagator = ZirPropagator::new();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldGt(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                )),
                BooleanExpression::Value(true)
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldGt(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                )),
                BooleanExpression::Value(false)
            );
        }

        #[test]
        fn field_eq() {
            let mut propagator = ZirPropagator::new();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldEq(
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                )),
                BooleanExpression::Value(true)
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::FieldEq(
                    box FieldElementExpression::Number(Bn128Field::from(3)),
                    box FieldElementExpression::Number(Bn128Field::from(2)),
                )),
                BooleanExpression::Value(false)
            );
        }

        #[test]
        fn uint_lt() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::UintLt(
                    box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                )),
                BooleanExpression::Value(true)
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::UintLt(
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                )),
                BooleanExpression::Value(false)
            );
        }

        #[test]
        fn uint_le() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::UintLe(
                    box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                )),
                BooleanExpression::Value(true)
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::UintLe(
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                )),
                BooleanExpression::Value(true)
            );
        }

        #[test]
        fn uint_ge() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::UintGe(
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                )),
                BooleanExpression::Value(true)
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::UintGe(
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                )),
                BooleanExpression::Value(true)
            );
        }

        #[test]
        fn uint_gt() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::UintGt(
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                )),
                BooleanExpression::Value(true)
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::UintGt(
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                )),
                BooleanExpression::Value(false)
            );
        }

        #[test]
        fn uint_eq() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::UintEq(
                    box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                )),
                BooleanExpression::Value(true)
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::UintEq(
                    box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                )),
                BooleanExpression::Value(false)
            );
        }

        #[test]
        fn bool_eq() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::BoolEq(
                    box BooleanExpression::Value(true),
                    box BooleanExpression::Value(true),
                )),
                BooleanExpression::Value(true)
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::BoolEq(
                    box BooleanExpression::Value(true),
                    box BooleanExpression::Value(false),
                )),
                BooleanExpression::Value(false)
            );
        }

        #[test]
        fn and() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::And(
                    box BooleanExpression::Value(true),
                    box BooleanExpression::Value(true),
                )),
                BooleanExpression::Value(true)
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::And(
                    box BooleanExpression::Value(true),
                    box BooleanExpression::Value(false),
                )),
                BooleanExpression::Value(false)
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::And(
                    box BooleanExpression::Identifier("a".into()),
                    box BooleanExpression::Value(true),
                )),
                BooleanExpression::Identifier("a".into())
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::And(
                    box BooleanExpression::Identifier("a".into()),
                    box BooleanExpression::Value(false),
                )),
                BooleanExpression::Value(false)
            );
        }

        #[test]
        fn or() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::Or(
                    box BooleanExpression::Value(true),
                    box BooleanExpression::Value(true),
                )),
                BooleanExpression::Value(true)
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::Or(
                    box BooleanExpression::Value(true),
                    box BooleanExpression::Value(false),
                )),
                BooleanExpression::Value(true)
            );
        }

        #[test]
        fn not() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::Not(
                    box BooleanExpression::Value(true),
                )),
                BooleanExpression::Value(false)
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::Not(
                    box BooleanExpression::Value(false),
                )),
                BooleanExpression::Value(true)
            );
        }

        #[test]
        fn if_else() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::IfElse(
                    box BooleanExpression::Value(true),
                    box BooleanExpression::Value(true),
                    box BooleanExpression::Value(false)
                )),
                BooleanExpression::Value(true)
            );

            assert_eq!(
                propagator.fold_boolean_expression(BooleanExpression::IfElse(
                    box BooleanExpression::Value(false),
                    box BooleanExpression::Value(true),
                    box BooleanExpression::Value(false)
                )),
                BooleanExpression::Value(false)
            );
        }
    }

    #[cfg(test)]
    mod uint {
        use super::*;

        #[test]
        fn select() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

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
                UExpressionInner::Value(2)
            );
        }

        #[test]
        fn add() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Add(
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    )
                ),
                UExpressionInner::Value(5)
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
                UExpressionInner::Identifier("a".into())
            );
        }

        #[test]
        fn sub() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Sub(
                        box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    )
                ),
                UExpressionInner::Value(1)
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
                UExpressionInner::Identifier("a".into())
            );
        }

        #[test]
        fn mult() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Mult(
                        box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    )
                ),
                UExpressionInner::Value(6)
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
                UExpressionInner::Identifier("a".into())
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
                UExpressionInner::Value(0)
            );
        }

        #[test]
        fn div() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Div(
                        box UExpressionInner::Value(6).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    )
                ),
                UExpressionInner::Value(3)
            );
        }

        #[test]
        fn rem() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Rem(
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    )
                ),
                UExpressionInner::Value(2)
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Rem(
                        box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    )
                ),
                UExpressionInner::Value(1)
            );
        }

        #[test]
        fn xor() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Xor(
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    )
                ),
                UExpressionInner::Value(1)
            );
        }

        #[test]
        fn and() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::And(
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    )
                ),
                UExpressionInner::Value(2)
            );
        }

        #[test]
        fn or() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Or(
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(3).annotate(UBitwidth::B32),
                    )
                ),
                UExpressionInner::Value(3)
            );
        }

        #[test]
        fn left_shift() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::LeftShift(
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                        3,
                    )
                ),
                UExpressionInner::Value(16)
            );
        }

        #[test]
        fn right_shift() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::RightShift(
                        box UExpressionInner::Value(4).annotate(UBitwidth::B32),
                        2,
                    )
                ),
                UExpressionInner::Value(1)
            );
        }

        #[test]
        fn not() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::Not(box UExpressionInner::Value(2).annotate(UBitwidth::B32),)
                ),
                UExpressionInner::Value(4294967293)
            );
        }

        #[test]
        fn if_else() {
            let mut propagator = ZirPropagator::<Bn128Field>::new();

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::IfElse(
                        box BooleanExpression::Value(true),
                        box UExpressionInner::Value(1).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    )
                ),
                UExpressionInner::Value(1)
            );

            assert_eq!(
                propagator.fold_uint_expression_inner(
                    UBitwidth::B32,
                    UExpressionInner::IfElse(
                        box BooleanExpression::Value(false),
                        box UExpressionInner::Value(1).annotate(UBitwidth::B32),
                        box UExpressionInner::Value(2).annotate(UBitwidth::B32),
                    )
                ),
                UExpressionInner::Value(2)
            );
        }
    }
}
