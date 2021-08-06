use crate::zir::{
    BooleanExpression, FieldElementExpression, Folder, UExpression, UExpressionInner, Variable,
    ZirExpression, ZirFunction, ZirProgram, ZirStatement,
};
use std::collections::HashMap;
use zokrates_field::Field;

type Constants<'ast, T> = HashMap<Variable<'ast>, ZirExpression<'ast, T>>;

trait Propagator<'ast, T> {
    type Output;
    fn propagate(self, constants: &mut Constants<'ast, T>) -> Self::Output;
}

#[derive(Default)]
pub struct ZirPropagator;

impl ZirPropagator {
    pub fn new() -> Self {
        ZirPropagator::default()
    }
    pub fn propagate<T: Field>(p: ZirProgram<T>) -> ZirProgram<T> {
        ZirPropagator::new().fold_program(p)
    }
}

impl<'ast, T: Field> Propagator<'ast, T> for ZirStatement<'ast, T> {
    type Output = Option<Self>;

    fn propagate(self, constants: &mut Constants<'ast, T>) -> Self::Output {
        match self {
            ZirStatement::Assertion(e) => match e.propagate(constants) {
                BooleanExpression::Value(true) => None,
                e => Some(ZirStatement::Assertion(e)),
            },
            ZirStatement::Definition(a, e) => {
                let e = e.propagate(constants);
                match e {
                    ZirExpression::FieldElement(FieldElementExpression::Number(_))
                    | ZirExpression::Boolean(BooleanExpression::Value(_)) => {
                        constants.insert(a, e);
                        None
                    }
                    ZirExpression::Uint(e) => match e.inner {
                        UExpressionInner::Value(_) => {
                            constants.insert(a, ZirExpression::Uint(e));
                            None
                        }
                        _ => Some(ZirStatement::Definition(a, ZirExpression::Uint(e))),
                    },
                    _ => Some(ZirStatement::Definition(a, e)),
                }
            }
            ZirStatement::IfElse(e, consequence, alternative) => Some(ZirStatement::IfElse(
                e.propagate(constants),
                consequence
                    .into_iter()
                    .filter_map(|s| s.propagate(constants))
                    .collect(),
                alternative
                    .into_iter()
                    .filter_map(|s| s.propagate(constants))
                    .collect(),
            )),
            ZirStatement::Return(e) => Some(ZirStatement::Return(
                e.into_iter().map(|e| e.propagate(constants)).collect(),
            )),
            ZirStatement::MultipleDefinition(assignees, list) => {
                // TODO: apply propagation here
                Some(ZirStatement::MultipleDefinition(assignees, list))
            }
        }
    }
}

impl<'ast, T: Field> Propagator<'ast, T> for ZirExpression<'ast, T> {
    type Output = Self;

    fn propagate(self, constants: &mut Constants<'ast, T>) -> Self::Output {
        match self {
            ZirExpression::Boolean(e) => ZirExpression::Boolean(e.propagate(constants)),
            ZirExpression::FieldElement(e) => ZirExpression::FieldElement(e.propagate(constants)),
            ZirExpression::Uint(e) => ZirExpression::Uint(e.propagate(constants)),
        }
    }
}

impl<'ast, T: Field> Propagator<'ast, T> for UExpression<'ast, T> {
    type Output = Self;

    fn propagate(self, constants: &mut Constants<'ast, T>) -> Self::Output {
        UExpression {
            inner: match self.inner {
                UExpressionInner::Value(v) => UExpressionInner::Value(v),
                UExpressionInner::Identifier(id) => {
                    match constants.get(&Variable::uint(id.clone(), self.bitwidth)) {
                        Some(ZirExpression::Uint(e)) => match e.inner {
                            UExpressionInner::Value(v) => UExpressionInner::Value(v),
                            _ => unreachable!("should contain constant uint value"),
                        },
                        _ => UExpressionInner::Identifier(id),
                    }
                }
                UExpressionInner::Select(e, box index) => {
                    let index = index.propagate(constants);
                    match index.inner {
                        UExpressionInner::Value(v) => e
                            .get(v as usize)
                            .cloned()
                            .expect("index out of bounds")
                            .into_inner(),
                        _ => UExpressionInner::Select(e, box index),
                    }
                }
                UExpressionInner::Add(box e1, box e2) => {
                    let e1 = e1.propagate(constants);
                    let e2 = e2.propagate(constants);

                    match (&e1.inner, &e2.inner) {
                        (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                            UExpressionInner::Value(n1 + n2)
                        }
                        _ => UExpressionInner::Add(box e1, box e2),
                    }
                }
                UExpressionInner::Sub(box e1, box e2) => {
                    let e1 = e1.propagate(constants);
                    let e2 = e2.propagate(constants);

                    match (&e1.inner, &e2.inner) {
                        (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                            UExpressionInner::Value(n1 - n2)
                        }
                        _ => UExpressionInner::Sub(box e1, box e2),
                    }
                }
                UExpressionInner::Mult(box e1, box e2) => {
                    let e1 = e1.propagate(constants);
                    let e2 = e2.propagate(constants);

                    match (&e1.inner, &e2.inner) {
                        (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                            UExpressionInner::Value(n1 * n2)
                        }
                        _ => UExpressionInner::Mult(box e1, box e2),
                    }
                }
                UExpressionInner::Div(box e1, box e2) => {
                    let e1 = e1.propagate(constants);
                    let e2 = e2.propagate(constants);

                    match (&e1.inner, &e2.inner) {
                        (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                            UExpressionInner::Value(n1 / n2)
                        }
                        _ => UExpressionInner::Div(box e1, box e2),
                    }
                }
                UExpressionInner::Rem(box e1, box e2) => {
                    let e1 = e1.propagate(constants);
                    let e2 = e2.propagate(constants);

                    match (&e1.inner, &e2.inner) {
                        (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                            UExpressionInner::Value(n1 % n2)
                        }
                        _ => UExpressionInner::Rem(box e1, box e2),
                    }
                }
                UExpressionInner::Xor(box e1, box e2) => {
                    let e1 = e1.propagate(constants);
                    let e2 = e2.propagate(constants);

                    match (&e1.inner, &e2.inner) {
                        (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                            UExpressionInner::Value(n1 ^ n2)
                        }
                        _ => UExpressionInner::Xor(box e1, box e2),
                    }
                }
                UExpressionInner::And(box e1, box e2) => {
                    let e1 = e1.propagate(constants);
                    let e2 = e2.propagate(constants);

                    match (&e1.inner, &e2.inner) {
                        (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                            UExpressionInner::Value(n1 & n2)
                        }
                        _ => UExpressionInner::And(box e1, box e2),
                    }
                }
                UExpressionInner::Or(box e1, box e2) => {
                    let e1 = e1.propagate(constants);
                    let e2 = e2.propagate(constants);

                    match (&e1.inner, &e2.inner) {
                        (UExpressionInner::Value(n1), UExpressionInner::Value(n2)) => {
                            UExpressionInner::Value(n1 | n2)
                        }
                        _ => UExpressionInner::Or(box e1, box e2),
                    }
                }
                UExpressionInner::LeftShift(box e, v) => {
                    let e = e.propagate(constants);
                    match &e.inner {
                        UExpressionInner::Value(n) => UExpressionInner::Value(n << v),
                        _ => UExpressionInner::LeftShift(box e, v),
                    }
                }
                UExpressionInner::RightShift(box e, v) => {
                    let e = e.propagate(constants);
                    match &e.inner {
                        UExpressionInner::Value(n) => UExpressionInner::Value(n >> v),
                        _ => UExpressionInner::RightShift(box e, v),
                    }
                }
                UExpressionInner::Not(box e) => {
                    let e = e.propagate(constants);
                    match &e.inner {
                        UExpressionInner::Value(n) => UExpressionInner::Value(!*n),
                        _ => UExpressionInner::Not(box e),
                    }
                }
                UExpressionInner::IfElse(box condition, box consequence, box alternative) => {
                    let condition = condition.propagate(constants);
                    match condition {
                        BooleanExpression::Value(true) => consequence.into_inner(),
                        BooleanExpression::Value(false) => alternative.into_inner(),
                        _ => UExpressionInner::IfElse(
                            box condition,
                            box consequence,
                            box alternative,
                        ),
                    }
                }
            },
            ..self
        }
    }
}

impl<'ast, T: Field> Propagator<'ast, T> for FieldElementExpression<'ast, T> {
    type Output = Self;

    fn propagate(self, constants: &mut Constants<'ast, T>) -> Self::Output {
        match self {
            FieldElementExpression::Number(n) => FieldElementExpression::Number(n),
            FieldElementExpression::Identifier(id) => {
                match constants.get(&Variable::field_element(id.clone())) {
                    Some(ZirExpression::FieldElement(FieldElementExpression::Number(v))) => {
                        FieldElementExpression::Number(v.clone())
                    }
                    _ => FieldElementExpression::Identifier(id),
                }
            }
            FieldElementExpression::Select(e, box index) => {
                let index = index.propagate(constants);
                match index.inner {
                    UExpressionInner::Value(v) => {
                        e.get(v as usize).cloned().expect("index out of bounds")
                    }
                    _ => FieldElementExpression::Select(e, box index),
                }
            }
            FieldElementExpression::Add(box e1, box e2) => {
                match (e1.propagate(constants), e2.propagate(constants)) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        FieldElementExpression::Number(n1 + n2)
                    }
                    (e1, e2) => FieldElementExpression::Add(box e1, box e2),
                }
            }
            FieldElementExpression::Sub(box e1, box e2) => {
                match (e1.propagate(constants), e2.propagate(constants)) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        FieldElementExpression::Number(n1 - n2)
                    }
                    (e1, e2) => FieldElementExpression::Sub(box e1, box e2),
                }
            }
            FieldElementExpression::Mult(box e1, box e2) => {
                match (e1.propagate(constants), e2.propagate(constants)) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        FieldElementExpression::Number(n1 * n2)
                    }
                    (e1, e2) => FieldElementExpression::Mult(box e1, box e2),
                }
            }
            FieldElementExpression::Div(box e1, box e2) => {
                match (e1.propagate(constants), e2.propagate(constants)) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        FieldElementExpression::Number(n1 / n2)
                    }
                    (e1, e2) => FieldElementExpression::Div(box e1, box e2),
                }
            }
            FieldElementExpression::Pow(box e, box exponent) => {
                let exponent = exponent.propagate(constants);
                match (e.propagate(constants), &exponent.inner) {
                    (_, UExpressionInner::Value(n2)) if *n2 == 0 => {
                        FieldElementExpression::Number(T::from(1))
                    }
                    (FieldElementExpression::Number(n), UExpressionInner::Value(e)) => {
                        FieldElementExpression::Number(n.pow(*e as usize))
                    }
                    (e, _) => FieldElementExpression::Pow(box e, box exponent),
                }
            }
            FieldElementExpression::IfElse(box condition, box consequence, box alternative) => {
                let condition = condition.propagate(constants);
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
}

impl<'ast, T: Field> Propagator<'ast, T> for BooleanExpression<'ast, T> {
    type Output = Self;

    fn propagate(self, constants: &mut Constants<'ast, T>) -> Self::Output {
        match self {
            BooleanExpression::Value(v) => BooleanExpression::Value(v),
            BooleanExpression::Identifier(id) => {
                match constants.get(&Variable::boolean(id.clone())) {
                    Some(ZirExpression::Boolean(BooleanExpression::Value(v))) => {
                        BooleanExpression::Value(*v)
                    }
                    _ => BooleanExpression::Identifier(id),
                }
            }
            BooleanExpression::Select(e, box index) => {
                let index = index.propagate(constants);
                match index.inner {
                    UExpressionInner::Value(v) => {
                        e.get(v as usize).cloned().expect("index out of bounds")
                    }
                    _ => BooleanExpression::Select(e, box index),
                }
            }
            BooleanExpression::FieldLt(box e1, box e2) => {
                match (e1.propagate(constants), e2.propagate(constants)) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        BooleanExpression::Value(n1 < n2)
                    }
                    (e1, e2) => BooleanExpression::FieldLt(box e1, box e2),
                }
            }
            BooleanExpression::FieldLe(box e1, box e2) => {
                match (e1.propagate(constants), e2.propagate(constants)) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        BooleanExpression::Value(n1 <= n2)
                    }
                    (e1, e2) => BooleanExpression::FieldLe(box e1, box e2),
                }
            }
            BooleanExpression::FieldGe(box e1, box e2) => {
                match (e1.propagate(constants), e2.propagate(constants)) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        BooleanExpression::Value(n1 >= n2)
                    }
                    (e1, e2) => BooleanExpression::FieldGe(box e1, box e2),
                }
            }
            BooleanExpression::FieldGt(box e1, box e2) => {
                match (e1.propagate(constants), e2.propagate(constants)) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        BooleanExpression::Value(n1 > n2)
                    }
                    (e1, e2) => BooleanExpression::FieldGt(box e1, box e2),
                }
            }
            BooleanExpression::FieldEq(box e1, box e2) => {
                match (e1.propagate(constants), e2.propagate(constants)) {
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
                let e1 = e1.propagate(constants);
                let e2 = e2.propagate(constants);

                match (&e1.inner, &e2.inner) {
                    (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                        BooleanExpression::Value(v1 < v2)
                    }
                    _ => BooleanExpression::UintLt(box e1, box e2),
                }
            }
            BooleanExpression::UintLe(box e1, box e2) => {
                let e1 = e1.propagate(constants);
                let e2 = e2.propagate(constants);

                match (&e1.inner, &e2.inner) {
                    (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                        BooleanExpression::Value(v1 <= v2)
                    }
                    _ => BooleanExpression::UintLe(box e1, box e2),
                }
            }
            BooleanExpression::UintGe(box e1, box e2) => {
                let e1 = e1.propagate(constants);
                let e2 = e2.propagate(constants);

                match (&e1.inner, &e2.inner) {
                    (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                        BooleanExpression::Value(v1 >= v2)
                    }
                    _ => BooleanExpression::UintGe(box e1, box e2),
                }
            }
            BooleanExpression::UintGt(box e1, box e2) => {
                let e1 = e1.propagate(constants);
                let e2 = e2.propagate(constants);

                match (&e1.inner, &e2.inner) {
                    (UExpressionInner::Value(v1), UExpressionInner::Value(v2)) => {
                        BooleanExpression::Value(v1 > v2)
                    }
                    _ => BooleanExpression::UintGt(box e1, box e2),
                }
            }
            BooleanExpression::UintEq(box e1, box e2) => {
                let e1 = e1.propagate(constants);
                let e2 = e2.propagate(constants);

                match (&e1.inner, &e2.inner) {
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
                match (e1.propagate(constants), e2.propagate(constants)) {
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
                match (e1.propagate(constants), e2.propagate(constants)) {
                    (BooleanExpression::Value(v1), BooleanExpression::Value(v2)) => {
                        BooleanExpression::Value(v1 || v2)
                    }
                    (e1, e2) => BooleanExpression::Or(box e1, box e2),
                }
            }
            BooleanExpression::And(box e1, box e2) => {
                match (e1.propagate(constants), e2.propagate(constants)) {
                    (BooleanExpression::Value(true), e) | (e, BooleanExpression::Value(true)) => e,
                    (BooleanExpression::Value(false), _) | (_, BooleanExpression::Value(false)) => {
                        BooleanExpression::Value(false)
                    }
                    (e1, e2) => BooleanExpression::And(box e1, box e2),
                }
            }
            BooleanExpression::Not(box e) => match e.propagate(constants) {
                BooleanExpression::Value(v) => BooleanExpression::Value(!v),
                e => BooleanExpression::Not(box e),
            },
            BooleanExpression::IfElse(box condition, box consequence, box alternative) => {
                let condition = condition.propagate(constants);
                match condition {
                    BooleanExpression::Value(true) => consequence,
                    BooleanExpression::Value(false) => alternative,
                    _ => BooleanExpression::IfElse(box condition, box consequence, box alternative),
                }
            }
        }
    }
}

impl<'ast, T: Field> Folder<'ast, T> for ZirPropagator {
    fn fold_function(&mut self, f: ZirFunction<'ast, T>) -> ZirFunction<'ast, T> {
        let mut constants: HashMap<Variable<'ast>, ZirExpression<'ast, T>> = HashMap::new();

        ZirFunction {
            signature: f.signature,
            arguments: f.arguments,
            statements: f
                .statements
                .into_iter()
                .filter_map(|s| s.propagate(&mut constants))
                .collect(),
        }
    }
}
