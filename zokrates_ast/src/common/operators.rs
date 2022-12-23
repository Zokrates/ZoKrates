use zokrates_field::Field;

use super::value::Value;

pub trait Operator<L, R, O>: OperatorStr
where
    L: Value,
    R: Value,
    O: Value,
{
    fn apply(left: L::Value, right: R::Value) -> O::Value;
}

pub trait OperatorStr {
    const STR: &'static str;
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpAdd;

impl OperatorStr for OpAdd {
    const STR: &'static str = "+";
}

impl<T: Field, E> Operator<E, E, E> for OpAdd
where
    E: Value<Value = T>,
{
    fn apply(left: T, right: T) -> T {
        left + right
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpSub;

impl OperatorStr for OpSub {
    const STR: &'static str = "-";
}

impl<T: Field, E> Operator<E, E, E> for OpSub
where
    E: Value<Value = T>,
{
    fn apply(left: T, right: T) -> T {
        left - right
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpMul;

impl OperatorStr for OpMul {
    const STR: &'static str = "*";
}

impl<T: Field, E> Operator<E, E, E> for OpMul
where
    E: Value<Value = T>,
{
    fn apply(left: T, right: T) -> T {
        left * right
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpDiv;

impl OperatorStr for OpDiv {
    const STR: &'static str = "*";
}

impl<T: Field, E> Operator<E, E, E> for OpDiv
where
    E: Value<Value = T>,
{
    fn apply(left: T, right: T) -> T {
        left / right
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpLt;

impl OperatorStr for OpLt {
    const STR: &'static str = "<";
}

impl<T: Field, E, Out> Operator<E, E, Out> for OpLt
where
    E: Value<Value = T>,
    Out: Value<Value = bool>,
{
    fn apply(left: T, right: T) -> bool {
        left < right
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpLe;

impl OperatorStr for OpLe {
    const STR: &'static str = "<=";
}

impl<T: Field, E, Out> Operator<E, E, Out> for OpLe
where
    E: Value<Value = T>,
    Out: Value<Value = bool>,
{
    fn apply(left: T, right: T) -> bool {
        left <= right
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpGt;

impl OperatorStr for OpGt {
    const STR: &'static str = ">";
}

impl<T: Field, E, Out> Operator<E, E, Out> for OpGt
where
    E: Value<Value = T>,
    Out: Value<Value = bool>,
{
    fn apply(left: T, right: T) -> bool {
        left > right
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpGe;

impl OperatorStr for OpGe {
    const STR: &'static str = ">=";
}

impl<T: Field, E, Out> Operator<E, E, Out> for OpGe
where
    E: Value<Value = T>,
    Out: Value<Value = bool>,
{
    fn apply(left: T, right: T) -> bool {
        left >= right
    }
}
