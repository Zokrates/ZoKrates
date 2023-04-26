pub trait OperatorStr {
    const STR: &'static str;
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpAdd;

impl OperatorStr for OpAdd {
    const STR: &'static str = "+";
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpSub;

impl OperatorStr for OpSub {
    const STR: &'static str = "-";
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpFloorSub;

impl OperatorStr for OpFloorSub {
    const STR: &'static str = "- /* FLOOR_SUB */";
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpMul;

impl OperatorStr for OpMul {
    const STR: &'static str = "*";
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpDiv;

impl OperatorStr for OpDiv {
    const STR: &'static str = "/";
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpRem;

impl OperatorStr for OpRem {
    const STR: &'static str = "%";
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpPow;

impl OperatorStr for OpPow {
    const STR: &'static str = "**";
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpEq;

impl OperatorStr for OpEq {
    const STR: &'static str = "==";
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpLt;

impl OperatorStr for OpLt {
    const STR: &'static str = "<";
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpLe;

impl OperatorStr for OpLe {
    const STR: &'static str = "<=";
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpGt;

impl OperatorStr for OpGt {
    const STR: &'static str = ">";
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpGe;

impl OperatorStr for OpGe {
    const STR: &'static str = ">=";
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpXor;

impl OperatorStr for OpXor {
    const STR: &'static str = "^";
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpOr;

impl OperatorStr for OpOr {
    const STR: &'static str = "|";
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpAnd;

impl OperatorStr for OpAnd {
    const STR: &'static str = "&";
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpLsh;

impl OperatorStr for OpLsh {
    const STR: &'static str = "<<";
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpRsh;

impl OperatorStr for OpRsh {
    const STR: &'static str = ">>";
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpNot;

impl OperatorStr for OpNot {
    const STR: &'static str = "!";
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpNeg;

impl OperatorStr for OpNeg {
    const STR: &'static str = "-";
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct OpPos;

impl OperatorStr for OpPos {
    const STR: &'static str = "+";
}
