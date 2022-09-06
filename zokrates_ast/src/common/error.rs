use serde::{Deserialize, Serialize};
use std::fmt;

#[derive(Debug, Clone, Serialize, Deserialize, Hash, PartialEq, Eq)]
pub enum RuntimeError {
    BellmanConstraint,
    BellmanOneBinding,
    BellmanInputBinding,
    ArkConstraint,
    ArkOneBinding,
    ArkInputBinding,
    Bitness,
    Sum,
    Equal,
    Le,
    BranchIsolation,
    ConstantLtBitness,
    ConstantLtSum,
    LtFinalSum,
    LtSymetric,
    Or,
    Xor,
    IncompleteDynamicRange,
    Inverse,
    Euclidean,
    ShaXor,
    Division,
    SourceAssertion(String),
    ArgumentBitness,
    SelectRangeCheck,
}

impl From<crate::zir::RuntimeError> for RuntimeError {
    fn from(error: crate::zir::RuntimeError) -> Self {
        match error {
            crate::zir::RuntimeError::SourceAssertion(s) => RuntimeError::SourceAssertion(s),
            crate::zir::RuntimeError::SelectRangeCheck => RuntimeError::SelectRangeCheck,
            crate::zir::RuntimeError::DivisionByZero => RuntimeError::Inverse,
            crate::zir::RuntimeError::IncompleteDynamicRange => {
                RuntimeError::IncompleteDynamicRange
            }
        }
    }
}

impl RuntimeError {
    pub fn is_malicious(&self) -> bool {
        use RuntimeError::*;

        !matches!(
            self,
            SourceAssertion(_)
                | Inverse
                | SelectRangeCheck
                | ArgumentBitness
                | IncompleteDynamicRange
        )
    }
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use RuntimeError::*;

        let msg = match self {
            BellmanConstraint => "Bellman constraint is unsatisfied",
            BellmanOneBinding => "Bellman ~one binding is unsatisfied",
            BellmanInputBinding => "Bellman input binding is unsatisfied",
            ArkConstraint => "Ark constraint is unsatisfied",
            ArkOneBinding => "Ark ~one binding is unsatisfied",
            ArkInputBinding => "Ark input binding is unsatisfied",
            Bitness => "Bitness check failed",
            Sum => "Sum check failed",
            Equal => "Equal check failed",
            Le => "Constant Le check failed",
            BranchIsolation => "Branch isolation failed",
            ConstantLtBitness => "Bitness check failed in constant Lt check",
            ConstantLtSum => "Sum check failed in constant Lt check",
            LtFinalSum => "Sum check failed in final Lt check",
            LtSymetric => "Symetrical check failed in Lt check",
            Or => "Or check failed",
            Xor => "Xor check failed",
            IncompleteDynamicRange => {
                "Failed to compare field elements because dynamic comparison is incomplete"
            }
            Inverse => "Division by zero",
            Euclidean => "Euclidean check failed",
            ShaXor => "Internal Sha check failed",
            Division => "Division check failed",
            SourceAssertion(m) => m.as_str(),
            ArgumentBitness => "Argument bitness check failed",
            SelectRangeCheck => "Out of bounds array access",
        };

        write!(f, "{}", msg)
    }
}
