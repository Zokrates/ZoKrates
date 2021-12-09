//! Module containing structs and enums to represent a program.
//!
//! @file absy.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

pub mod flat_parameter;
pub mod flat_variable;

pub use self::flat_parameter::FlatParameter;
pub use self::flat_variable::FlatVariable;

use serde::{Deserialize, Serialize};

pub use crate::ast::{DynamicError, IntoStatements, MemoryStatements, StatementTrait, Statements};
use crate::solvers::Solver;
use fallible_iterator::{FallibleIterator, IntoFallibleIterator};
use std::collections::HashMap;
use std::fmt;
use std::iter::FromIterator;
use zokrates_field::Field;

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
    LtBitness,
    LtSum,
    LtFinalBitness,
    LtFinalSum,
    LtSymetric,
    Or,
    Xor,
    Inverse,
    Euclidean,
    ShaXor,
    Division,
    SourceAssertion(String),
    ArgumentBitness,
    SelectRangeCheck,
}

impl RuntimeError {
    pub(crate) fn is_malicious(&self) -> bool {
        use RuntimeError::*;

        !matches!(
            self,
            SourceAssertion(_) | Inverse | LtSum | SelectRangeCheck | ArgumentBitness
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
            LtBitness => "Bitness check failed in Lt check",
            LtSum => "Sum check failed in Lt check",
            LtFinalBitness => "Bitness check failed in final Lt check",
            LtFinalSum => "Sum check failed in final Lt check",
            LtSymetric => "Symetrical check failed in Lt check",
            Or => "Or check failed",
            Xor => "Xor check failed",
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

pub type FlatProg<T> = FlatFunction<T>;

#[derive(Clone, PartialEq, Debug, Default)]
pub struct MemoryFlatStatements<T>(Vec<FlatStatement<T>>);

impl<T> From<Vec<FlatStatement<T>>> for MemoryFlatStatements<T> {
    fn from(v: Vec<FlatStatement<T>>) -> Self {
        MemoryFlatStatements(v)
    }
}

impl<T> MemoryFlatStatements<T> {
    pub fn iter(&self) -> std::slice::Iter<FlatStatement<T>> {
        self.0.iter()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn into_inner(self) -> Vec<FlatStatement<T>> {
        self.0
    }
}

impl<T> IntoIterator for MemoryFlatStatements<T> {
    type Item = FlatStatement<T>;
    type IntoIter = std::vec::IntoIter<FlatStatement<T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T> FromIterator<FlatStatement<T>> for MemoryFlatStatements<T> {
    fn from_iter<I: IntoIterator<Item = FlatStatement<T>>>(i: I) -> Self {
        MemoryFlatStatements(i.into_iter().collect())
    }
}

pub struct MemoryFlatStatementsIterator<T, I: Iterator<Item = FlatStatement<T>>> {
    statements: I,
}

impl<T, I: Iterator<Item = FlatStatement<T>>> FallibleIterator
    for MemoryFlatStatementsIterator<T, I>
{
    type Item = FlatStatement<T>;
    type Error = DynamicError;

    fn next(&mut self) -> Result<Option<Self::Item>, Self::Error> {
        Ok(self.statements.next())
    }
}

impl<T> IntoFallibleIterator for MemoryFlatStatements<T> {
    type Item = FlatStatement<T>;
    type Error = DynamicError;
    type IntoFallibleIter = MemoryFlatStatementsIterator<T, std::vec::IntoIter<FlatStatement<T>>>;

    fn into_fallible_iter(self) -> Self::IntoFallibleIter {
        MemoryFlatStatementsIterator {
            statements: self.into_iter(),
        }
    }
}

impl<T> StatementTrait for FlatStatement<T> {
    type Field = T;
}

pub type FlatFunction<T> = FlatFunctionIterator<MemoryFlatStatements<T>>;

pub type FlatProgIterator<I> = FlatFunctionIterator<I>;

#[derive(Clone, PartialEq, Debug)]
pub struct FlatFunctionIterator<I: IntoStatements> {
    /// Arguments of the function
    pub arguments: Vec<FlatParameter>,
    /// Vector of statements that are executed when running the function
    pub statements: I,
    /// Number of outputs
    pub return_count: usize,
}

impl<T, I: IntoStatements<Statement = FlatStatement<T>>> FlatFunctionIterator<I> {
    pub fn collect(self) -> Result<FlatFunction<T>, DynamicError> {
        Ok(FlatFunction {
            statements: MemoryFlatStatements(self.statements.into_fallible_iter().collect()?),
            arguments: self.arguments,
            return_count: self.return_count,
        })
    }
}

impl<T: Field> fmt::Display for FlatFunction<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "def main({}) -> {}:\n{}",
            self.arguments
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>()
                .join(","),
            self.return_count,
            self.statements
                .iter()
                .map(|x| format!("\t{}", x))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

/// Calculates a flattened function based on a R1CS (A, B, C) and returns that flattened function:
/// * The Rank 1 Constraint System (R1CS) is defined as:
/// * `<A,x>*<B,x> = <C,x>` for a witness `x`
/// * Since the matrices in R1CS are usually sparse, the following encoding is used:
/// * For each constraint (i.e., row in the R1CS), only non-zero values are supplied and encoded as a tuple (index, value).
///
/// # Arguments
///
/// * r1cs - R1CS in standard JSON data format

#[derive(Clone, PartialEq, Debug)]
pub enum FlatStatement<T> {
    Condition(FlatExpression<T>, FlatExpression<T>, RuntimeError),
    Definition(FlatVariable, FlatExpression<T>),
    Directive(FlatDirective<T>),
}

impl<T: Field> fmt::Display for FlatStatement<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FlatStatement::Definition(ref lhs, ref rhs) => write!(f, "{} = {}", lhs, rhs),
            FlatStatement::Condition(ref lhs, ref rhs, ref message) => {
                write!(f, "{} == {} // {}", lhs, rhs, message)
            }
            FlatStatement::Directive(ref d) => write!(f, "{}", d),
        }
    }
}

impl<T: Field> FlatStatement<T> {
    pub fn apply_substitution(
        self,
        substitution: &HashMap<FlatVariable, FlatVariable>,
    ) -> FlatStatement<T> {
        match self {
            FlatStatement::Definition(id, x) => FlatStatement::Definition(
                *id.apply_substitution(substitution),
                x.apply_substitution(substitution),
            ),
            FlatStatement::Condition(x, y, message) => FlatStatement::Condition(
                x.apply_substitution(substitution),
                y.apply_substitution(substitution),
                message,
            ),
            FlatStatement::Directive(d) => {
                let outputs = d
                    .outputs
                    .into_iter()
                    .map(|o| *o.apply_substitution(substitution))
                    .collect();
                let inputs = d
                    .inputs
                    .into_iter()
                    .map(|i| i.apply_substitution(substitution))
                    .collect();

                FlatStatement::Directive(FlatDirective {
                    inputs,
                    outputs,
                    ..d
                })
            }
        }
    }
}

#[derive(Clone, Hash, Debug, PartialEq, Eq)]
pub struct FlatDirective<T> {
    pub inputs: Vec<FlatExpression<T>>,
    pub outputs: Vec<FlatVariable>,
    pub solver: Solver,
}

impl<T> FlatDirective<T> {
    pub fn new<E: Into<FlatExpression<T>>>(
        outputs: Vec<FlatVariable>,
        solver: Solver,
        inputs: Vec<E>,
    ) -> Self {
        let (in_len, out_len) = solver.get_signature();
        assert_eq!(in_len, inputs.len());
        assert_eq!(out_len, outputs.len());
        FlatDirective {
            solver,
            inputs: inputs.into_iter().map(|i| i.into()).collect(),
            outputs,
        }
    }
}

impl<T: Field> fmt::Display for FlatDirective<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "# {} = {}({})",
            self.outputs
                .iter()
                .map(|o| o.to_string())
                .collect::<Vec<String>>()
                .join(", "),
            self.solver,
            self.inputs
                .iter()
                .map(|i| i.to_string())
                .collect::<Vec<String>>()
                .join(", ")
        )
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum FlatExpression<T> {
    Number(T),
    Identifier(FlatVariable),
    Add(Box<FlatExpression<T>>, Box<FlatExpression<T>>),
    Sub(Box<FlatExpression<T>>, Box<FlatExpression<T>>),
    Mult(Box<FlatExpression<T>>, Box<FlatExpression<T>>),
}

impl<T> From<T> for FlatExpression<T> {
    fn from(other: T) -> Self {
        Self::Number(other)
    }
}

impl<T: Field> FlatExpression<T> {
    pub fn apply_substitution(
        self,
        substitution: &HashMap<FlatVariable, FlatVariable>,
    ) -> FlatExpression<T> {
        match self {
            e @ FlatExpression::Number(_) => e,
            FlatExpression::Identifier(id) => {
                FlatExpression::Identifier(*id.apply_substitution(substitution))
            }
            FlatExpression::Add(e1, e2) => FlatExpression::Add(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            FlatExpression::Sub(e1, e2) => FlatExpression::Sub(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            FlatExpression::Mult(e1, e2) => FlatExpression::Mult(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
        }
    }

    pub fn is_linear(&self) -> bool {
        match *self {
            FlatExpression::Number(_) | FlatExpression::Identifier(_) => true,
            FlatExpression::Add(ref x, ref y) | FlatExpression::Sub(ref x, ref y) => {
                x.is_linear() && y.is_linear()
            }
            FlatExpression::Mult(ref x, ref y) => matches!(
                (x.clone(), y.clone()),
                (box FlatExpression::Number(_), box FlatExpression::Number(_))
                    | (
                        box FlatExpression::Number(_),
                        box FlatExpression::Identifier(_)
                    )
                    | (
                        box FlatExpression::Identifier(_),
                        box FlatExpression::Number(_)
                    )
            ),
        }
    }
}

impl<T: Field> fmt::Display for FlatExpression<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FlatExpression::Number(ref i) => write!(f, "{}", i),
            FlatExpression::Identifier(ref var) => write!(f, "{}", var),
            FlatExpression::Add(ref lhs, ref rhs) => write!(f, "({} + {})", lhs, rhs),
            FlatExpression::Sub(ref lhs, ref rhs) => write!(f, "({} - {})", lhs, rhs),
            FlatExpression::Mult(ref lhs, ref rhs) => write!(f, "({} * {})", lhs, rhs),
        }
    }
}

impl<T: Field> From<FlatVariable> for FlatExpression<T> {
    fn from(v: FlatVariable) -> FlatExpression<T> {
        FlatExpression::Identifier(v)
    }
}

#[derive(PartialEq, Debug)]
pub struct Error {
    message: String,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}
