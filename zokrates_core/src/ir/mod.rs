use crate::flat_absy::flat_parameter::FlatParameter;
use crate::flat_absy::{FlatVariable, RuntimeError};
use crate::solvers::Solver;
use fallible_iterator::{FallibleIterator, IntoFallibleIterator};
use serde::{Deserialize, Serialize};
use std::fmt;
use std::hash::Hash;
use zokrates_field::Field;

mod expression;
pub mod folder;
pub mod from_flat;
mod interpreter;
mod serialize;
pub mod smtlib2;
pub mod visitor;
mod witness;

pub use self::expression::QuadComb;
pub use self::expression::{CanonicalLinComb, LinComb};
pub use self::serialize::ProgEnum;

pub use self::interpreter::{Error, ExecutionResult, Interpreter};
pub use self::witness::Witness;
pub use crate::ast::{Ast, DynamicError, IntoStatements, MemoryStatements, Statements};

use std::marker::PhantomData;

pub struct Ir<T>(PhantomData<T>);

impl<T> Ast for Ir<T> {
    type Statement = Statement<T>;
}

#[derive(Debug, Serialize, Deserialize, Clone, Hash, PartialEq, Eq)]
pub enum Statement<T> {
    Constraint(QuadComb<T>, LinComb<T>, Option<RuntimeError>),
    Directive(Directive<T>),
}

impl<T: Field> Statement<T> {
    pub fn definition<U: Into<QuadComb<T>>>(v: FlatVariable, e: U) -> Self {
        Statement::Constraint(e.into(), v.into(), None)
    }

    pub fn constraint<U: Into<QuadComb<T>>, V: Into<LinComb<T>>>(quad: U, lin: V) -> Self {
        Statement::Constraint(quad.into(), lin.into(), None)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, Hash, PartialEq, Eq)]
pub struct Directive<T> {
    pub inputs: Vec<QuadComb<T>>,
    pub outputs: Vec<FlatVariable>,
    pub solver: Solver,
}

impl<T: Field> fmt::Display for Directive<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "# {} = {}({})",
            self.outputs
                .iter()
                .map(|o| format!("{}", o))
                .collect::<Vec<_>>()
                .join(", "),
            self.solver,
            self.inputs
                .iter()
                .map(|i| format!("{}", i))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl<T: Field> fmt::Display for Statement<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Statement::Constraint(ref quad, ref lin, _) => write!(f, "{} == {}", quad, lin),
            Statement::Directive(ref s) => write!(f, "{}", s),
        }
    }
}

pub type MemoryIrStatements<T> = MemoryStatements<Statement<T>>;

pub type Prog<T> = ProgIterator<T, MemoryIrStatements<T>>;

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Default)]
pub struct ProgIterator<T, I: IntoStatements<Ir<T>>> {
    pub arguments: Vec<FlatParameter>,
    pub return_count: usize,
    pub statements: I,
    m: PhantomData<T>,
}

impl<T, I: IntoStatements<Ir<T>>> ProgIterator<T, I> {
    pub fn new(arguments: Vec<FlatParameter>, statements: I, return_count: usize) -> Self {
        Self {
            arguments,
            statements,
            return_count,
            m: PhantomData,
        }
    }

    pub fn collect(self) -> Result<ProgIterator<T, MemoryIrStatements<T>>, DynamicError> {
        Ok(ProgIterator::new(
            self.arguments,
            self.statements.into_fallible_iter().collect()?,
            self.return_count,
        ))
    }

    pub fn returns(&self) -> Vec<FlatVariable> {
        (0..self.return_count).map(FlatVariable::public).collect()
    }
}

impl<T: Field, I: IntoStatements<Ir<T>>> ProgIterator<T, I> {
    pub fn public_inputs(&self, witness: &Witness<T>) -> Vec<T> {
        self.arguments
            .iter()
            .filter(|p| !p.private)
            .map(|p| witness.0.get(&p.id).unwrap().clone())
            .chain(witness.return_values())
            .collect()
    }
}

impl<T> Prog<T> {
    pub fn constraint_count(&self) -> usize {
        self.statements
            .0
            .iter()
            .filter(|s| matches!(s, Statement::Constraint(..)))
            .count()
    }

    pub fn into_prog_iter(self) -> ProgIterator<T, impl IntoStatements<Ir<T>>> {
        ProgIterator::new(
            self.arguments,
            self.statements.into_fallible_iter(),
            self.return_count,
        )
    }
}

impl<T: Field> fmt::Display for Prog<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(
            f,
            "def main({}) -> ({}):",
            self.arguments
                .iter()
                .map(|v| format!("{}", v))
                .collect::<Vec<_>>()
                .join(", "),
            self.return_count,
        )?;
        for s in &self.statements.0 {
            writeln!(f, "\t{}", s)?;
        }
        writeln!(
            f,
            "\treturn {}",
            (0..self.return_count)
                .map(FlatVariable::public)
                .map(|e| format!("{}", e))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::Bn128Field;

    mod statement {
        use super::*;

        #[test]
        fn print_constraint() {
            let c: Statement<Bn128Field> = Statement::Constraint(
                QuadComb::from_linear_combinations(
                    FlatVariable::new(42).into(),
                    FlatVariable::new(42).into(),
                ),
                FlatVariable::new(42).into(),
                None,
            );
            assert_eq!(format!("{}", c), "(1 * _42) * (1 * _42) == 1 * _42")
        }
    }
}
