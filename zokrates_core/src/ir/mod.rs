use crate::flat_absy::flat_parameter::FlatParameter;
use crate::flat_absy::{FlatVariable, RuntimeError};
use crate::solvers::Solver;
use fallible_iterator::{FallibleIterator, IntoFallibleIterator};
use serde::{Deserialize, Serialize};
use std::fmt;
use std::hash::Hash;
use std::iter::FromIterator;
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

#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct MemoryStatements<T>(Vec<Statement<T>>);

impl<T> From<Vec<Statement<T>>> for MemoryStatements<T> {
    fn from(v: Vec<Statement<T>>) -> Self {
        MemoryStatements(v)
    }
}

impl<T> IntoIterator for MemoryStatements<T> {
    type Item = Statement<T>;
    type IntoIter = std::vec::IntoIter<Statement<T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T> FromIterator<Statement<T>> for MemoryStatements<T> {
    fn from_iter<I: IntoIterator<Item = Statement<T>>>(i: I) -> Self {
        MemoryStatements(i.into_iter().collect())
    }
}

pub struct MemoryStatementsIterator<T, I: Iterator<Item = Statement<T>>> {
    statements: I,
}

impl<T, I: Iterator<Item = Statement<T>>> FallibleIterator for MemoryStatementsIterator<T, I> {
    type Item = Statement<T>;
    type Error = ();

    fn next(&mut self) -> Result<Option<Self::Item>, Self::Error> {
        Ok(self.statements.next())
    }
}

impl<T> IntoFallibleIterator for MemoryStatements<T> {
    type Item = Statement<T>;
    type Error = ();
    type IntoFallibleIter = MemoryStatementsIterator<T, std::vec::IntoIter<Statement<T>>>;

    fn into_fallible_iter(self) -> Self::IntoFallibleIter {
        MemoryStatementsIterator {
            statements: self.into_iter(),
        }
    }
}

pub trait IntoStatements: IntoFallibleIterator<Item = Statement<Self::Field>, Error = ()> {
    type Field;
}

impl<T, U: IntoFallibleIterator<Item = Statement<T>, Error = ()>> IntoStatements for U {
    type Field = T;
}

pub type Prog<T> = ProgIterator<MemoryStatements<T>>;

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Default)]
pub struct ProgIterator<I: IntoStatements> {
    pub arguments: Vec<FlatParameter>,
    pub return_count: usize,
    pub statements: I,
}

impl<I: IntoStatements> ProgIterator<I> {
    pub fn collect(self) -> Result<ProgIterator<MemoryStatements<I::Field>>, ()> {
        Ok(ProgIterator {
            statements: MemoryStatements(self.statements.into_fallible_iter().collect()?),
            arguments: self.arguments,
            return_count: self.return_count,
        })
    }

    pub fn returns(&self) -> Vec<FlatVariable> {
        (0..self.return_count).map(FlatVariable::public).collect()
    }
}

impl<T: Field, I: IntoStatements<Field = T>> ProgIterator<I> {
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

    pub fn into_prog_iter(self) -> ProgIterator<impl IntoStatements<Field = T>> {
        ProgIterator {
            statements: self.statements.into_fallible_iter(),
            arguments: self.arguments,
            return_count: self.return_count,
        }
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
