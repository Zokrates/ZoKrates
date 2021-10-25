use crate::flat_absy::flat_parameter::FlatParameter;
use crate::flat_absy::{FlatVariable, RuntimeError};
use crate::solvers::Solver;
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

#[derive(Serialize, Deserialize, Debug, Clone, Hash, PartialEq, Eq, Default)]
pub struct Prog<T> {
    pub statements: Vec<Statement<T>>,
    pub arguments: Vec<FlatParameter>,
    pub return_count: usize,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct ProgIterator<I> {
    pub statements: I,
    pub arguments: Vec<FlatParameter>,
    pub return_count: usize,
}

impl<T> From<Prog<T>> for ProgIterator<std::vec::IntoIter<Statement<T>>> {
    fn from(p: Prog<T>) -> ProgIterator<std::vec::IntoIter<Statement<T>>> {
        ProgIterator {
            statements: p.statements.into_iter(),
            arguments: p.arguments,
            return_count: p.return_count,
        }
    }
}

impl<T, I: Iterator<Item = Statement<T>>> From<ProgIterator<I>> for Prog<T> {
    fn from(p: ProgIterator<I>) -> Prog<T> {
        Prog {
            statements: p.statements.collect(),
            arguments: p.arguments,
            return_count: p.return_count,
        }
    }
}

impl<T> ProgIterator<T> {
    pub fn returns(&self) -> Vec<FlatVariable> {
        (0..self.return_count)
            .map(|id| FlatVariable::public(id))
            .collect()
    }
}

impl<T: Field> Prog<T> {
    pub fn returns(&self) -> Vec<FlatVariable> {
        (0..self.return_count)
            .map(|id| FlatVariable::public(id))
            .collect()
    }

    pub fn constraint_count(&self) -> usize {
        self.statements
            .iter()
            .filter(|s| matches!(s, Statement::Constraint(..)))
            .count()
    }

    pub fn arguments_count(&self) -> usize {
        self.arguments.len()
    }

    pub fn public_inputs(&self, witness: &Witness<T>) -> Vec<T> {
        self.arguments
            .iter()
            .filter(|p| !p.private)
            .map(|p| witness.0.get(&p.id).unwrap().clone())
            .chain(witness.return_values())
            .collect()
    }
}

impl<T: Field> fmt::Display for Prog<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "def main({}) -> ({}):\n{}\n\treturn {}",
            self.arguments
                .iter()
                .map(|v| format!("{}", v))
                .collect::<Vec<_>>()
                .join(", "),
            self.return_count,
            self.statements
                .iter()
                .map(|s| format!("\t{}", s))
                .collect::<Vec<_>>()
                .join("\n"),
            (0..self.return_count)
                .map(|i| FlatVariable::public(i))
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
