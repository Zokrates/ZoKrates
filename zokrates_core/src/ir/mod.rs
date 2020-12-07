use crate::flat_absy::flat_parameter::FlatParameter;
use crate::flat_absy::FlatVariable;
use crate::solvers::Solver;
use serde::{Deserialize, Serialize};
use std::fmt;
use zokrates_field::Field;

mod expression;
pub mod folder;
mod from_flat;
mod interpreter;
mod serialize;
mod witness;

pub use self::expression::QuadComb;
pub use self::expression::{CanonicalLinComb, LinComb};
pub use self::serialize::ProgEnum;

pub use self::interpreter::{Error, ExecutionResult, Interpreter};
pub use self::witness::Witness;

#[derive(Debug, Serialize, Deserialize, Clone, Hash)]
pub enum Statement<T> {
    Constraint(QuadComb<T>, LinComb<T>),
    Directive(Directive<T>),
}

impl<T: Field> PartialEq for Statement<T> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Statement::Constraint(l1, r1), Statement::Constraint(l2, r2)) => {
                l1.eq(l2) && r1.eq(r2)
            }
            (Statement::Directive(d1), Statement::Directive(d2)) => d1.eq(d2),
            _ => false,
        }
    }
}

impl<T: Field> Eq for Statement<T> {}

impl<T: Field> Statement<T> {
    pub fn definition<U: Into<QuadComb<T>>>(v: FlatVariable, e: U) -> Self {
        Statement::Constraint(e.into(), v.into())
    }

    pub fn constraint<U: Into<QuadComb<T>>, V: Into<LinComb<T>>>(quad: U, lin: V) -> Self {
        Statement::Constraint(quad.into(), lin.into())
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, Hash)]
pub struct Directive<T> {
    pub inputs: Vec<QuadComb<T>>,
    pub outputs: Vec<FlatVariable>,
    pub solver: Solver,
}

impl<T: Field> PartialEq for Directive<T> {
    fn eq(&self, other: &Self) -> bool {
        self.inputs.eq(&other.inputs)
            && self.outputs.eq(&other.outputs)
            && self.solver.eq(&other.solver)
    }
}

impl<T: Field> Eq for Directive<T> {}

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
            Statement::Constraint(ref quad, ref lin) => write!(f, "{} == {}", quad, lin),
            Statement::Directive(ref s) => write!(f, "{}", s),
        }
    }
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct Function<T> {
    pub id: String,
    pub statements: Vec<Statement<T>>,
    pub arguments: Vec<FlatVariable>,
    pub returns: Vec<FlatVariable>,
}

impl<T: Field> PartialEq for Function<T> {
    fn eq(&self, other: &Self) -> bool {
        self.id.eq(&other.id)
            && self.statements.eq(&other.statements)
            && self.arguments.eq(&other.arguments)
            && self.returns.eq(&other.returns)
    }
}

impl<T: Field> fmt::Display for Function<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "def {}({}) -> ({}):\n{}\n\t return {}",
            self.id,
            self.arguments
                .iter()
                .map(|v| format!("{}", v))
                .collect::<Vec<_>>()
                .join(", "),
            self.returns.len(),
            self.statements
                .iter()
                .map(|s| format!("\t{}", s))
                .collect::<Vec<_>>()
                .join("\n"),
            self.returns
                .iter()
                .map(|e| format!("{}", e))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Prog<T> {
    pub main: Function<T>,
    pub private: Vec<bool>,
}

impl<T: Field> PartialEq for Prog<T> {
    fn eq(&self, other: &Self) -> bool {
        self.main.eq(&other.main) && self.private.eq(&other.private)
    }
}

impl<T: Field> Prog<T> {
    pub fn constraint_count(&self) -> usize {
        self.main
            .statements
            .iter()
            .filter(|s| match s {
                Statement::Constraint(..) => true,
                _ => false,
            })
            .count()
    }

    pub fn arguments_count(&self) -> usize {
        self.private.len()
    }

    pub fn parameters(&self) -> Vec<FlatParameter> {
        self.main
            .arguments
            .iter()
            .zip(self.private.iter())
            .map(|(id, private)| FlatParameter {
                private: *private,
                id: *id,
            })
            .collect()
    }

    pub fn public_inputs(&self, witness: &Witness<T>) -> Vec<T> {
        self.main
            .arguments
            .clone()
            .iter()
            .zip(self.private.iter())
            .filter(|(_, p)| !**p)
            .map(|(v, _)| witness.0.get(v).unwrap().clone())
            .chain(witness.return_values())
            .collect()
    }
}

impl<T: Field> fmt::Display for Prog<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.main)
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
            );
            assert_eq!(format!("{}", c), "(1 * _42) * (1 * _42) == 1 * _42")
        }
    }
}
