use helpers::Helper;
use ir::variable::Variable;
use std::fmt;
use zokrates_field::field::Field;

mod expression;
mod from_flat;
mod interpreter;
mod variable;

use self::expression::LinComb;
use self::expression::QuadComb;

pub use self::interpreter::Error;
pub use self::interpreter::ExecutionResult;
pub use self::variable::FullWitness;
pub use self::variable::Layout;
pub use self::variable::Witness;

#[derive(Debug, Serialize, Deserialize, Clone)]
pub enum Statement<T: Field> {
    Constraint(QuadComb<T>, LinComb<T>),
    Directive(DirectiveStatement<T>),
}

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub struct DirectiveStatement<T: Field> {
    pub inputs: Vec<LinComb<T>>,
    pub outputs: Vec<Variable>,
    pub helper: Helper,
}

impl<T: Field> fmt::Display for DirectiveStatement<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "# {} = {}({})",
            self.outputs
                .iter()
                .map(|o| format!("{}", o))
                .collect::<Vec<_>>()
                .join(", "),
            self.helper,
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
pub struct Function<T: Field> {
    pub id: String,
    pub statements: Vec<Statement<T>>,
    pub arguments: Vec<Variable>,
    pub returns: Vec<QuadComb<T>>,
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
pub struct Prog<T: Field> {
    pub main: Function<T>,
    pub private: Vec<bool>,
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

    pub fn public_arguments_count(&self) -> usize {
        self.private.iter().filter(|b| !**b).count()
    }

    pub fn private_arguments_count(&self) -> usize {
        self.private.iter().filter(|b| **b).count()
    }

    pub fn parameters(&self) -> Vec<Variable> {
        self.main.arguments.clone()
    }
}

impl<T: Field> fmt::Display for Prog<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.main)
    }
}

// /// Returns the index of `var` in `variables`, adding `var` with incremented index if it not yet exists.
// ///
// /// # Arguments
// ///
// /// * `variables` - A mutual map that maps all existing variables to their index.
// /// * `var` - Variable to be searched for.
// // pub fn provide_variable_idx(
// //     variables: &mut HashMap<Variable, usize>,
// //     var: &Variable,
// // ) -> usize {
// //     let index = variables.len();
// //     *variables.entry(*var).or_insert(index)
// // }

// /// Calculates one R1CS row representation of a program and returns (V, A, B, C) so that:
// /// * `V` contains all used variables and the index in the vector represents the used number in `A`, `B`, `C`
// /// * `<A,x>*<B,x> = <C,x>` for a witness `x`
// ///
// /// # Arguments
// ///
// /// * `prog` - The program the representation is calculated for.
// pub fn r1cs_program<T: Field>(
//     prog: Prog<T>,
// ) -> (
//     Vec<Variable>,
//     usize,
//     Vec<Vec<(usize, T)>>,
//     Vec<Vec<(usize, T)>>,
//     Vec<Vec<(usize, T)>>,
// ) {

//     unimplemented!()
// }

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    mod statement {
        use super::*;

        #[test]
        fn print_constraint() {
            let c: Statement<FieldPrime> = Statement::Constraint(
                QuadComb::from_linear_combinations(
                    Variable::Private(42).into(),
                    Variable::Private(42).into(),
                ),
                Variable::Private(42).into(),
            );
            assert_eq!(format!("{}", c), "(1 * _42) * (1 * _42) == 1 * _42")
        }
    }
}
