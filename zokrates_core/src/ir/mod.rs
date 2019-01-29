use flat_absy::flat_parameter::FlatParameter;
use flat_absy::FlatVariable;
use helpers::Helper;
use std::collections::HashMap;
use std::fmt;
use std::mem;
use zokrates_field::field::Field;

mod expression;
mod from_flat;
mod interpreter;

use self::expression::LinComb;
use self::expression::QuadComb;

pub use self::interpreter::Error;
pub use self::interpreter::ExecutionResult;

#[derive(Debug, Serialize, Deserialize, Clone)]
pub enum Statement<T: Field> {
    Constraint(QuadComb<T>, LinComb<T>),
    Directive(DirectiveStatement<T>),
}

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub struct DirectiveStatement<T: Field> {
    pub inputs: Vec<LinComb<T>>,
    pub outputs: Vec<FlatVariable>,
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
    pub arguments: Vec<FlatVariable>,
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
}

impl<T: Field> fmt::Display for Prog<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.main)
    }
}

/// Returns the index of `var` in `variables`, adding `var` with incremented index if it not yet exists.
///
/// # Arguments
///
/// * `variables` - A mutual map that maps all existing variables to their index.
/// * `var` - Variable to be searched for.
pub fn provide_variable_idx(
    variables: &mut HashMap<FlatVariable, usize>,
    var: &FlatVariable,
) -> usize {
    let index = variables.len();
    *variables.entry(*var).or_insert(index)
}

/// Calculates one R1CS row representation of a program and returns (V, A, B, C) so that:
/// * `V` contains all used variables and the index in the vector represents the used number in `A`, `B`, `C`
/// * `<A,x>*<B,x> = <C,x>` for a witness `x`
///
/// # Arguments
///
/// * `prog` - The program the representation is calculated for.
pub fn r1cs_program<T: Field>(
    prog: Prog<T>,
) -> (
    Vec<FlatVariable>,
    usize,
    Vec<Vec<(usize, T)>>,
    Vec<Vec<(usize, T)>>,
    Vec<Vec<(usize, T)>>,
) {
    let mut variables: HashMap<FlatVariable, usize> = HashMap::new();
    provide_variable_idx(&mut variables, &FlatVariable::one());

    for x in prog
        .main
        .arguments
        .iter()
        .enumerate()
        .filter(|(index, _)| !prog.private[*index])
    {
        provide_variable_idx(&mut variables, &x.1);
    }

    //Only the main function is relevant in this step, since all calls to other functions were resolved during flattening
    let main = prog.main;

    //~out are added after main's arguments as we want variables (columns)
    //in the r1cs to be aligned like "public inputs | private inputs"
    let main_return_count = main.returns.len();

    for i in 0..main_return_count {
        provide_variable_idx(&mut variables, &FlatVariable::public(i));
    }

    // position where private part of witness starts
    let private_inputs_offset = variables.len();

    // first pass through statements to populate `variables`
    for (quad, lin) in main.statements.iter().filter_map(|s| match s {
        Statement::Constraint(quad, lin) => Some((quad, lin)),
        Statement::Directive(..) => None,
    }) {
        for (k, _) in &quad.left.0 {
            provide_variable_idx(&mut variables, &k);
        }
        for (k, _) in &quad.right.0 {
            provide_variable_idx(&mut variables, &k);
        }
        for (k, _) in &lin.0 {
            provide_variable_idx(&mut variables, &k);
        }
    }

    let mut a = vec![];
    let mut b = vec![];
    let mut c = vec![];

    // second pass to convert program to raw sparse vectors
    for (quad, lin) in main.statements.into_iter().filter_map(|s| match s {
        Statement::Constraint(quad, lin) => Some((quad, lin)),
        Statement::Directive(..) => None,
    }) {
        a.push(
            quad.left
                .0
                .into_iter()
                .map(|(k, v)| (variables.get(&k).unwrap().clone(), v))
                .collect(),
        );
        b.push(
            quad.right
                .0
                .into_iter()
                .map(|(k, v)| (variables.get(&k).unwrap().clone(), v))
                .collect(),
        );
        c.push(
            lin.0
                .into_iter()
                .map(|(k, v)| (variables.get(&k).unwrap().clone(), v))
                .collect(),
        );
    }

    // Convert map back into list ordered by index
    let mut variables_list = vec![FlatVariable::new(0); variables.len()];
    for (k, v) in variables.drain() {
        assert_eq!(variables_list[v], FlatVariable::new(0));
        mem::replace(&mut variables_list[v], k);
    }
    (variables_list, private_inputs_offset, a, b, c)
}

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
                    FlatVariable::new(42).into(),
                    FlatVariable::new(42).into(),
                ),
                FlatVariable::new(42).into(),
            );
            assert_eq!(format!("{}", c), "(1 * _42) * (1 * _42) == 1 * _42")
        }
    }
}
