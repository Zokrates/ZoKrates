use crate::flat_absy::flat_variable::FlatVariable;
use crate::ir::Directive;
use crate::ir::{LinComb, Prog, QuadComb, Statement, Witness};
use crate::solvers::{Executable, Solver};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fmt;
use zokrates_field::Field;

pub type ExecutionResult<T> = Result<Witness<T>, Error>;

impl<T: Field> Prog<T> {}

pub struct Interpreter {
    /// Whether we should try to give out-of-range bit decompositions when the input is not a single summand.
    /// Used to do targetted testing of `<` flattening, making sure the bit decomposition we base the result on is unique.
    should_try_out_of_range: bool,
}

impl Default for Interpreter {
    fn default() -> Interpreter {
        Interpreter {
            should_try_out_of_range: false,
        }
    }
}

impl Interpreter {
    pub fn try_out_of_range() -> Interpreter {
        Interpreter {
            should_try_out_of_range: true,
        }
    }
}

impl Interpreter {
    pub fn execute<T: Field>(&self, program: &Prog<T>, inputs: &Vec<T>) -> ExecutionResult<T> {
        let main = &program.main;
        self.check_inputs(&program, &inputs)?;
        let mut witness = BTreeMap::new();
        witness.insert(FlatVariable::one(), T::one());
        for (arg, value) in main.arguments.iter().zip(inputs.iter()) {
            witness.insert(arg.clone(), value.clone().into());
        }

        for statement in main.statements.iter() {
            match statement {
                Statement::Constraint(quad, lin) => match lin.is_assignee(&witness) {
                    true => {
                        let val = quad.evaluate(&witness).unwrap();
                        witness.insert(lin.0.iter().next().unwrap().0.clone(), val);
                    }
                    false => {
                        let lhs_value = quad.evaluate(&witness).unwrap();
                        let rhs_value = lin.evaluate(&witness).unwrap();
                        if lhs_value != rhs_value {
                            return Err(Error::UnsatisfiedConstraint {
                                left: lhs_value.to_dec_string(),
                                right: rhs_value.to_dec_string(),
                            });
                        }
                    }
                },
                Statement::Directive(ref d) => {
                    match (&d.solver, &d.inputs, self.should_try_out_of_range) {
                        (Solver::Bits(bitwidth), inputs, true)
                            if inputs[0].left.0.len() > 1
                                || inputs[0].right.0.len() > 1
                                    && *bitwidth == T::get_required_bits() =>
                        {
                            Self::try_solve_out_of_range(&d, &mut witness)
                        }
                        _ => {
                            let inputs: Vec<_> = d
                                .inputs
                                .iter()
                                .map(|i| i.evaluate(&witness).unwrap())
                                .collect();
                            match d.solver.execute(&inputs) {
                                Ok(res) => {
                                    for (i, o) in d.outputs.iter().enumerate() {
                                        witness.insert(o.clone(), res[i].clone());
                                    }
                                    continue;
                                }
                                Err(_) => return Err(Error::Solver),
                            };
                        }
                    }
                }
            }
        }

        Ok(Witness(witness))
    }

    fn try_solve_out_of_range<T: Field>(d: &Directive<T>, witness: &mut BTreeMap<FlatVariable, T>) {
        use num::traits::Pow;

        // we target the `2a - 2b` part of the `<` check by only returning out-of-range results
        // when the input is not a single summand
        let value = d.inputs[0].evaluate(&witness).unwrap();
        let candidate = value.to_biguint() + T::max_value().to_biguint() + T::from(1).to_biguint();
        let input = if candidate < T::from(2).to_biguint().pow(T::get_required_bits()) {
            candidate
        } else {
            value.to_biguint()
        };

        let mut num = input.clone();
        let mut res = vec![];
        let bits = T::get_required_bits();
        for i in (0..bits).rev() {
            if T::from(2).to_biguint().pow(i as usize) <= num {
                num = num - T::from(2).to_biguint().pow(i as usize);
                res.push(T::one());
            } else {
                res.push(T::zero());
            }
        }
        assert_eq!(num, T::zero().to_biguint());
        for (i, o) in d.outputs.iter().enumerate() {
            witness.insert(o.clone(), res[i].clone());
        }
    }

    fn check_inputs<T: Field, U>(&self, program: &Prog<T>, inputs: &Vec<U>) -> Result<(), Error> {
        if program.main.arguments.len() == inputs.len() {
            Ok(())
        } else {
            Err(Error::WrongInputCount {
                expected: program.main.arguments.len(),
                received: inputs.len(),
            })
        }
    }
}

impl<T: Field> LinComb<T> {
    fn evaluate(&self, witness: &BTreeMap<FlatVariable, T>) -> Result<T, ()> {
        self.0
            .iter()
            .map(|(var, mult)| witness.get(var).map(|v| v.clone() * mult).ok_or(())) // get each term
            .collect::<Result<Vec<_>, _>>() // fail if any term isn't found
            .map(|v| v.iter().fold(T::from(0), |acc, t| acc + t)) // return the sum
    }

    fn is_assignee<U>(&self, witness: &BTreeMap<FlatVariable, U>) -> bool {
        self.0.iter().count() == 1
            && self.0.iter().next().unwrap().1 == T::from(1)
            && !witness.contains_key(&self.0.iter().next().unwrap().0)
    }
}

impl<T: Field> QuadComb<T> {
    pub fn evaluate(&self, witness: &BTreeMap<FlatVariable, T>) -> Result<T, ()> {
        let left = self.left.evaluate(&witness)?;
        let right = self.right.evaluate(&witness)?;
        Ok(left * right)
    }
}

#[derive(PartialEq, Serialize, Deserialize, Clone)]
pub enum Error {
    UnsatisfiedConstraint { left: String, right: String },
    Solver,
    WrongInputCount { expected: usize, received: usize },
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::UnsatisfiedConstraint {
                ref left,
                ref right,
            } => write!(f, "Expected {} to equal {}", left, right),
            Error::Solver => write!(f, ""),
            Error::WrongInputCount { expected, received } => write!(
                f,
                "Program takes {} input{} but was passed {} value{}",
                expected,
                if expected == 1 { "" } else { "s" },
                received,
                if received == 1 { "" } else { "s" }
            ),
        }
    }
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}
