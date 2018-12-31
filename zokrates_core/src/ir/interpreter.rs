use field::Field;
use helpers::Executable;
use ir::*;
use std::collections::BTreeMap;

pub type ExecutionResult<T> = Result<Witness<T>, Error<T>>;

pub struct Witness<T: Field>(BTreeMap<FlatVariable, T>);

impl<T: Field> Witness<T> {
    pub fn return_values(&self) -> Vec<T> {
        self.0
            .clone()
            .into_iter()
            .filter(|(k, _)| k.is_output())
            .map(|(_, v)| v)
            .collect()
    }

    pub fn format_outputs(&self) -> String {
        self.0
            .iter()
            .filter_map(|(variable, value)| match variable {
                variable if variable.is_output() => Some(format!("{} {}", variable, value)),
                _ => None,
            })
            .collect::<Vec<String>>()
            .join("\n")
    }
}

impl<T: Field> fmt::Display for Witness<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            self.0
                .iter()
                .map(|(k, v)| format!("{} {}", k, v.to_dec_string()))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

impl<T: Field> Prog<T> {
    pub fn execute<U: Into<T> + Clone>(&self, inputs: &Vec<U>) -> ExecutionResult<T> {
        let main = &self.main;
        self.check_inputs(&inputs)?;
        let mut witness = BTreeMap::new();
        witness.insert(FlatVariable::one(), T::one());
        for (arg, value) in main.arguments.iter().zip(inputs.iter()) {
            witness.insert(arg.clone(), value.clone().into());
        }

        for statement in &main.statements {
            match statement {
                Statement::Constraint(quad, lin) => match lin.is_assignee(&witness) {
                    true => {
                        let val = quad.evaluate(&witness);
                        witness.insert(lin.0.iter().next().unwrap().0.clone(), val);
                    }
                    false => {
                        let lhs_value = quad.evaluate(&witness);
                        let rhs_value = lin.evaluate(&witness);
                        if lhs_value != rhs_value {
                            return Err(Error::Constraint(
                                quad.clone(),
                                lin.clone(),
                                lhs_value,
                                rhs_value,
                            ));
                        }
                    }
                },
                Statement::Directive(ref d) => {
                    let input_values: Vec<T> =
                        d.inputs.iter().map(|i| i.evaluate(&witness)).collect();
                    match d.helper.execute(&input_values) {
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

        Ok(Witness(witness))
    }

    fn check_inputs<U>(&self, inputs: &Vec<U>) -> Result<(), Error<T>> {
        if self.main.arguments.len() == inputs.len() {
            Ok(())
        } else {
            Err(Error::Inputs(self.main.arguments.len(), inputs.len()))
        }
    }
}

impl<T: Field> LinComb<T> {
    fn evaluate(&self, witness: &BTreeMap<FlatVariable, T>) -> T {
        self.0
            .iter()
            .map(|(var, val)| witness.get(var).unwrap().clone() * val)
            .fold(T::from(0), |acc, t| acc + t)
    }

    fn is_assignee(&self, witness: &BTreeMap<FlatVariable, T>) -> bool {
        self.0.iter().count() == 1
            && self.0.iter().next().unwrap().1 == &T::from(1)
            && !witness.contains_key(self.0.iter().next().unwrap().0)
    }
}

impl<T: Field> QuadComb<T> {
    fn evaluate(&self, witness: &BTreeMap<FlatVariable, T>) -> T {
        self.left.evaluate(&witness) * self.right.evaluate(&witness)
    }
}

#[derive(PartialEq)]
pub enum Error<T: Field> {
    Constraint(QuadComb<T>, LinComb<T>, T, T),
    Solver,
    Inputs(usize, usize),
}

impl<T: Field> fmt::Display for Error<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::Constraint(ref quad, ref lin, ref left_value, ref right_value) => write!(
                f,
                "Expected {} to equal {}, but {} != {}",
                quad, lin, left_value, right_value
            ),
            Error::Solver => write!(f, ""),
            Error::Inputs(expected, received) => write!(
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

impl<T: Field> fmt::Debug for Error<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}
