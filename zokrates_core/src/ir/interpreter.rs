use helpers::Executable;
use ir::*;
use std::collections::BTreeMap;
use zokrates_field::field::Field;

pub type ExecutionResult<T> = Result<Witness<T>, Error>;

pub struct Witness<T: Field>(BTreeMap<FlatVariable, T>);

impl<T: Field> Witness<T> {
    pub fn return_values(&self) -> Vec<&T> {
        let out = self
            .0
            .iter()
            .filter(|(k, _)| k.is_output())
            .collect::<HashMap<_, _>>();
        (0..out.len())
            .map(|i| *out.get(&FlatVariable::public(i)).unwrap())
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
                            return Err(Error::UnsatisfiedConstraint {
                                left: lhs_value.to_dec_string(),
                                right: rhs_value.to_dec_string(),
                            });
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

    fn check_inputs<U>(&self, inputs: &Vec<U>) -> Result<(), Error> {
        if self.main.arguments.len() == inputs.len() {
            Ok(())
        } else {
            Err(Error::WrongInputCount {
                expected: self.main.arguments.len(),
                received: inputs.len(),
            })
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

#[derive(PartialEq, Serialize, Deserialize)]
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
