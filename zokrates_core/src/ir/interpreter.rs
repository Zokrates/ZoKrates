use helpers::Executable;
use ir::*;
use std::collections::BTreeMap;
use zokrates_field::field::Field;

impl<T: Field> Prog<T> {
    pub fn execute(self, inputs: Vec<T>) -> Result<BTreeMap<FlatVariable, T>, Error<T>> {
        let main = self.main;
        assert_eq!(main.arguments.len(), inputs.len());
        let mut witness = BTreeMap::new();
        witness.insert(FlatVariable::one(), T::one());
        for (arg, value) in main.arguments.iter().zip(inputs.iter()) {
            witness.insert(arg.clone(), value.clone());
        }

        for statement in main.statements {
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
                            return Err(Error::Constraint(quad, lin, lhs_value, rhs_value));
                        }
                    }
                },
                Statement::Directive(ref d) => {
                    let input_values: Vec<T> = d
                        .inputs
                        .iter()
                        .map(|i| i.evaluate(&witness).unwrap())
                        .collect();
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

        Ok(witness)
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

    pub fn is_assignee<U>(&self, witness: &BTreeMap<FlatVariable, U>) -> bool {
        self.0.iter().count() == 1
            && self.0.iter().next().unwrap().1 == &T::from(1)
            && !witness.contains_key(self.0.iter().next().unwrap().0)
    }
}

impl<T: Field> QuadComb<T> {
    pub fn evaluate(&self, witness: &BTreeMap<FlatVariable, T>) -> Result<T, ()> {
        let left = self.left.evaluate(&witness)?;
        let right = self.right.evaluate(&witness)?;
        Ok(left * right)
    }
}

#[derive(PartialEq, Debug)]
pub enum Error<T: Field> {
    Constraint(QuadComb<T>, LinComb<T>, T, T),
    Solver,
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
        }
    }
}
