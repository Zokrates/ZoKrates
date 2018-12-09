use bellman::groth16::Proof as BellmanSnark;
use ff::ScalarEngine;
use field::Field;
use helpers::Executable;
use ir::*;
use pairing::Engine;
use std::collections::BTreeMap;

struct BellmanProof<E: Engine> {
    snark: BellmanSnark<E>,
    public_inputs: Vec<E::Fr>,
}

pub struct Snark<T: Field> {
    dummy: T,
}

impl<T: Field, E: Engine> From<BellmanProof<E>> for Proof<T> {
    fn from(p: BellmanProof<E>) -> Proof<T> {
        unimplemented!()
    }
}

impl<T: Field, E: Engine> From<BellmanSnark<E>> for Snark<T> {
    fn from(p: BellmanSnark<E>) -> Snark<T> {
        unimplemented!()
    }
}

// fn to_bellman<T: Field, E: Engine>(e: T) -> E::Fr {
//     unimplemented!()
// }

fn to_bellman<FieldPrime, Bn256>(e: FieldPrime) -> <Bn256 as ScalarEngine>::Fr {
    unimplemented!()
}

pub struct Proof<T: Field> {
    snark: Snark<T>,
    public_inputs: Vec<T>,
}

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
                        let val = quad.evaluate(&witness);
                        witness.insert(lin.0.iter().next().unwrap().0.clone(), val);
                    }
                    false => {
                        let lhs_value = quad.evaluate(&witness);
                        let rhs_value = lin.evaluate(&witness);
                        if lhs_value != rhs_value {
                            return Err(Error::Constraint(quad, lin, lhs_value, rhs_value));
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

        Ok(witness)
    }

    pub fn prove(self, inputs: Vec<T>) -> Result<Proof<T>, Error<T>> {
        Ok(Proof {
            snark: Snark { dummy: T::from(0) },
            public_inputs: vec![],
        })
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

#[cfg(test)]
mod tests {
    use super::*;
    use field::FieldPrime;

    mod prove {
        use super::*;

        #[test]
        fn test() {
            let p: Prog<FieldPrime> = Prog {
                main: Function {
                    id: String::from("main"),
                    arguments: vec![],
                    returns: vec![],
                    statements: vec![],
                },
                private: vec![],
            };

            let proof = p.prove(vec![]).unwrap();
            assert_eq!(proof.public_inputs, vec![]);
        }
    }
}
