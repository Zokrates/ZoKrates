extern crate rand;

use bellman::groth16::Proof;
use bellman::groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    Parameters,
};
use bellman::{Circuit, ConstraintSystem, LinearCombination, SynthesisError, Variable};
use field::{Field, FieldPrime};
use ir::*;
use pairing::bn256::{Bn256, Fr};
use std::collections::BTreeMap;

use self::rand::*;
use ff::PrimeField;
use ff::PrimeFieldRepr;
use flat_absy::FlatVariable;

impl From<FieldPrime> for Fr {
    fn from(e: FieldPrime) -> Fr {
        let s = e.to_dec_string();
        Fr::from_str(&s).unwrap()
    }
}

impl From<Fr> for FieldPrime {
    fn from(e: Fr) -> FieldPrime {
        let mut res: Vec<u8> = vec![];
        e.into_repr().write_le(&mut res).unwrap();
        FieldPrime::from_byte_vector(res)
    }
}

#[derive(Clone)]
pub struct Computation<T: Field> {
    program: Prog<T>,
    witness: Option<BTreeMap<FlatVariable, T>>,
}

impl<T: Field> Computation<T> {
    pub fn with_witness(program: Prog<T>, witness: BTreeMap<FlatVariable, T>) -> Self {
        Computation {
            program,
            witness: Some(witness),
        }
    }

    pub fn without_witness(program: Prog<T>) -> Self {
        Computation {
            program,
            witness: None,
        }
    }
}
impl<T: Field> fmt::Display for Computation<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Compute:\n{}\n\nwith witness {}",
            self.program,
            self.witness
                .clone()
                .unwrap()
                .iter()
                .map(|(k, v)| format!("{} -> {}", k, v))
                .collect::<Vec<_>>()
                .join("\n"),
        )
    }
}

impl LinComb<FieldPrime> {
    fn into_bellman_combination(
        self,
        symbols: &BTreeMap<FlatVariable, Variable>,
    ) -> LinearCombination<Bn256> {
        self.0
            .into_iter()
            .map(|(k, v)| (Fr::from(v), symbols.get(&k).unwrap().clone()))
            .fold(LinearCombination::zero(), |acc, e| acc + e)
    }
}

fn alloc<CS: ConstraintSystem<Bn256>>(
    cs: &mut CS,
    var: FlatVariable,
    witness: &BTreeMap<FlatVariable, FieldPrime>,
) -> Result<Variable, SynthesisError> {
    match var.is_output() {
        true => cs.alloc(
            || format!("{}", var),
            || {
                // let w = witness.ok_or(SynthesisError::AssignmentMissing)?;
                let val = witness.get(&var).ok_or(SynthesisError::AssignmentMissing)?;
                Ok(Fr::from(val.clone()))
            },
        ),
        false => cs.alloc_input(
            || format!("{}", var),
            || {
                // let witness = witness.ok_or(SynthesisError::AssignmentMissing)?;
                let val = witness.get(&var).ok_or(SynthesisError::AssignmentMissing)?;
                Ok(Fr::from(val.clone()))
            },
        ),
    }
}

impl Prog<FieldPrime> {
    pub fn synthesize<CS: ConstraintSystem<Bn256>>(
        self,
        cs: &mut CS,
        witness: Option<BTreeMap<FlatVariable, FieldPrime>>,
    ) -> Result<(), SynthesisError> {
        let mut symbols = BTreeMap::new();

        let mut arguments = vec![];

        let witness = witness.unwrap();

        for (index, (var, private)) in self
            .main
            .arguments
            .clone()
            .into_iter()
            .zip(self.private)
            .enumerate()
        {
            let wire = match private {
                true => cs.alloc(
                    || format!("PRIVATE_INPUT_{}", index),
                    || {
                        // let w = witness.ok_or(SynthesisError::AssignmentMissing)?;
                        let val = witness.get(&var).ok_or(SynthesisError::AssignmentMissing)?;
                        Ok(Fr::from(val.clone()))
                    },
                ),
                false => cs.alloc_input(
                    || format!("PUBLIC_INPUT_{}", index),
                    || {
                        // let witness = witness.ok_or(SynthesisError::AssignmentMissing)?;
                        let val = witness.get(&var).ok_or(SynthesisError::AssignmentMissing)?;
                        Ok(Fr::from(val.clone()))
                    },
                ),
            }?;
            arguments.push((var, wire));
        }

        symbols.extend(arguments);

        let main = self.main;
        symbols.insert(FlatVariable::one(), CS::one());

        for statement in main.statements {
            match statement {
                Statement::Constraint(quad, lin) => {
                    if lin.is_assignee(&symbols) {
                        let flat_var = lin.0.iter().next().unwrap().0.clone();
                        let var = alloc(cs, flat_var, &witness)?;
                        symbols.insert(flat_var, var);
                    }
                    cs.enforce(
                        || "Definition",
                        |lc| lc + &quad.left.clone().into_bellman_combination(&symbols),
                        |lc| lc + &quad.right.clone().into_bellman_combination(&symbols),
                        |lc| lc + &lin.into_bellman_combination(&symbols),
                    );
                }
                Statement::Directive(d) => {
                    for output in d.outputs {
                        let var = alloc(cs, output, &witness)?;
                        symbols.insert(output, var);
                    }
                }
            }
        }

        Ok(())
    }
}

impl Computation<FieldPrime> {
    pub fn setup_prove_verify(self) -> Proof<Bn256> {
        // run setup phase
        let params = self.clone().setup();
        let pvk = prepare_verifying_key(&params.vk);

        // generate proof
        let rng = &mut thread_rng();

        let proof = create_random_proof(self.clone(), &params, rng).unwrap();

        // extract public inputs
        let public_inputs: Vec<Fr> = self
            .program
            .main
            .arguments
            .clone()
            .iter()
            .zip(self.program.private.clone())
            .filter(|(_, p)| !p)
            .map(|(a, _)| a)
            .chain(
                self.witness
                    .clone()
                    .unwrap()
                    .keys()
                    .filter(|k| k.is_output()),
            )
            .map(|v| self.witness.clone().unwrap().get(v).unwrap().clone())
            .map(|v| Fr::from(v.clone()))
            .collect();

        assert!(verify_proof(&pvk, &proof, &public_inputs).unwrap());

        proof
    }

    pub fn setup(self) -> Parameters<Bn256> {
        let rng = &mut thread_rng();
        // run setup phase
        generate_random_parameters(self, rng).unwrap()
    }
}

impl Circuit<Bn256> for Computation<FieldPrime> {
    fn synthesize<CS: ConstraintSystem<Bn256>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        self.program.synthesize(cs, self.witness)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use field::FieldPrime;

    mod prove {
        use super::*;
        use ff::Field;

        #[test]
        fn empty_program() {
            let program: Prog<FieldPrime> = Prog {
                main: Function {
                    id: String::from("main"),
                    arguments: vec![],
                    returns: vec![],
                    statements: vec![],
                },
                private: vec![],
            };

            let witness = program.clone().execute(vec![]).unwrap();
            let computation = Computation::with_witness(program, witness);

            let _proof = computation.setup_prove_verify();
        }

        #[test]
        fn fr_to_field_to_fr() {
            let rng = &mut thread_rng();
            let a: Fr = rng.gen();

            assert_eq!(Fr::from(FieldPrime::from(a)), a);
        }

        #[test]
        fn field_to_fr_to_field() {
            // use Fr to get a random element
            let rng = &mut thread_rng();
            let a: Fr = rng.gen();

            // now test idempotence
            let a = FieldPrime::from(a);

            assert_eq!(FieldPrime::from(Fr::from(a.clone())), a);
        }

        #[test]
        fn one() {
            let a = FieldPrime::from(1);

            assert_eq!(Fr::from(a), Fr::one());
        }

        #[test]
        fn zero() {
            let a = FieldPrime::from(0);

            assert_eq!(Fr::from(a), Fr::zero());
        }

        #[test]
        fn minus_one() {
            let mut a: Fr = Fr::one();
            a.negate();
            assert_eq!(FieldPrime::from(a), FieldPrime::from(-1));
        }

        #[test]
        fn add() {
            let rng = &mut thread_rng();

            let mut a: Fr = rng.gen();
            let b: Fr = rng.gen();

            let aa = FieldPrime::from(a);
            let bb = FieldPrime::from(b);
            let cc = aa + bb;

            a.add_assign(&b);

            assert_eq!(FieldPrime::from(a), cc);
        }
    }
}
