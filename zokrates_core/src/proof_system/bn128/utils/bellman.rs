extern crate rand;

use bellman::groth16::Proof;
use bellman::groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    Parameters, VerifyingKey,
};
use bellman::{Circuit, ConstraintSystem, LinearCombination, SynthesisError, Variable};
use ir::{LinComb, Prog, Statement, Witness};
use pairing::bn256::{Bn256, Fr};
use std::collections::BTreeMap;
use std::fmt;
use zokrates_field::field::{Field, FieldPrime};

use self::rand::*;
use flat_absy::FlatVariable;

#[derive(Clone)]
pub struct Computation<T: Field> {
    program: Prog<T>,
    witness: Option<Witness<T>>,
}

impl<T: Field> Computation<T> {
    pub fn with_witness(program: Prog<T>, witness: Witness<T>) -> Self {
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
                .0
                .iter()
                .map(|(k, v)| format!("{} -> {}", k, v))
                .collect::<Vec<_>>()
                .join("\n"),
        )
    }
}

fn bellman_combination(
    l: LinComb<FieldPrime>,
    symbols: &BTreeMap<FlatVariable, Variable>,
) -> LinearCombination<Bn256> {
    l.0.into_iter()
        .map(|(k, v)| (Fr::from(v), symbols.get(&k).unwrap().clone()))
        .fold(LinearCombination::zero(), |acc, e| acc + e)
}

fn alloc<CS: ConstraintSystem<Bn256>>(
    cs: &mut CS,
    var: FlatVariable,
    witness: &Witness<FieldPrime>,
) -> Result<Variable, SynthesisError> {
    match var.is_output() {
        true => cs.alloc_input(
            || format!("{}", var),
            || {
                // let w = witness.ok_or(SynthesisError::AssignmentMissing)?;
                let val = witness
                    .0
                    .get(&var)
                    .ok_or(SynthesisError::AssignmentMissing)?;
                Ok(Fr::from(val.clone()))
            },
        ),
        false => cs.alloc(
            || format!("{}", var),
            || {
                // let witness = witness.ok_or(SynthesisError::AssignmentMissing)?;
                let val = witness
                    .0
                    .get(&var)
                    .ok_or(SynthesisError::AssignmentMissing)?;
                Ok(Fr::from(val.clone()))
            },
        ),
    }
}

impl Prog<FieldPrime> {
    pub fn synthesize<CS: ConstraintSystem<Bn256>>(
        self,
        cs: &mut CS,
        witness: Option<Witness<FieldPrime>>,
    ) -> Result<(), SynthesisError> {
        let mut symbols = BTreeMap::new();

        let mut arguments = vec![];

        let witness = witness.unwrap_or(Witness::empty());

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
                        let val = witness
                            .0
                            .get(&var)
                            .ok_or(SynthesisError::AssignmentMissing)?;
                        Ok(Fr::from(val.clone()))
                    },
                ),
                false => cs.alloc_input(
                    || format!("PUBLIC_INPUT_{}", index),
                    || {
                        // let witness = witness.ok_or(SynthesisError::AssignmentMissing)?;
                        let val = witness
                            .0
                            .get(&var)
                            .ok_or(SynthesisError::AssignmentMissing)?;
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
                        |lc| lc + &bellman_combination(quad.left.clone(), &symbols),
                        |lc| lc + &bellman_combination(quad.right.clone(), &symbols),
                        |lc| lc + &bellman_combination(lin, &symbols),
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
    pub fn prove(self, params: &Parameters<Bn256>) -> Proof<Bn256> {
        let rng = &mut thread_rng();
        let proof = create_random_proof(self.clone(), params, rng).unwrap();

        let pvk = prepare_verifying_key(&params.vk);

        // extract public inputs
        let public_inputs = self.public_inputs_values();

        assert!(verify_proof(&pvk, &proof, &public_inputs).unwrap());

        proof
    }

    pub fn public_inputs_values(&self) -> Vec<Fr> {
        self.program
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
                    .0
                    .keys()
                    .filter(|k| k.is_output()),
            )
            .map(|v| self.witness.clone().unwrap().0.get(v).unwrap().clone())
            .map(|v| Fr::from(v.clone()))
            .collect()
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

pub fn serialize_vk(vk: VerifyingKey<Bn256>) -> String {
    format!(
        "vk.alpha = {}
vk.beta = {}
vk.gamma = {}
vk.delta = {}
vk.gammaABC.len() = {}
{}",
        vk.alpha_g1,
        vk.beta_g2,
        vk.gamma_g2,
        vk.delta_g2,
        vk.ic.len(),
        vk.ic
            .iter()
            .enumerate()
            .map(|(i, x)| format!("vk.gammaABC[{}] = {}", i, x))
            .collect::<Vec<_>>()
            .join("\n")
    )
    .replace("G2(x=Fq2(Fq(", "[[")
    .replace("), y=Fq(", ", ")
    .replace("G1(x=Fq(", "[")
    .replace(") + Fq(", ", ")
    .replace("))", "]")
    .replace(") * u), y=Fq2(Fq(", "], [")
    .replace(") * u]", "]]")
}

pub fn serialize_proof(p: &Proof<Bn256>, inputs: &Vec<Fr>) -> String {
    format!(
        "{{
    \"proof\": {{
        \"a\": {},
        \"b\": {},
        \"c\": {}
    }},
    \"inputs\": [{}]
}}",
        p.a,
        p.b,
        p.c,
        inputs
            .iter()
            .map(|v| format!("\"{}\"", v))
            .collect::<Vec<_>>()
            .join(", "),
    )
    .replace("G2(x=Fq2(Fq(", "[[\"")
    .replace("), y=Fq(", "\", \"")
    .replace("G1(x=Fq(", "[\"")
    .replace(") + Fq(", "\", \"")
    .replace(") * u), y=Fq2(Fq(", "\"], [\"")
    .replace(") * u]", "\"]]")
    .replace(") * u))", "\"]]")
    .replace("))", "\"]")
    .replace("Fr(", "")
    .replace(")", "")
}

#[cfg(test)]
mod tests {
    use super::*;
    use ir::Function;
    use zokrates_field::field::FieldPrime;

    mod prove {
        use super::*;

        #[test]
        fn empty() {
            let program: Prog<FieldPrime> = Prog {
                main: Function {
                    id: String::from("main"),
                    arguments: vec![],
                    returns: vec![],
                    statements: vec![],
                },
                private: vec![],
            };

            let witness = program.clone().execute::<FieldPrime>(&vec![]).unwrap();
            let computation = Computation::with_witness(program, witness);

            let params = computation.clone().setup();
            let _proof = computation.prove(&params);
        }

        #[test]
        fn identity() {
            let program: Prog<FieldPrime> = Prog {
                main: Function {
                    id: String::from("main"),
                    arguments: vec![FlatVariable::new(0)],
                    returns: vec![FlatVariable::public(0)],
                    statements: vec![Statement::Constraint(
                        FlatVariable::new(0).into(),
                        FlatVariable::public(0).into(),
                    )],
                },
                private: vec![true],
            };

            let witness = program
                .clone()
                .execute::<FieldPrime>(&vec![FieldPrime::from(0)])
                .unwrap();
            let computation = Computation::with_witness(program, witness);

            let params = computation.clone().setup();
            let _proof = computation.prove(&params);
        }

        #[test]
        fn public_identity() {
            let program: Prog<FieldPrime> = Prog {
                main: Function {
                    id: String::from("main"),
                    arguments: vec![FlatVariable::new(0)],
                    returns: vec![FlatVariable::public(0)],
                    statements: vec![Statement::Constraint(
                        FlatVariable::new(0).into(),
                        FlatVariable::public(0).into(),
                    )],
                },
                private: vec![false],
            };

            let witness = program
                .clone()
                .execute::<FieldPrime>(&vec![FieldPrime::from(0)])
                .unwrap();
            let computation = Computation::with_witness(program, witness);

            let params = computation.clone().setup();
            let _proof = computation.prove(&params);
        }
    }

    mod serialize {
        use super::*;

        mod proof {
            use super::*;

            #[allow(dead_code)]
            #[derive(Deserialize)]
            struct G16ProofPoints {
                a: [String; 2],
                b: [[String; 2]; 2],
                c: [String; 2],
            }

            #[allow(dead_code)]
            #[derive(Deserialize)]
            struct G16Proof {
                proof: G16ProofPoints,
                inputs: Vec<String>,
            }

            #[test]
            fn serialize() {
                let program: Prog<FieldPrime> = Prog {
                    main: Function {
                        id: String::from("main"),
                        arguments: vec![FlatVariable::new(0)],
                        returns: vec![FlatVariable::public(0)],
                        statements: vec![Statement::Constraint(
                            FlatVariable::new(0).into(),
                            FlatVariable::public(0).into(),
                        )],
                    },
                    private: vec![false],
                };

                let witness = program
                    .clone()
                    .execute::<FieldPrime>(&vec![FieldPrime::from(42)])
                    .unwrap();
                let computation = Computation::with_witness(program, witness);

                let public_inputs_values = computation.public_inputs_values();

                let params = computation.clone().setup();
                let proof = computation.prove(&params);

                let serialized_proof = serialize_proof(&proof, &public_inputs_values);
                serde_json::from_str::<G16Proof>(&serialized_proof).unwrap();
            }
        }
    }
}
