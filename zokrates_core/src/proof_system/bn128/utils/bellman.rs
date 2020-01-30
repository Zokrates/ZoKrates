extern crate rand;

use crate::ir::{CanonicalLinComb, Prog, Statement, Witness};
use bellman::groth16::Proof;
use bellman::groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    Parameters,
};
use bellman::{Circuit, ConstraintSystem, LinearCombination, SynthesisError, Variable};
use pairing::bn256::{Bn256, Fr};
use std::collections::BTreeMap;
use zokrates_field::field::{Field, FieldPrime};

use self::rand::ChaChaRng;
use crate::flat_absy::FlatVariable;

pub use self::parse::*;

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

fn bellman_combination<CS: ConstraintSystem<Bn256>>(
    l: CanonicalLinComb<FieldPrime>,
    cs: &mut CS,
    symbols: &mut BTreeMap<FlatVariable, Variable>,
    witness: &mut Witness<FieldPrime>,
) -> LinearCombination<Bn256> {
    l.0.into_iter()
        .map(|(k, v)| {
            (
                v.into_bellman(),
                symbols
                    .entry(k)
                    .or_insert_with(|| {
                        match k.is_output() {
                            true => cs.alloc_input(
                                || format!("{}", k),
                                || {
                                    Ok(witness
                                        .0
                                        .remove(&k)
                                        .ok_or(SynthesisError::AssignmentMissing)?
                                        .into_bellman())
                                },
                            ),
                            false => cs.alloc(
                                || format!("{}", k),
                                || {
                                    Ok(witness
                                        .0
                                        .remove(&k)
                                        .ok_or(SynthesisError::AssignmentMissing)?
                                        .into_bellman())
                                },
                            ),
                        }
                        .unwrap()
                    })
                    .clone(),
            )
        })
        .fold(LinearCombination::zero(), |acc, e| acc + e)
}

impl Prog<FieldPrime> {
    pub fn synthesize<CS: ConstraintSystem<Bn256>>(
        self,
        cs: &mut CS,
        witness: Option<Witness<FieldPrime>>,
    ) -> Result<(), SynthesisError> {
        // mapping from IR variables
        let mut symbols = BTreeMap::new();

        let mut witness = witness.unwrap_or(Witness::empty());

        assert!(symbols.insert(FlatVariable::one(), CS::one()).is_none());

        symbols.extend(
            self.main
                .arguments
                .iter()
                .zip(self.private)
                .enumerate()
                .map(|(index, (var, private))| {
                    let wire = match private {
                        true => cs.alloc(
                            || format!("PRIVATE_INPUT_{}", index),
                            || {
                                Ok(witness
                                    .0
                                    .remove(&var)
                                    .ok_or(SynthesisError::AssignmentMissing)?
                                    .into_bellman())
                            },
                        ),
                        false => cs.alloc_input(
                            || format!("PUBLIC_INPUT_{}", index),
                            || {
                                Ok(witness
                                    .0
                                    .remove(&var)
                                    .ok_or(SynthesisError::AssignmentMissing)?
                                    .into_bellman())
                            },
                        ),
                    }
                    .unwrap();
                    (var.clone(), wire)
                }),
        );

        let main = self.main;

        for statement in main.statements {
            match statement {
                Statement::Constraint(quad, lin) => {
                    let a = &bellman_combination(
                        quad.left.clone().as_canonical(),
                        cs,
                        &mut symbols,
                        &mut witness,
                    );
                    let b = &bellman_combination(
                        quad.right.clone().as_canonical(),
                        cs,
                        &mut symbols,
                        &mut witness,
                    );
                    let c =
                        &bellman_combination(lin.as_canonical(), cs, &mut symbols, &mut witness);

                    cs.enforce(|| "Constraint", |lc| lc + a, |lc| lc + b, |lc| lc + c);
                }
                _ => {}
            }
        }

        Ok(())
    }
}

impl Computation<FieldPrime> {
    pub fn prove(self, params: &Parameters<Bn256>) -> Proof<Bn256> {
        let rng = &mut ChaChaRng::new_unseeded();
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
            .map(|v| self.witness.clone().unwrap().0.get(v).unwrap().clone())
            .chain(self.witness.clone().unwrap().return_values())
            .map(|v| v.clone().into_bellman())
            .collect()
    }

    pub fn setup(self) -> Parameters<Bn256> {
        let rng = &mut ChaChaRng::new_unseeded();
        // run setup phase
        generate_random_parameters(self, rng).unwrap()
    }
}

impl Circuit<Bn256> for Computation<FieldPrime> {
    fn synthesize<CS: ConstraintSystem<Bn256>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        self.program.synthesize(cs, self.witness)
    }
}

mod parse {
    use lazy_static::lazy_static;

    use super::*;
    use regex::Regex;

    lazy_static! {
        static ref G2_REGEX: Regex = Regex::new(r"G2\(x=Fq2\(Fq\((?P<x0>0[xX][0-9a-fA-F]{64})\) \+ Fq\((?P<x1>0[xX][0-9a-fA-F]{64})\) \* u\), y=Fq2\(Fq\((?P<y0>0[xX][0-9a-fA-F]{64})\) \+ Fq\((?P<y1>0[xX][0-9a-fA-F]{64})\) \* u\)\)").unwrap();
    }

    lazy_static! {
        static ref G1_REGEX: Regex = Regex::new(
            r"G1\(x=Fq\((?P<x>0[xX][0-9a-fA-F]{64})\), y=Fq\((?P<y>0[xX][0-9a-fA-F]{64})\)\)"
        )
        .unwrap();
    }

    lazy_static! {
        static ref FR_REGEX: Regex = Regex::new(r"Fr\((?P<x>0[xX][0-9a-fA-F]{64})\)").unwrap();
    }

    fn parse_g1(e: &<Bn256 as bellman::pairing::Engine>::G1Affine) -> (String, String) {
        let raw_e = e.to_string();

        let captures = G1_REGEX.captures(&raw_e).unwrap();

        (
            captures.name(&"x").unwrap().as_str().to_string(),
            captures.name(&"y").unwrap().as_str().to_string(),
        )
    }

    fn parse_g2(
        e: &<Bn256 as bellman::pairing::Engine>::G2Affine,
    ) -> (String, String, String, String) {
        let raw_e = e.to_string();

        let captures = G2_REGEX.captures(&raw_e).unwrap();

        (
            captures.name(&"x1").unwrap().as_str().to_string(),
            captures.name(&"x0").unwrap().as_str().to_string(),
            captures.name(&"y1").unwrap().as_str().to_string(),
            captures.name(&"y0").unwrap().as_str().to_string(),
        )
    }

    fn parse_fr(e: &Fr) -> String {
        let raw_e = e.to_string();

        let captures = FR_REGEX.captures(&raw_e).unwrap();

        captures.name(&"x").unwrap().as_str().to_string()
    }

    pub fn parse_g1_json(e: &<Bn256 as bellman::pairing::Engine>::G1Affine) -> String {
        let parsed = parse_g1(e);

        format!("[\"{}\", \"{}\"]", parsed.0, parsed.1)
    }

    pub fn parse_g2_json(e: &<Bn256 as bellman::pairing::Engine>::G2Affine) -> String {
        let parsed = parse_g2(e);

        format!(
            "[[\"{}\", \"{}\"], [\"{}\", \"{}\"]]",
            parsed.0, parsed.1, parsed.2, parsed.3,
        )
    }

    pub fn parse_fr_json(e: &Fr) -> String {
        let parsed = parse_fr(e);

        format!("\"{}\"", parsed)
    }

    pub fn parse_g1_hex(e: &<Bn256 as bellman::pairing::Engine>::G1Affine) -> String {
        let parsed = parse_g1(e);

        format!("{}, {}", parsed.0, parsed.1)
    }

    pub fn parse_g2_hex(e: &<Bn256 as bellman::pairing::Engine>::G2Affine) -> String {
        let parsed = parse_g2(e);

        format!("[{}, {}], [{}, {}]", parsed.0, parsed.1, parsed.2, parsed.3,)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Function, LinComb};
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

            let witness = program.clone().execute(&vec![]).unwrap();
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

            let witness = program.clone().execute(&vec![FieldPrime::from(0)]).unwrap();
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

            let witness = program.clone().execute(&vec![FieldPrime::from(0)]).unwrap();
            let computation = Computation::with_witness(program, witness);

            let params = computation.clone().setup();
            let _proof = computation.prove(&params);
        }

        #[test]
        fn no_arguments() {
            let program: Prog<FieldPrime> = Prog {
                main: Function {
                    id: String::from("main"),
                    arguments: vec![],
                    returns: vec![FlatVariable::public(0)],
                    statements: vec![Statement::Constraint(
                        FlatVariable::one().into(),
                        FlatVariable::public(0).into(),
                    )],
                },
                private: vec![],
            };

            let witness = program.clone().execute(&vec![]).unwrap();
            let computation = Computation::with_witness(program, witness);

            let params = computation.clone().setup();
            let _proof = computation.prove(&params);
        }

        #[test]
        fn unordered_variables() {
            // public variables must be ordered from 0
            // private variables can be unordered
            let program: Prog<FieldPrime> = Prog {
                main: Function {
                    id: String::from("main"),
                    arguments: vec![FlatVariable::new(42), FlatVariable::new(51)],
                    returns: vec![FlatVariable::public(0), FlatVariable::public(1)],
                    statements: vec![
                        Statement::Constraint(
                            (LinComb::from(FlatVariable::new(42))
                                + LinComb::from(FlatVariable::new(51)))
                            .into(),
                            FlatVariable::public(0).into(),
                        ),
                        Statement::Constraint(
                            (LinComb::from(FlatVariable::one())
                                + LinComb::from(FlatVariable::new(42)))
                            .into(),
                            FlatVariable::public(1).into(),
                        ),
                    ],
                },
                private: vec![true, false],
            };

            let witness = program
                .clone()
                .execute(&vec![FieldPrime::from(3), FieldPrime::from(4)])
                .unwrap();
            let computation = Computation::with_witness(program, witness);

            let params = computation.clone().setup();
            let _proof = computation.prove(&params);
        }

        #[test]
        fn one() {
            let program: Prog<FieldPrime> = Prog {
                main: Function {
                    id: String::from("main"),
                    arguments: vec![FlatVariable::new(42)],
                    returns: vec![FlatVariable::public(0)],
                    statements: vec![Statement::Constraint(
                        (LinComb::from(FlatVariable::new(42)) + LinComb::one()).into(),
                        FlatVariable::public(0).into(),
                    )],
                },
                private: vec![false],
            };

            let witness = program.clone().execute(&vec![FieldPrime::from(3)]).unwrap();
            let computation = Computation::with_witness(program, witness);

            let params = computation.clone().setup();
            let _proof = computation.prove(&params);
        }

        #[test]
        fn with_directives() {
            let program: Prog<FieldPrime> = Prog {
                main: Function {
                    id: String::from("main"),
                    arguments: vec![FlatVariable::new(42), FlatVariable::new(51)],
                    returns: vec![FlatVariable::public(0)],
                    statements: vec![Statement::Constraint(
                        (LinComb::from(FlatVariable::new(42))
                            + LinComb::from(FlatVariable::new(51)))
                        .into(),
                        FlatVariable::public(0).into(),
                    )],
                },
                private: vec![true, false],
            };

            let witness = program
                .clone()
                .execute(&vec![FieldPrime::from(3), FieldPrime::from(4)])
                .unwrap();
            let computation = Computation::with_witness(program, witness);

            let params = computation.clone().setup();
            let _proof = computation.prove(&params);
        }
    }
}
