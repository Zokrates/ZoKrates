pub mod groth16;

use crate::ir::{CanonicalLinComb, Prog, Statement, Witness};
use bellman::groth16::Proof;
use bellman::groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    Parameters,
};
use bellman::pairing::ff::ScalarEngine;
use bellman::{Circuit, ConstraintSystem, LinearCombination, SynthesisError, Variable};
use std::collections::BTreeMap;
use zokrates_field::BellmanFieldExtensions;
use zokrates_field::Field;

use crate::flat_absy::FlatVariable;
use rand_0_4::ChaChaRng;

pub use self::parse::*;

pub struct Bellman;

#[derive(Clone)]
pub struct Computation<T> {
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

fn bellman_combination<T: BellmanFieldExtensions, CS: ConstraintSystem<T::BellmanEngine>>(
    l: CanonicalLinComb<T>,
    cs: &mut CS,
    symbols: &mut BTreeMap<FlatVariable, Variable>,
    witness: &mut Witness<T>,
) -> LinearCombination<T::BellmanEngine> {
    l.0.into_iter()
        .map(|(k, v)| {
            (
                v.into_bellman(),
                *symbols.entry(k).or_insert_with(|| {
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
                }),
            )
        })
        .fold(LinearCombination::zero(), |acc, e| acc + e)
}

impl<T: BellmanFieldExtensions + Field> Prog<T> {
    pub fn synthesize<CS: ConstraintSystem<T::BellmanEngine>>(
        self,
        cs: &mut CS,
        witness: Option<Witness<T>>,
    ) -> Result<(), SynthesisError> {
        // mapping from IR variables
        let mut symbols = BTreeMap::new();

        let mut witness = witness.unwrap_or_else(Witness::empty);

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
                    (*var, wire)
                }),
        );

        let main = self.main;

        for statement in main.statements {
            if let Statement::Constraint(quad, lin) = statement {
                let a = &bellman_combination(
                    quad.left.into_canonical(),
                    cs,
                    &mut symbols,
                    &mut witness,
                );
                let b = &bellman_combination(
                    quad.right.into_canonical(),
                    cs,
                    &mut symbols,
                    &mut witness,
                );
                let c = &bellman_combination(lin.into_canonical(), cs, &mut symbols, &mut witness);

                cs.enforce(|| "Constraint", |lc| lc + a, |lc| lc + b, |lc| lc + c);
            }
        }

        Ok(())
    }
}

impl<T: BellmanFieldExtensions + Field> Computation<T> {
    fn get_random_seed(&self) -> Result<[u32; 8], getrandom::Error> {
        let mut seed = [0u8; 32];
        getrandom::getrandom(&mut seed)?;

        use std::mem::transmute;
        // This is safe because we are just reinterpreting the bytes (u8[32] -> u32[8]),
        // byte order or the actual content does not matter here as this is used
        // as a random seed for the rng.
        let seed: [u32; 8] = unsafe { transmute(seed) };
        Ok(seed)
    }

    pub fn prove(self, params: &Parameters<T::BellmanEngine>) -> Proof<T::BellmanEngine> {
        use rand_0_4::SeedableRng;
        let seed = self.get_random_seed().unwrap();
        let rng = &mut ChaChaRng::from_seed(seed.as_ref());

        let proof = create_random_proof(self.clone(), params, rng).unwrap();

        let pvk = prepare_verifying_key(&params.vk);

        // extract public inputs
        let public_inputs = self.public_inputs_values();

        assert!(verify_proof(&pvk, &proof, &public_inputs).unwrap());

        proof
    }

    pub fn public_inputs_values(&self) -> Vec<<T::BellmanEngine as ScalarEngine>::Fr> {
        self.program
            .public_inputs(self.witness.as_ref().unwrap())
            .iter()
            .map(|v| v.clone().into_bellman())
            .collect()
    }

    pub fn setup(self) -> Parameters<T::BellmanEngine> {
        use rand_0_4::SeedableRng;
        let seed = self.get_random_seed().unwrap();
        let rng = &mut ChaChaRng::from_seed(seed.as_ref());
        // run setup phase
        generate_random_parameters(self, rng).unwrap()
    }
}

impl<T: BellmanFieldExtensions + Field> Circuit<T::BellmanEngine> for Computation<T> {
    fn synthesize<CS: ConstraintSystem<T::BellmanEngine>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        self.program.synthesize(cs, self.witness)
    }
}

mod parse {
    use lazy_static::lazy_static;

    use super::*;
    use crate::proof_system::{Fr, G1Affine, G2Affine};
    use regex::Regex;

    lazy_static! {
        static ref G2_REGEX: Regex = Regex::new(r"G2\(x=Fq2\(Fq\((?P<x0>0[xX][0-9a-fA-F]*)\) \+ Fq\((?P<x1>0[xX][0-9a-fA-F]*)\) \* u\), y=Fq2\(Fq\((?P<y0>0[xX][0-9a-fA-F]*)\) \+ Fq\((?P<y1>0[xX][0-9a-fA-F]*)\) \* u\)\)").unwrap();
    }

    lazy_static! {
        static ref G1_REGEX: Regex =
            Regex::new(r"G1\(x=Fq\((?P<x>0[xX][0-9a-fA-F]*)\), y=Fq\((?P<y>0[xX][0-9a-fA-F]*)\)\)")
                .unwrap();
    }

    lazy_static! {
        static ref FR_REGEX: Regex = Regex::new(r"Fr\((?P<x>0[xX][0-9a-fA-F]*)\)").unwrap();
    }

    pub fn parse_g1<T: BellmanFieldExtensions>(
        e: &<T::BellmanEngine as bellman::pairing::Engine>::G1Affine,
    ) -> G1Affine {
        let raw_e = e.to_string();
        let captures = G1_REGEX.captures(&raw_e).unwrap();
        G1Affine(
            captures.name(&"x").unwrap().as_str().to_string(),
            captures.name(&"y").unwrap().as_str().to_string(),
        )
    }

    pub fn parse_g2<T: BellmanFieldExtensions>(
        e: &<T::BellmanEngine as bellman::pairing::Engine>::G2Affine,
    ) -> G2Affine {
        let raw_e = e.to_string();
        let captures = G2_REGEX.captures(&raw_e).unwrap();
        G2Affine(
            (
                captures.name(&"x0").unwrap().as_str().to_string(),
                captures.name(&"x1").unwrap().as_str().to_string(),
            ),
            (
                captures.name(&"y0").unwrap().as_str().to_string(),
                captures.name(&"y1").unwrap().as_str().to_string(),
            ),
        )
    }

    pub fn parse_fr<T: BellmanFieldExtensions>(e: &<T::BellmanEngine as ScalarEngine>::Fr) -> Fr {
        let raw_e = e.to_string();
        let captures = FR_REGEX.captures(&raw_e).unwrap();
        captures.name(&"x").unwrap().as_str().to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::Interpreter;
    use crate::ir::{Function, LinComb};
    use zokrates_field::Bn128Field;

    mod prove {
        use super::*;

        #[test]
        fn empty() {
            let program: Prog<Bn128Field> = Prog {
                main: Function {
                    id: String::from("main"),
                    arguments: vec![],
                    returns: vec![],
                    statements: vec![],
                },
                private: vec![],
            };

            let interpreter = Interpreter::default();

            let witness = interpreter.execute(&program, &[]).unwrap();
            let computation = Computation::with_witness(program, witness);

            let params = computation.clone().setup();
            let _proof = computation.prove(&params);
        }

        #[test]
        fn identity() {
            let program: Prog<Bn128Field> = Prog {
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

            let interpreter = Interpreter::default();

            let witness = interpreter
                .execute(&program, &[Bn128Field::from(0)])
                .unwrap();

            let computation = Computation::with_witness(program, witness);

            let params = computation.clone().setup();
            let _proof = computation.prove(&params);
        }

        #[test]
        fn public_identity() {
            let program: Prog<Bn128Field> = Prog {
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

            let interpreter = Interpreter::default();

            let witness = interpreter
                .execute(&program, &[Bn128Field::from(0)])
                .unwrap();

            let computation = Computation::with_witness(program, witness);

            let params = computation.clone().setup();
            let _proof = computation.prove(&params);
        }

        #[test]
        fn no_arguments() {
            let program: Prog<Bn128Field> = Prog {
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

            let interpreter = Interpreter::default();

            let witness = interpreter.execute(&program, &[]).unwrap();
            let computation = Computation::with_witness(program, witness);

            let params = computation.clone().setup();
            let _proof = computation.prove(&params);
        }

        #[test]
        fn unordered_variables() {
            // public variables must be ordered from 0
            // private variables can be unordered
            let program: Prog<Bn128Field> = Prog {
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

            let interpreter = Interpreter::default();

            let witness = interpreter
                .execute(&program, &[Bn128Field::from(3), Bn128Field::from(4)])
                .unwrap();
            let computation = Computation::with_witness(program, witness);

            let params = computation.clone().setup();
            let _proof = computation.prove(&params);
        }

        #[test]
        fn one() {
            let program: Prog<Bn128Field> = Prog {
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

            let interpreter = Interpreter::default();

            let witness = interpreter
                .execute(&program, &[Bn128Field::from(3)])
                .unwrap();

            let computation = Computation::with_witness(program, witness);

            let params = computation.clone().setup();
            let _proof = computation.prove(&params);
        }

        #[test]
        fn with_directives() {
            let program: Prog<Bn128Field> = Prog {
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

            let interpreter = Interpreter::default();

            let witness = interpreter
                .execute(&program, &[Bn128Field::from(3), Bn128Field::from(4)])
                .unwrap();
            let computation = Computation::with_witness(program, witness);

            let params = computation.clone().setup();
            let _proof = computation.prove(&params);
        }
    }
}
