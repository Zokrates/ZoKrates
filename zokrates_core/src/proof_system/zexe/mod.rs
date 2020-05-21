pub mod gm17;

extern crate rand;

use crate::ir::{CanonicalLinComb, Prog, Statement, Witness};
use zexe::gm17::Proof;
use zexe::gm17::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    Parameters,
};
use bellman::pairing::ff::ScalarEngine;
use bellman::{Circuit, ConstraintSystem, LinearCombination, SynthesisError, Variable};
use std::collections::BTreeMap;
use zokrates_field::Field;

use self::rand::ChaChaRng;
use crate::flat_absy::FlatVariable;

pub use self::parse::*;

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

impl<T: Field> Computation<T> {
    pub fn prove(self, params: &Parameters<T::BellmanEngine>) -> Proof<T::BellmanEngine> {
        let rng = &mut ChaChaRng::new_unseeded();

        let proof = create_random_proof(self.clone(), params, rng).unwrap();

        let pvk = prepare_verifying_key(&params.vk);

        // extract public inputs
        let public_inputs = self.public_inputs_values();

        assert!(verify_proof(&pvk, &proof, &public_inputs).unwrap());

        proof
    }

    pub fn public_inputs_values(&self) -> Vec<<T::BellmanEngine as ScalarEngine>::Fr> {
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

    pub fn setup(self) -> Parameters<T::BellmanEngine> {
        let rng = &mut ChaChaRng::new_unseeded();
        // run setup phase
        generate_random_parameters(self, rng).unwrap()
    }
}


mod parse {
    use lazy_static::lazy_static;

    use super::*;
    use proof_system::{G1Affine, G2Affine};
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

    pub fn parse_g1<T: Field>(
        e: &<T::BellmanEngine as bellman::pairing::Engine>::G1Affine,
    ) -> G1Affine {
        let raw_e = e.to_string();
        let captures = G1_REGEX.captures(&raw_e).unwrap();
        G1Affine(
            captures.name(&"x").unwrap().as_str().to_string(),
            captures.name(&"y").unwrap().as_str().to_string(),
        )
    }

    pub fn parse_g2<T: Field>(
        e: &<T::BellmanEngine as bellman::pairing::Engine>::G2Affine,
    ) -> G2Affine {
        let raw_e = e.to_string();
        let captures = G2_REGEX.captures(&raw_e).unwrap();
        G2Affine(
            G1Affine(
                captures.name(&"x1").unwrap().as_str().to_string(),
                captures.name(&"x0").unwrap().as_str().to_string(),
            ),
            G1Affine(
                captures.name(&"y1").unwrap().as_str().to_string(),
                captures.name(&"y0").unwrap().as_str().to_string(),
            ),
        )
    }

    pub fn parse_fr<T: Field>(e: &<T::BellmanEngine as ScalarEngine>::Fr) -> String {
        let raw_e = e.to_string();
        let captures = FR_REGEX.captures(&raw_e).unwrap();
        captures.name(&"x").unwrap().as_str().to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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

            let witness = program.clone().execute(&vec![]).unwrap();
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

            let witness = program.clone().execute(&vec![Bn128Field::from(0)]).unwrap();
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

            let witness = program.clone().execute(&vec![Bn128Field::from(0)]).unwrap();
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

            let witness = program.clone().execute(&vec![]).unwrap();
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

            let witness = program
                .clone()
                .execute(&vec![Bn128Field::from(3), Bn128Field::from(4)])
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

            let witness = program.clone().execute(&vec![Bn128Field::from(3)]).unwrap();
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

            let witness = program
                .clone()
                .execute(&vec![Bn128Field::from(3), Bn128Field::from(4)])
                .unwrap();
            let computation = Computation::with_witness(program, witness);

            let params = computation.clone().setup();
            let _proof = computation.prove(&params);
        }
    }
}
