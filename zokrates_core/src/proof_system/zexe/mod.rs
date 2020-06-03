pub mod gm17;

use crate::ir::{CanonicalLinComb, Prog, Statement, Witness};
use zexe_gm17::Proof;
use zexe_gm17::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    Parameters,
};

use r1cs_core::{
    ConstraintSynthesizer, ConstraintSystem, LinearCombination, SynthesisError, Variable,
};
use std::collections::BTreeMap;
// use rand::rngs::StdRng;
use crate::flat_absy::FlatVariable;
use algebra_core::PairingEngine;
use zokrates_field::{Field, ZexeFieldExtensions};

pub use self::parse::*;

pub fn test_rng() -> rand_0_7::rngs::StdRng {
    use rand_0_7::SeedableRng;

    // arbitrary seed
    let seed = [
        1, 0, 0, 0, 23, 0, 0, 0, 200, 1, 0, 0, 210, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0,
    ];
    rand_0_7::rngs::StdRng::from_seed(seed)
}

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

fn zexe_combination<
    T: Field + ZexeFieldExtensions,
    CS: ConstraintSystem<<<T as ZexeFieldExtensions>::ZexeEngine as PairingEngine>::Fr>,
>(
    l: CanonicalLinComb<T>,
    cs: &mut CS,
    symbols: &mut BTreeMap<FlatVariable, Variable>,
    witness: &mut Witness<T>,
) -> LinearCombination<<<T as ZexeFieldExtensions>::ZexeEngine as PairingEngine>::Fr> {
    l.0.into_iter()
        .map(|(k, v)| {
            (
                v.into_zexe(),
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
                                        .into_zexe())
                                },
                            ),
                            false => cs.alloc(
                                || format!("{}", k),
                                || {
                                    Ok(witness
                                        .0
                                        .remove(&k)
                                        .ok_or(SynthesisError::AssignmentMissing)?
                                        .into_zexe())
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

impl<T: Field + ZexeFieldExtensions> Prog<T> {
    pub fn generate_constraints<
        CS: ConstraintSystem<<<T as ZexeFieldExtensions>::ZexeEngine as PairingEngine>::Fr>,
    >(
        self,
        cs: &mut CS,
        witness: Option<Witness<T>>,
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
                                    .into_zexe())
                            },
                        ),
                        false => cs.alloc_input(
                            || format!("PUBLIC_INPUT_{}", index),
                            || {
                                Ok(witness
                                    .0
                                    .remove(&var)
                                    .ok_or(SynthesisError::AssignmentMissing)?
                                    .into_zexe())
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
                    let a = &zexe_combination(
                        quad.left.clone().as_canonical(),
                        cs,
                        &mut symbols,
                        &mut witness,
                    );
                    let b = &zexe_combination(
                        quad.right.clone().as_canonical(),
                        cs,
                        &mut symbols,
                        &mut witness,
                    );
                    let c = &zexe_combination(lin.as_canonical(), cs, &mut symbols, &mut witness);

                    cs.enforce(|| "Constraint", |lc| lc + a, |lc| lc + b, |lc| lc + c);
                }
                _ => {}
            }
        }

        Ok(())
    }
}

impl<T: Field + ZexeFieldExtensions> Computation<T> {
    pub fn prove(self, params: &Parameters<T::ZexeEngine>) -> Proof<T::ZexeEngine> {
        let rng = &mut test_rng();
        // let rng = &mut ChaChaRng::new_unseeded();

        let proof = create_random_proof(self.clone(), params, rng).unwrap();

        let pvk = prepare_verifying_key(&params.vk);

        // extract public inputs
        let public_inputs = self.public_inputs_values();

        assert!(verify_proof(&pvk, &proof, &public_inputs).unwrap());

        proof
    }

    pub fn public_inputs_values(&self) -> Vec<<T::ZexeEngine as PairingEngine>::Fr> {
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
            .map(|v| v.clone().into_zexe())
            .collect()
    }

    pub fn setup(self) -> Parameters<T::ZexeEngine> {
        let rng = &mut test_rng();
        // let rng = &mut ChaChaRng::new_unseeded();
        // run setup phase
        generate_random_parameters(self, rng).unwrap()
    }
}

impl<T: Field + ZexeFieldExtensions>
    ConstraintSynthesizer<<<T as ZexeFieldExtensions>::ZexeEngine as PairingEngine>::Fr>
    for Computation<T>
{
    fn generate_constraints<
        CS: ConstraintSystem<<<T as ZexeFieldExtensions>::ZexeEngine as PairingEngine>::Fr>,
    >(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        self.program.generate_constraints(cs, self.witness)
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

    //ZexeEngine as algebra_core::curves::PairingEngine
    pub fn parse_g1<T: ZexeFieldExtensions>(
        e: &<T::ZexeEngine as PairingEngine>::G1Affine,
    ) -> G1Affine {
        let raw_e = e.to_string();
        let captures = G1_REGEX.captures(&raw_e).unwrap();
        G1Affine(
            captures.name(&"x").unwrap().as_str().to_string(),
            captures.name(&"y").unwrap().as_str().to_string(),
        )
    }

    pub fn parse_g2<T: ZexeFieldExtensions>(
        e: &<T::ZexeEngine as PairingEngine>::G2Affine,
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

    pub fn parse_fr<T: ZexeFieldExtensions>(e: &<T::ZexeEngine as PairingEngine>::Fr) -> String {
        let raw_e = e.to_string();
        let captures = FR_REGEX.captures(&raw_e).unwrap();
        captures.name(&"x").unwrap().as_str().to_string()
    }
}
