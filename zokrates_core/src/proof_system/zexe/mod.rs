pub mod gm17;

use crate::ir::{CanonicalLinComb, Prog, Statement, Witness};
use zexe_gm17::Proof;
use zexe_gm17::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    Parameters,
};

use crate::flat_absy::FlatVariable;
use algebra_core::PairingEngine;
use r1cs_core::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, LinearCombination,
    SynthesisError, Variable,
};
use std::collections::BTreeMap;
use zokrates_field::{Field, ZexeFieldExtensions};

pub use self::parse::*;

use rand_0_7::SeedableRng;

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

fn zexe_combination<T: Field + ZexeFieldExtensions>(
    l: CanonicalLinComb<T>,
    cs: &mut ConstraintSystem<<<T as ZexeFieldExtensions>::ZexeEngine as PairingEngine>::Fr>,
    symbols: &mut BTreeMap<FlatVariable, Variable>,
    witness: &mut Witness<T>,
) -> Result<
    LinearCombination<<<T as ZexeFieldExtensions>::ZexeEngine as PairingEngine>::Fr>,
    SynthesisError,
> {
    let lc =
        l.0.into_iter()
            .map(|(k, v)| {
                (
                    v.into_zexe(),
                    symbols
                        .entry(k)
                        .or_insert_with(|| {
                            match k.is_output() {
                                true => cs.new_input_variable(|| {
                                    Ok(witness
                                        .0
                                        .remove(&k)
                                        .ok_or(SynthesisError::AssignmentMissing)?
                                        .into_zexe())
                                }),
                                false => cs.new_witness_variable(|| {
                                    Ok(witness
                                        .0
                                        .remove(&k)
                                        .ok_or(SynthesisError::AssignmentMissing)?
                                        .into_zexe())
                                }),
                            }
                            .unwrap()
                        })
                        .clone(),
                )
            })
            .fold(LinearCombination::zero(), |acc, e| acc + e);

    Ok(lc)
}

impl<T: Field + ZexeFieldExtensions> Prog<T> {
    pub fn generate_constraints(
        self,
        cs: ConstraintSystemRef<<<T as ZexeFieldExtensions>::ZexeEngine as PairingEngine>::Fr>,
        witness: Option<Witness<T>>,
    ) -> Result<(), SynthesisError> {
        // mapping from IR variables
        let mut symbols = BTreeMap::new();

        let mut witness = witness.unwrap_or(Witness::empty());

        assert!(symbols.insert(FlatVariable::one(), ConstraintSystem::<<<T as ZexeFieldExtensions>::ZexeEngine as PairingEngine>::Fr>::one()).is_none());

        match cs {
            ConstraintSystemRef::CS(rc) => {
                let mut cs = rc.borrow_mut();
                symbols.extend(
                    self.main
                        .arguments
                        .iter()
                        .zip(self.private)
                        .enumerate()
                        .map(|(_, (var, private))| {
                            let wire = match private {
                                true => cs.new_witness_variable(|| {
                                    Ok(witness
                                        .0
                                        .remove(&var)
                                        .ok_or(SynthesisError::AssignmentMissing)?
                                        .into_zexe())
                                }),
                                false => cs.new_input_variable(|| {
                                    Ok(witness
                                        .0
                                        .remove(&var)
                                        .ok_or(SynthesisError::AssignmentMissing)?
                                        .into_zexe())
                                }),
                            }
                            .unwrap();
                            (var.clone(), wire)
                        }),
                );

                let main = self.main;

                for statement in main.statements {
                    match statement {
                        Statement::Constraint(quad, lin) => {
                            let a = zexe_combination(
                                quad.left.clone().into_canonical(),
                                &mut cs,
                                &mut symbols,
                                &mut witness,
                            )?;
                            let b = zexe_combination(
                                quad.right.clone().into_canonical(),
                                &mut cs,
                                &mut symbols,
                                &mut witness,
                            )?;
                            let c = zexe_combination(
                                lin.into_canonical(),
                                &mut cs,
                                &mut symbols,
                                &mut witness,
                            )?;

                            cs.enforce_constraint(a, b, c)?;
                        }
                        _ => {}
                    }
                }

                Ok(())
            }
            ConstraintSystemRef::None => Err(SynthesisError::MissingCS),
        }
    }
}

impl<T: Field + ZexeFieldExtensions> Computation<T> {
    pub fn prove(self, params: &Parameters<T::ZexeEngine>) -> Proof<T::ZexeEngine> {
        let rng = &mut rand_0_7::rngs::StdRng::from_entropy();

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
        let rng = &mut rand_0_7::rngs::StdRng::from_entropy();

        // run setup phase
        generate_random_parameters(self, rng).unwrap()
    }
}

impl<T: Field + ZexeFieldExtensions>
    ConstraintSynthesizer<<<T as ZexeFieldExtensions>::ZexeEngine as PairingEngine>::Fr>
    for Computation<T>
{
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<<<T as ZexeFieldExtensions>::ZexeEngine as PairingEngine>::Fr>,
    ) -> Result<(), SynthesisError> {
        self.program.generate_constraints(cs, self.witness)
    }
}

mod parse {
    use lazy_static::lazy_static;

    use super::*;
    use proof_system::{Fr, G1Affine, G2Affine, G2AffineFq};
    use regex::Regex;

    lazy_static! {
        pub static ref G2_REGEX: Regex = Regex::new(r#"GroupAffine\(x=QuadExtField\(Fp\d{3} "\((?P<x0>[0-9a-fA-F]*)\)" \+ Fp\d{3} "\((?P<x1>[0-9a-fA-F]*)\)" \* u\), y=QuadExtField\(Fp\d{3} "\((?P<y0>[0-9a-fA-F]*)\)" \+ Fp\d{3} "\((?P<y1>[0-9a-fA-F]*)\)" \* u\)\)"#).unwrap();
    }

    lazy_static! {
        static ref G1_REGEX: Regex =
            Regex::new(r#"GroupAffine\(x=Fp\d{3} "\((?P<x>[0-9a-fA-F]*)\)", y=Fp\d{3} "\((?P<y>[0-9a-fA-F]*)\)"\)"#)
                .unwrap();
    }

    lazy_static! {
        static ref FR_REGEX: Regex = Regex::new(r#"Fp\d{3} "\((?P<x>[0-9a-fA-F]*)\)""#).unwrap();
    }

    lazy_static! {
        pub static ref G1_G2_REGEX_FQ: Regex = Regex::new(r#"GroupAffine\(x=Fp\d{3} "\((?P<x>[0-9a-fA-F]*)\)", y=Fp\d{3} "\((?P<y>[0-9a-fA-F]*)\)"\)"#).unwrap();
    }

    lazy_static! {
        static ref FR_REGEX_FQ: Regex = Regex::new(r#"Fp\d{3} "\((?P<x>[0-9a-fA-F]*)\)""#).unwrap();
    }

    pub fn parse_g1<T: Field + ZexeFieldExtensions>(
        e: &<T::ZexeEngine as PairingEngine>::G1Affine,
    ) -> G1Affine {
        let raw_e = e.to_string();
        match T::name() {
            "bw6_761" => {
                let captures = G1_G2_REGEX_FQ.captures(&raw_e).unwrap();
                G1Affine(
                    ("0x".to_string() + captures.name(&"x").unwrap().as_str()).to_string(),
                    ("0x".to_string() + captures.name(&"y").unwrap().as_str()).to_string(),
                )
            }
            _ => {
                let captures = G1_REGEX.captures(&raw_e).unwrap();
                G1Affine(
                    ("0x".to_string() + captures.name(&"x").unwrap().as_str()).to_string(),
                    ("0x".to_string() + captures.name(&"y").unwrap().as_str()).to_string(),
                )
            }
        }
    }

    pub fn parse_g2<T: ZexeFieldExtensions>(
        e: &<T::ZexeEngine as PairingEngine>::G2Affine,
    ) -> G2Affine {
        let raw_e = e.to_string();
        let captures = G2_REGEX.captures(&raw_e).unwrap();
        G2Affine(
            (
                ("0x".to_string() + captures.name(&"x0").unwrap().as_str()).to_string(),
                ("0x".to_string() + captures.name(&"x1").unwrap().as_str()).to_string(),
            ),
            (
                ("0x".to_string() + captures.name(&"y0").unwrap().as_str()).to_string(),
                ("0x".to_string() + captures.name(&"y1").unwrap().as_str()).to_string(),
            ),
        )
    }

    pub fn parse_g2_fq<T: ZexeFieldExtensions>(
        e: &<T::ZexeEngine as PairingEngine>::G2Affine,
    ) -> G2AffineFq {
        let raw_e = e.to_string();
        let captures = G1_G2_REGEX_FQ.captures(&raw_e).unwrap();
        G2AffineFq(
            ("0x".to_string() + captures.name(&"x").unwrap().as_str()).to_string(),
            ("0x".to_string() + captures.name(&"y").unwrap().as_str()).to_string(),
        )
    }

    pub fn parse_fr<T: ZexeFieldExtensions>(e: &<T::ZexeEngine as PairingEngine>::Fr) -> Fr {
        let raw_e = e.to_string();
        let captures = FR_REGEX.captures(&raw_e).unwrap();
        ("0x".to_string() + captures.name(&"x").unwrap().as_str()).to_string()
    }
}
