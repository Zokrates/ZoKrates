pub mod gm17;
pub mod groth16;
pub mod marlin;

use ark_ec::PairingEngine;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, LinearCombination,
    SynthesisError, Variable as ArkVariable,
};
use std::collections::BTreeMap;
use zokrates_ast::common::Variable;
use zokrates_ast::ir::{CanonicalLinComb, ProgIterator, Statement, Witness};
use zokrates_field::{ArkFieldExtensions, Field};

pub use self::parse::*;

pub struct Ark;

#[derive(Clone)]
pub struct Computation<T, I: IntoIterator<Item = Statement<T>>> {
    program: ProgIterator<T, I>,
    witness: Option<Witness<T>>,
}

impl<T, I: IntoIterator<Item = Statement<T>>> Computation<T, I> {
    pub fn with_witness(program: ProgIterator<T, I>, witness: Witness<T>) -> Self {
        Computation {
            program,
            witness: Some(witness),
        }
    }

    pub fn without_witness(program: ProgIterator<T, I>) -> Self {
        Computation {
            program,
            witness: None,
        }
    }
}

fn ark_combination<T: Field + ArkFieldExtensions>(
    l: CanonicalLinComb<T>,
    cs: &mut ConstraintSystem<<<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr>,
    symbols: &mut BTreeMap<Variable, ArkVariable>,
    witness: &mut Witness<T>,
) -> LinearCombination<<<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr> {
    l.0.into_iter()
        .map(|(k, v)| {
            (
                v.into_ark(),
                *symbols.entry(k).or_insert_with(|| {
                    match k.is_output() {
                        true => cs.new_input_variable(|| {
                            Ok(witness
                                .0
                                .remove(&k)
                                .ok_or(SynthesisError::AssignmentMissing)?
                                .into_ark())
                        }),
                        false => cs.new_witness_variable(|| {
                            Ok(witness
                                .0
                                .remove(&k)
                                .ok_or(SynthesisError::AssignmentMissing)?
                                .into_ark())
                        }),
                    }
                    .unwrap()
                }),
            )
        })
        .fold(LinearCombination::zero(), |acc, e| acc + e)
}

impl<T: Field + ArkFieldExtensions, I: IntoIterator<Item = Statement<T>>>
    ConstraintSynthesizer<<<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr>
    for Computation<T, I>
{
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<<<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr>,
    ) -> Result<(), SynthesisError> {
        // mapping from IR variables
        let mut symbols = BTreeMap::new();

        let mut witness = self.witness.unwrap_or_else(Witness::empty);

        assert!(symbols.insert(Variable::one(), ConstraintSystem::<<<T as ArkFieldExtensions>::ArkEngine as PairingEngine>::Fr>::one()).is_none());

        match cs {
            ConstraintSystemRef::CS(rc) => {
                let mut cs = rc.borrow_mut();
                symbols.extend(self.program.arguments.iter().enumerate().map(|(_, p)| {
                    let wire = match p.private {
                        true => cs.new_witness_variable(|| {
                            Ok(witness
                                .0
                                .remove(&p.id)
                                .ok_or(SynthesisError::AssignmentMissing)?
                                .into_ark())
                        }),
                        false => cs.new_input_variable(|| {
                            Ok(witness
                                .0
                                .remove(&p.id)
                                .ok_or(SynthesisError::AssignmentMissing)?
                                .into_ark())
                        }),
                    }
                    .unwrap();
                    (p.id, wire)
                }));

                for statement in self.program.statements {
                    if let Statement::Constraint(quad, lin, _) = statement {
                        let a = ark_combination(
                            quad.left.clone().into_canonical(),
                            &mut cs,
                            &mut symbols,
                            &mut witness,
                        );
                        let b = ark_combination(
                            quad.right.clone().into_canonical(),
                            &mut cs,
                            &mut symbols,
                            &mut witness,
                        );
                        let c = ark_combination(
                            lin.into_canonical(),
                            &mut cs,
                            &mut symbols,
                            &mut witness,
                        );

                        cs.enforce_constraint(a, b, c)?;
                    }
                }

                Ok(())
            }
            ConstraintSystemRef::None => Err(SynthesisError::MissingCS),
        }
    }
}

impl<T: Field + ArkFieldExtensions, I: IntoIterator<Item = Statement<T>>> Computation<T, I> {
    pub fn public_inputs_values(&self) -> Vec<<T::ArkEngine as PairingEngine>::Fr> {
        self.program
            .public_inputs_values(self.witness.as_ref().unwrap())
            .iter()
            .map(|v| v.clone().into_ark())
            .collect()
    }
}

mod parse {
    use super::*;
    use ark_ff::ToBytes;
    use zokrates_field::G2Type;
    use zokrates_proof_systems::{Fq2, Fr, G1Affine, G2Affine, G2AffineFq, GAffine};

    pub fn parse_g1<T: Field + ArkFieldExtensions>(
        e: &<T::ArkEngine as PairingEngine>::G1Affine,
    ) -> G1Affine {
        let mut bytes: Vec<u8> = Vec::new();
        e.write(&mut bytes).unwrap();

        let length = bytes.len() - 1; // [x, y, infinity] - infinity
        let element_length = length / 2;

        let mut x = bytes[0..element_length].to_vec();
        let mut y = bytes[element_length..length].to_vec();

        x.reverse();
        y.reverse();

        G1Affine::new(
            format!("0x{}", hex::encode(&x)),
            format!("0x{}", hex::encode(&y)),
        )
    }

    pub fn parse_g2<T: Field + ArkFieldExtensions>(
        e: &<T::ArkEngine as PairingEngine>::G2Affine,
    ) -> G2Affine {
        let mut bytes: Vec<u8> = Vec::new();
        e.write(&mut bytes).unwrap();

        let length = bytes.len() - 1; // [x, y, infinity] - infinity

        match T::G2_TYPE {
            G2Type::Fq2 => {
                let element_length = length / 4;

                let mut elements = vec![];
                for i in 0..4 {
                    let start = i * element_length;
                    let end = start + element_length;
                    let mut e = bytes[start..end].to_vec();
                    e.reverse();
                    elements.push(e);
                }

                G2Affine::Fq2(GAffine::new(
                    Fq2(
                        format!("0x{}", hex::encode(&elements[0])),
                        format!("0x{}", hex::encode(&elements[1])),
                    ),
                    Fq2(
                        format!("0x{}", hex::encode(&elements[2])),
                        format!("0x{}", hex::encode(&elements[3])),
                    ),
                ))
            }
            G2Type::Fq => {
                let element_length = length / 2;

                let mut x = bytes[0..element_length].to_vec();
                let mut y = bytes[element_length..length].to_vec();

                x.reverse();
                y.reverse();

                G2Affine::Fq(G2AffineFq::new(
                    format!("0x{}", hex::encode(&x)),
                    format!("0x{}", hex::encode(&y)),
                ))
            }
        }
    }

    pub fn parse_fr<T: ArkFieldExtensions>(e: &<T::ArkEngine as PairingEngine>::Fr) -> Fr {
        let mut bytes: Vec<u8> = Vec::new();
        e.write(&mut bytes).unwrap();
        bytes.reverse();

        format!("0x{}", hex::encode(&bytes))
    }
}

pub mod serialization {
    use ark_ec::PairingEngine;
    use ark_ff::FromBytes;
    use zokrates_field::ArkFieldExtensions;
    use zokrates_proof_systems::{G1Affine, G2Affine};

    #[inline]
    fn decode_hex(value: String) -> Vec<u8> {
        let mut bytes = hex::decode(value.strip_prefix("0x").unwrap()).unwrap();
        bytes.reverse();
        bytes
    }

    pub fn to_g1<T: ArkFieldExtensions>(g1: G1Affine) -> <T::ArkEngine as PairingEngine>::G1Affine {
        let infinity_flag = if g1.is_infinity { 1u8 } else { 0u8 };

        let mut bytes = vec![];
        bytes.append(&mut decode_hex(g1.x));
        bytes.append(&mut decode_hex(g1.y));
        bytes.push(infinity_flag); // infinity flag

        <T::ArkEngine as PairingEngine>::G1Affine::read(&*bytes).unwrap()
    }

    pub fn to_g2<T: ArkFieldExtensions>(g2: G2Affine) -> <T::ArkEngine as PairingEngine>::G2Affine {
        let mut bytes = vec![];

        match g2 {
            G2Affine::Fq(g2) => {
                let infinity_flag = if g2.is_infinity { 1u8 } else { 0u8 };

                bytes.append(&mut decode_hex(g2.x));
                bytes.append(&mut decode_hex(g2.y));
                bytes.push(infinity_flag); // infinity flag
            }
            G2Affine::Fq2(g2) => {
                let infinity_flag = if g2.is_infinity { 1u8 } else { 0u8 };

                bytes.append(&mut decode_hex((g2.x).0));
                bytes.append(&mut decode_hex((g2.x).1));
                bytes.append(&mut decode_hex((g2.y).0));
                bytes.append(&mut decode_hex((g2.y).1));
                bytes.push(infinity_flag); // infinity flag
            }
        };

        <T::ArkEngine as PairingEngine>::G2Affine::read(&*bytes).unwrap()
    }
}
