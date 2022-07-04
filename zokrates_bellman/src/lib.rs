pub mod groth16;

use bellman::groth16::Proof;
use bellman::groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    Parameters,
};
use bellman::pairing::ff::ScalarEngine;
use bellman::{
    Circuit, ConstraintSystem, LinearCombination, SynthesisError, Variable as BellmanVariable,
};
use std::collections::BTreeMap;
use zokrates_ast::common::Variable;
use zokrates_ast::ir::{CanonicalLinComb, ProgIterator, Statement, Witness};
use zokrates_field::BellmanFieldExtensions;
use zokrates_field::Field;

use rand_0_4::ChaChaRng;

pub use self::parse::*;

pub struct Bellman;

#[derive(Clone)]
pub struct Computation<T, I: IntoIterator<Item = Statement<T>>> {
    program: ProgIterator<T, I>,
    witness: Option<Witness<T>>,
}

impl<T: Field, I: IntoIterator<Item = Statement<T>>> Computation<T, I> {
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

fn bellman_combination<T: BellmanFieldExtensions, CS: ConstraintSystem<T::BellmanEngine>>(
    l: CanonicalLinComb<T>,
    cs: &mut CS,
    symbols: &mut BTreeMap<Variable, BellmanVariable>,
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

impl<T: BellmanFieldExtensions + Field, I: IntoIterator<Item = Statement<T>>>
    Circuit<T::BellmanEngine> for Computation<T, I>
{
    fn synthesize<CS: ConstraintSystem<T::BellmanEngine>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        // mapping from IR variables
        let mut symbols = BTreeMap::new();

        let mut witness = self.witness.unwrap_or_else(Witness::empty);

        assert!(symbols.insert(Variable::one(), CS::one()).is_none());

        symbols.extend(self.program.arguments.iter().enumerate().map(|(index, p)| {
            let wire = match p.private {
                true => cs.alloc(
                    || format!("PRIVATE_INPUT_{}", index),
                    || {
                        Ok(witness
                            .0
                            .remove(&p.id)
                            .ok_or(SynthesisError::AssignmentMissing)?
                            .into_bellman())
                    },
                ),
                false => cs.alloc_input(
                    || format!("PUBLIC_INPUT_{}", index),
                    || {
                        Ok(witness
                            .0
                            .remove(&p.id)
                            .ok_or(SynthesisError::AssignmentMissing)?
                            .into_bellman())
                    },
                ),
            }
            .unwrap();
            (p.id, wire)
        }));

        for statement in self.program.statements {
            if let Statement::Constraint(quad, lin, _) = statement {
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

impl<T: BellmanFieldExtensions + Field, I: IntoIterator<Item = Statement<T>>> Computation<T, I> {
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

        // extract public inputs
        let public_inputs = self.public_inputs_values();

        let proof = create_random_proof(self, params, rng).unwrap();

        let pvk = prepare_verifying_key(&params.vk);

        assert!(verify_proof(&pvk, &proof, &public_inputs).unwrap());

        proof
    }

    pub fn public_inputs_values(&self) -> Vec<<T::BellmanEngine as ScalarEngine>::Fr> {
        self.program
            .public_inputs_values(self.witness.as_ref().unwrap())
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

mod parse {
    use super::*;
    use pairing::CurveAffine;
    use zokrates_proof_systems::{G1Affine, G2Affine, G2AffineFq2};

    fn to_hex(bytes: &[u8]) -> String {
        let mut hex = hex::encode(bytes);
        hex.insert_str(0, "0x");
        hex
    }

    pub fn parse_g1<T: BellmanFieldExtensions>(
        e: &<T::BellmanEngine as bellman::pairing::Engine>::G1Affine,
    ) -> G1Affine {
        let uncompressed = e.into_uncompressed();
        let bytes: &[u8] = uncompressed.as_ref();

        let mut iter = bytes.chunks(bytes.len() / 2);
        let x = to_hex(iter.next().unwrap());
        let y = to_hex(iter.next().unwrap());

        G1Affine(x, y)
    }

    pub fn parse_g2<T: BellmanFieldExtensions>(
        e: &<T::BellmanEngine as bellman::pairing::Engine>::G2Affine,
    ) -> G2Affine {
        let uncompressed = e.into_uncompressed();
        let bytes: &[u8] = uncompressed.as_ref();

        let mut iter = bytes.chunks(bytes.len() / 4);
        let x1 = to_hex(iter.next().unwrap());
        let x0 = to_hex(iter.next().unwrap());
        let y1 = to_hex(iter.next().unwrap());
        let y0 = to_hex(iter.next().unwrap());

        G2Affine::Fq2(G2AffineFq2((x0, x1), (y0, y1)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_ast::ir::LinComb;
    use zokrates_field::Bn128Field;
    use zokrates_interpreter::Interpreter;

    mod prove {
        use super::*;
        use zokrates_ast::flat::Parameter;
        use zokrates_ast::ir::Prog;

        #[test]
        fn empty() {
            let program: Prog<Bn128Field> = Prog::default();

            let interpreter = Interpreter::default();

            let witness = interpreter.execute(program.clone(), &[]).unwrap();
            let computation = Computation::with_witness(program, witness);

            let params = computation.clone().setup();
            let _proof = computation.prove(&params);
        }

        #[test]
        fn identity() {
            let program: Prog<Bn128Field> = Prog {
                arguments: vec![Parameter::private(Variable::new(0))],
                return_count: 1,
                statements: vec![Statement::constraint(Variable::new(0), Variable::public(0))],
            };

            let interpreter = Interpreter::default();

            let witness = interpreter
                .execute(program.clone(), &[Bn128Field::from(0)])
                .unwrap();

            let computation = Computation::with_witness(program, witness);

            let params = computation.clone().setup();
            let _proof = computation.prove(&params);
        }

        #[test]
        fn public_identity() {
            let program: Prog<Bn128Field> = Prog {
                arguments: vec![Parameter::public(Variable::new(0))],
                return_count: 1,
                statements: vec![Statement::constraint(Variable::new(0), Variable::public(0))],
            };

            let interpreter = Interpreter::default();

            let witness = interpreter
                .execute(program.clone(), &[Bn128Field::from(0)])
                .unwrap();

            let computation = Computation::with_witness(program, witness);

            let params = computation.clone().setup();
            let _proof = computation.prove(&params);
        }

        #[test]
        fn no_arguments() {
            let program: Prog<Bn128Field> = Prog {
                arguments: vec![],
                return_count: 1,
                statements: vec![Statement::constraint(Variable::one(), Variable::public(0))],
            };

            let interpreter = Interpreter::default();

            let witness = interpreter.execute(program.clone(), &[]).unwrap();
            let computation = Computation::with_witness(program, witness);

            let params = computation.clone().setup();
            let _proof = computation.prove(&params);
        }

        #[test]
        fn unordered_variables() {
            // public variables must be ordered from 0
            // private variables can be unordered
            let program: Prog<Bn128Field> = Prog {
                arguments: vec![
                    Parameter::private(Variable::new(42)),
                    Parameter::public(Variable::new(51)),
                ],
                return_count: 2,
                statements: vec![
                    Statement::constraint(
                        LinComb::from(Variable::new(42)) + LinComb::from(Variable::new(51)),
                        Variable::public(0),
                    ),
                    Statement::constraint(
                        LinComb::from(Variable::one()) + LinComb::from(Variable::new(42)),
                        Variable::public(1),
                    ),
                ],
            };

            let interpreter = Interpreter::default();

            let witness = interpreter
                .execute(program.clone(), &[Bn128Field::from(3), Bn128Field::from(4)])
                .unwrap();
            let computation = Computation::with_witness(program, witness);

            let params = computation.clone().setup();
            let _proof = computation.prove(&params);
        }

        #[test]
        fn one() {
            let program: Prog<Bn128Field> = Prog {
                arguments: vec![Parameter::public(Variable::new(42))],
                return_count: 1,
                statements: vec![Statement::constraint(
                    LinComb::from(Variable::new(42)) + LinComb::one(),
                    Variable::public(0),
                )],
            };

            let interpreter = Interpreter::default();

            let witness = interpreter
                .execute(program.clone(), &[Bn128Field::from(3)])
                .unwrap();

            let computation = Computation::with_witness(program, witness);

            let params = computation.clone().setup();
            let _proof = computation.prove(&params);
        }

        #[test]
        fn with_directives() {
            let program: Prog<Bn128Field> = Prog {
                arguments: vec![
                    Parameter::private(Variable::new(42)),
                    Parameter::public(Variable::new(51)),
                ],
                return_count: 1,
                statements: vec![Statement::constraint(
                    LinComb::from(Variable::new(42)) + LinComb::from(Variable::new(51)),
                    Variable::public(0),
                )],
            };

            let interpreter = Interpreter::default();

            let witness = interpreter
                .execute(program.clone(), &[Bn128Field::from(3), Bn128Field::from(4)])
                .unwrap();
            let computation = Computation::with_witness(program, witness);

            let params = computation.clone().setup();
            let _proof = computation.prove(&params);
        }
    }
}
