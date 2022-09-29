//pub mod groth16;
// pub mod nova;

use bellperson::gadgets::num::AllocatedNum;
use bellperson::{
    Circuit, ConstraintSystem, LinearCombination, SynthesisError, Variable as BellpersonVariable,
};

use std::collections::BTreeMap;
use zokrates_ast::common::Variable;
use zokrates_ast::ir::{CanonicalLinComb, ProgIterator, Statement, Witness};
use zokrates_field::BellpersonFieldExtensions;
use zokrates_field::Field;

pub struct Bellperson;

#[derive(Clone, Debug)]
pub struct Computation<T, I: IntoIterator<Item = Statement<T>>> {
    pub program: ProgIterator<T, I>,
    pub witness: Option<Witness<T>>,
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

fn bellperson_combination<
    T: BellpersonFieldExtensions,
    CS: ConstraintSystem<T::BellpersonField>,
>(
    l: CanonicalLinComb<T>,
    cs: &mut CS,
    symbols: &mut BTreeMap<Variable, BellpersonVariable>,
    witness: &mut Witness<T>,
) -> LinearCombination<T::BellpersonField> {
    l.0.into_iter()
        .map(|(k, v)| {
            (
                v.into_bellperson(),
                *symbols.entry(k).or_insert_with(|| {
                    match k.is_output() {
                        true => unreachable!("outputs should already have been allocated"),
                        false => AllocatedNum::alloc(cs.namespace(|| format!("{}", k)), || {
                            Ok(witness
                                .0
                                .remove(&k)
                                .ok_or(SynthesisError::AssignmentMissing)?
                                .into_bellperson())
                        }),
                    }
                    .unwrap()
                    .get_variable()
                }),
            )
        })
        .fold(LinearCombination::zero(), |acc, e| acc + e)
}

impl<T: BellpersonFieldExtensions + Field, I: IntoIterator<Item = Statement<T>>>
    Circuit<T::BellpersonField> for Computation<T, I>
{
    fn synthesize<CS: ConstraintSystem<T::BellpersonField>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let mut symbols = BTreeMap::new();

        let mut witness = self.witness.clone().unwrap_or_else(Witness::empty);

        assert!(symbols.insert(Variable::one(), CS::one()).is_none());

        symbols.extend(self.program.arguments.iter().enumerate().map(|(index, p)| {
            let wire = match p.private {
                true => {
                    AllocatedNum::alloc(cs.namespace(|| format!("PRIVATE_INPUT_{}", index)), || {
                        Ok(witness
                            .0
                            .remove(&p.id)
                            .ok_or(SynthesisError::AssignmentMissing)?
                            .into_bellperson())
                    })
                }
                false => AllocatedNum::alloc_input(
                    cs.namespace(|| format!("PUBLIC_INPUT_{}", index)),
                    || {
                        Ok(witness
                            .0
                            .remove(&p.id)
                            .ok_or(SynthesisError::AssignmentMissing)?
                            .into_bellperson())
                    },
                ),
            }
            .unwrap();
            (p.id, wire.get_variable())
        }));

        self.program.returns().iter().for_each(|v| {
            assert!(v.id < 0); // this should indeed be an output
            let wire = AllocatedNum::alloc_input(
                cs.namespace(|| format!("PUBLIC_OUTPUT_{}", -v.id - 1)),
                || {
                    Ok(witness
                        .0
                        .remove(v)
                        .ok_or(SynthesisError::AssignmentMissing)?
                        .into_bellperson())
                },
            )
            .unwrap();
            symbols.insert(*v, wire.get_variable());
        });

        self.synthesize_input_to_output(cs, &mut symbols, &mut witness)
    }
}

impl<T: BellpersonFieldExtensions + Field, I: IntoIterator<Item = Statement<T>>> Computation<T, I> {
    pub fn synthesize_input_to_output<CS: ConstraintSystem<T::BellpersonField>>(
        self,
        cs: &mut CS,
        symbols: &mut BTreeMap<Variable, BellpersonVariable>,
        witness: &mut Witness<T>,
    ) -> Result<(), SynthesisError> {
        for (i, statement) in self.program.statements.into_iter().enumerate() {
            if let Statement::Constraint(quad, lin, _) = statement {
                let a = &bellperson_combination(quad.left.into_canonical(), cs, symbols, witness);
                let b = &bellperson_combination(quad.right.into_canonical(), cs, symbols, witness);
                let c = &bellperson_combination(lin.into_canonical(), cs, symbols, witness);

                cs.enforce(
                    || format!("Constraint {}", i),
                    |lc| lc + a,
                    |lc| lc + b,
                    |lc| lc + c,
                );
            }
        }

        Ok(())
    }

    pub fn public_inputs_values(&self) -> Vec<T::BellpersonField> {
        self.program
            .public_inputs_values(self.witness.as_ref().unwrap())
            .iter()
            .map(|v| v.clone().into_bellperson())
            .collect()
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
