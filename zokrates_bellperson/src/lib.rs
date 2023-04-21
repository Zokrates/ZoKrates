pub mod nova;

use bellperson::gadgets::num::AllocatedNum;
use bellperson::{
    Circuit, ConstraintSystem, LinearCombination, SynthesisError, Variable as BellpersonVariable,
};

use std::collections::BTreeMap;
use zokrates_ast::common::flat::Variable;
use zokrates_ast::ir::{LinComb, Prog, Statement, Witness};
use zokrates_field::BellpersonFieldExtensions;
use zokrates_field::Field;

pub struct Bellperson;

#[derive(Clone, Debug)]
pub struct Computation<'ast, T> {
    pub program: &'ast Prog<'ast, T>,
    pub witness: Option<Witness<T>>,
}

impl<'ast, T: Field> Computation<'ast, T> {
    pub fn with_witness(program: &'ast Prog<'ast, T>, witness: Witness<T>) -> Self {
        Computation {
            program,
            witness: Some(witness),
        }
    }

    pub fn without_witness(program: &'ast Prog<'ast, T>) -> Self {
        Computation {
            program,
            witness: None,
        }
    }
}

fn bellperson_combination<
    T: Field + BellpersonFieldExtensions,
    CS: ConstraintSystem<T::BellpersonField>,
>(
    l: &LinComb<T>,
    cs: &mut CS,
    symbols: &mut BTreeMap<Variable, BellpersonVariable>,
    witness: &mut Witness<T>,
) -> LinearCombination<T::BellpersonField> {
    l.value
        .iter()
        .map(|(k, v)| {
            (
                v.into_bellperson(),
                *symbols.entry(*k).or_insert_with(|| {
                    match k.is_output() {
                        true => {
                            unreachable!("outputs should already have been allocated, found {}", k)
                        }
                        false => AllocatedNum::alloc(cs.namespace(|| format!("{}", k)), || {
                            Ok(witness
                                .0
                                .remove(k)
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

impl<'ast, T: BellpersonFieldExtensions + Field> Circuit<T::BellpersonField>
    for Computation<'ast, T>
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

impl<'ast, T: BellpersonFieldExtensions + Field> Computation<'ast, T> {
    pub fn synthesize_input_to_output<CS: ConstraintSystem<T::BellpersonField>>(
        &self,
        cs: &mut CS,
        symbols: &mut BTreeMap<Variable, BellpersonVariable>,
        witness: &mut Witness<T>,
    ) -> Result<(), SynthesisError> {
        for (i, statement) in self.program.statements.iter().enumerate() {
            if let Statement::Constraint(constraint) = statement {
                let a = &bellperson_combination(&constraint.quad.left, cs, symbols, witness);
                let b = &bellperson_combination(&constraint.quad.right, cs, symbols, witness);
                let c = &bellperson_combination(&constraint.lin, cs, symbols, witness);

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
            .map(|v| v.into_bellperson())
            .collect()
    }
}
