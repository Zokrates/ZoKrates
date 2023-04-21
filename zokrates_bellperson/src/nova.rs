use std::collections::BTreeMap;

use crate::Computation;
use bellperson::gadgets::num::AllocatedNum;
use bellperson::SynthesisError;
use ff::Field as FFField;
use nova_snark::errors::NovaError;
pub use nova_snark::traits::circuit::StepCircuit;
pub use nova_snark::traits::circuit::TrivialTestCircuit;
use nova_snark::traits::Group;
use nova_snark::CompressedSNARK as GCompressedSNARK;
pub use nova_snark::PublicParams as GPublicParams;
pub use nova_snark::RecursiveSNARK as GRecursiveSNARK;
use nova_snark::VerifierKey as GVerifierKey;
use serde::{Deserialize, Serialize};
use std::fmt;
use zokrates_ast::ir::*;
use zokrates_field::{BellpersonFieldExtensions, Cycle, Field};
use zokrates_interpreter::Interpreter;

pub trait NovaField:
    Field
    + BellpersonFieldExtensions<BellpersonField = <<Self as Cycle>::Point as Group>::Scalar>
    + Cycle
{
}

impl<
        T: Field
            + BellpersonFieldExtensions<BellpersonField = <<Self as Cycle>::Point as Group>::Scalar>
            + Cycle,
    > NovaField for T
{
}

#[derive(Clone, Debug)]
pub struct NovaComputation<'ast, T> {
    step_private: Option<Vec<T>>,
    computation: Computation<'ast, T>,
}

impl<'ast, T> TryFrom<Computation<'ast, T>> for NovaComputation<'ast, T> {
    type Error = Error;
    fn try_from(c: Computation<'ast, T>) -> Result<Self, Self::Error> {
        let return_count = c.program.return_count;
        let public_input_count = c.program.public_count() - return_count;

        if public_input_count != return_count {
            return Err(Error::User(format!("Number of return values must match number of public input values for Nova circuits, found `{} != {}`", c.program.return_count, public_input_count)));
        }

        Ok(NovaComputation {
            step_private: None,
            computation: c,
        })
    }
}

type G1<T> = <T as Cycle>::Point;
type G2<T> = <<T as Cycle>::Other as Cycle>::Point;
type C1<'ast, T> = NovaComputation<'ast, T>;
type C2<T> = TrivialTestCircuit<<<T as Cycle>::Point as Group>::Base>;

type PublicParams<'ast, T> = GPublicParams<G1<T>, G2<T>, C1<'ast, T>, C2<T>>;
pub type RecursiveSNARK<'ast, T> = GRecursiveSNARK<G1<T>, G2<T>, C1<'ast, T>, C2<T>>;

#[derive(Debug)]
pub enum Error {
    Internal(NovaError),
    User(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> std::fmt::Result {
        match self {
            Error::Internal(e) => write!(f, "Internal error: {:#?}", e),
            Error::User(s) => write!(f, "{}", s),
        }
    }
}

impl From<NovaError> for Error {
    fn from(e: NovaError) -> Self {
        Self::Internal(e)
    }
}

pub fn generate_public_parameters<
    'ast,
    T: Field
        + BellpersonFieldExtensions<BellpersonField = <<T as Cycle>::Point as Group>::Scalar>
        + Cycle,
>(
    program: &'ast Prog<'ast, T>,
) -> Result<PublicParams<'ast, T>, Error> {
    Ok(GPublicParams::setup(
        NovaComputation::try_from(Computation::without_witness(program))?,
        TrivialTestCircuit::default(),
    ))
}

pub fn verify<T: NovaField>(
    params: &PublicParams<T>,
    proof: &RecursiveSNARKWithStepCount<T>,
    arguments: Vec<T>,
) -> Result<Vec<T>, Error> {
    let z0_primary: Vec<_> = arguments.into_iter().map(|a| a.into_bellperson()).collect();
    let z0_secondary = vec![<<T as Cycle>::Point as Group>::Base::one()];

    proof
        .proof
        .verify(params, proof.steps, z0_primary, z0_secondary)
        .map_err(Error::Internal)
        .map(|(primary, _)| primary.into_iter().map(T::from_bellperson).collect())
}

#[derive(Serialize, Debug, Deserialize)]
pub struct RecursiveSNARKWithStepCount<'ast, T: NovaField> {
    #[serde(bound = "T: NovaField")]
    pub proof: RecursiveSNARK<'ast, T>,
    pub steps: usize,
}

type EE1<T> = nova_snark::provider::ipa_pc::EvaluationEngine<G1<T>>;
type EE2<T> = nova_snark::provider::ipa_pc::EvaluationEngine<G2<T>>;
type S1<T> = nova_snark::spartan::RelaxedR1CSSNARK<G1<T>, EE1<T>>;
type S2<T> = nova_snark::spartan::RelaxedR1CSSNARK<G2<T>, EE2<T>>;

pub type CompressedSNARK<'ast, T> =
    GCompressedSNARK<G1<T>, G2<T>, C1<'ast, T>, C2<T>, S1<T>, S2<T>>;
pub type VerifierKey<'ast, T> = GVerifierKey<G1<T>, G2<T>, C1<'ast, T>, C2<T>, S1<T>, S2<T>>;

pub fn compress<'ast, T: NovaField>(
    public_parameters: &PublicParams<'ast, T>,
    instance: RecursiveSNARKWithStepCount<'ast, T>,
) -> (CompressedSNARK<'ast, T>, VerifierKey<'ast, T>) {
    let (pk, vk) = CompressedSNARK::<'ast, T>::setup(public_parameters).unwrap();

    (
        CompressedSNARK::prove(public_parameters, &pk, &instance.proof).unwrap(),
        vk,
    )
}

pub fn verify_compressed<'ast, T: NovaField>(
    proof: &CompressedSNARK<'ast, T>,
    vk: &VerifierKey<'ast, T>,
    arguments: Vec<T>,
    step_count: usize,
) -> bool {
    let z0_primary: Vec<_> = arguments.into_iter().map(|a| a.into_bellperson()).collect();
    let z0_secondary = vec![<<T as Cycle>::Point as Group>::Base::one()];

    proof
        .verify(vk, step_count, z0_primary, z0_secondary)
        .is_ok()
}

pub fn prove<'ast, T: NovaField>(
    public_parameters: &PublicParams<'ast, T>,
    program: &'ast Prog<'ast, T>,
    arguments: Vec<T>,
    mut proof: Option<RecursiveSNARKWithStepCount<'ast, T>>,
    steps: impl IntoIterator<Item = Vec<T>>,
) -> Result<Option<RecursiveSNARKWithStepCount<'ast, T>>, Error> {
    let c_primary = NovaComputation::try_from(Computation::without_witness(program))?;
    let c_secondary = TrivialTestCircuit::default();
    let z0_primary: Vec<_> = arguments.into_iter().map(|a| a.into_bellperson()).collect();
    let z0_secondary = vec![<<T as Cycle>::Point as Group>::Base::one()];

    for steps_private in steps {
        let mut c_primary = c_primary.clone();
        c_primary.step_private = Some(steps_private);

        let steps = proof.as_ref().map(|proof| proof.steps).unwrap_or_default() + 1;

        proof = Some(RecursiveSNARKWithStepCount {
            proof: RecursiveSNARK::prove_step(
                public_parameters,
                proof.map(|proof| proof.proof),
                c_primary,
                c_secondary.clone(),
                z0_primary.clone(),
                z0_secondary.clone(),
            )?,
            steps,
        });
    }

    Ok(proof)
}

impl<'ast, T: Field + BellpersonFieldExtensions + Cycle> StepCircuit<T::BellpersonField>
    for NovaComputation<'ast, T>
{
    fn arity(&self) -> usize {
        let output_count = self.computation.program.return_count;
        let input_count = self.computation.program.public_count() - output_count;
        assert_eq!(input_count, output_count);
        input_count
    }

    fn synthesize<CS: bellperson::ConstraintSystem<T::BellpersonField>>(
        &self,
        cs: &mut CS,
        input: &[bellperson::gadgets::num::AllocatedNum<T::BellpersonField>],
    ) -> Result<
        Vec<bellperson::gadgets::num::AllocatedNum<T::BellpersonField>>,
        bellperson::SynthesisError,
    > {
        let output_count = self.computation.program.return_count;
        let input_count = self.computation.program.public_count() - output_count;
        assert_eq!(input_count, output_count);

        let mut symbols = BTreeMap::new();

        let mut witness = Witness::default();

        let outputs = self.computation.program.returns();

        // populate the witness if we got some input values
        // this is a bit hacky and in particular generates the witness in all cases if there are no inputs
        if input
            .get(0)
            .map(|n| n.get_value().is_some())
            .unwrap_or(true)
        {
            let interpreter = Interpreter::default();
            let inputs: Vec<_> = input
                .iter()
                .map(|v| T::from_bellperson(v.get_value().unwrap()))
                .chain(self.step_private.clone().into_iter().flatten())
                .collect();

            let program = self.computation.program;
            witness = interpreter
                .execute(
                    &inputs,
                    program.statements.iter(),
                    &program.arguments,
                    &program.solvers,
                )
                .unwrap();
        }

        // allocate the inputs
        for (p, allocated_num) in self.computation.program.arguments.iter().zip(input) {
            symbols.insert(p.id, allocated_num.get_variable());
        }

        // allocate the outputs

        let outputs: Vec<_> = outputs
            .iter()
            .map(|v| {
                assert!(v.id < 0); // this should indeed be an output
                let wire = AllocatedNum::alloc(
                    cs.namespace(|| format!("NOVA_INCREMENTAL_OUTPUT_{}", -v.id - 1)),
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
                wire
            })
            .collect();

        self.computation
            .synthesize_input_to_output(cs, &mut symbols, &mut witness)?;

        Ok(outputs)
    }

    fn output(&self, z: &[T::BellpersonField]) -> Vec<T::BellpersonField> {
        let interpreter = Interpreter::default();
        let inputs: Vec<_> = z
            .iter()
            .map(|v| T::from_bellperson(*v))
            .chain(self.step_private.clone().unwrap())
            .collect();

        let program = self.computation.program;
        let output = interpreter
            .execute(
                &inputs,
                program.statements.iter(),
                &program.arguments,
                &program.solvers,
            )
            .unwrap();

        output
            .return_values()
            .into_iter()
            .map(|v| v.into_bellperson())
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_ast::ir::LinComb;

    mod prove {
        use super::*;
        use zokrates_ast::flat::Parameter;
        use zokrates_ast::ir::Prog;
        use zokrates_field::PallasField;

        fn test<T: NovaField>(
            program: Prog<T>,
            initial_state: Vec<T>,
            step_privates: Vec<Vec<T>>,
            expected_final_state: Vec<T>,
        ) {
            let params = generate_public_parameters(&program).unwrap();
            let proof = prove(
                &params,
                &program,
                initial_state.clone(),
                None,
                step_privates,
            )
            .unwrap()
            .unwrap();
            assert_eq!(
                verify(&params, &proof, initial_state).unwrap(),
                expected_final_state
            );
        }

        #[test]
        fn empty() {
            let program: Prog<PallasField> = Prog::default();
            test(program, vec![], vec![vec![]; 3], vec![]);
        }

        #[test]
        fn identity() {
            let program: Prog<PallasField> = Prog {
                arguments: vec![Parameter::public(Variable::new(0))],
                return_count: 1,
                statements: vec![Statement::constraint(
                    Variable::new(0),
                    Variable::public(0),
                    None,
                )],
                module_map: Default::default(),
                solvers: vec![],
            };

            test(
                program,
                vec![PallasField::from(0)],
                vec![vec![]; 3],
                vec![PallasField::from(0)],
            );
        }

        #[test]
        fn plus_one() {
            let program = Prog {
                arguments: vec![Parameter::public(Variable::new(42))],
                return_count: 1,
                statements: vec![Statement::constraint(
                    LinComb::from(Variable::new(42)) + LinComb::one(),
                    Variable::public(0),
                    None,
                )],
                module_map: Default::default(),
                solvers: vec![],
            };

            test(
                program,
                vec![PallasField::from(3)],
                vec![vec![]; 3],
                vec![PallasField::from(6)],
            );
        }

        #[test]
        fn private_gaps() {
            let program = Prog {
                arguments: vec![
                    Parameter::public(Variable::new(42)),
                    Parameter::public(Variable::new(51)),
                ],
                return_count: 2,
                statements: vec![
                    Statement::constraint(
                        LinComb::from(Variable::new(42)) + LinComb::from(Variable::new(51)),
                        Variable::public(0),
                        None,
                    ),
                    Statement::constraint(
                        LinComb::from(Variable::new(51)) + LinComb::from(Variable::new(42)),
                        Variable::public(1),
                        None,
                    ),
                ],
                module_map: Default::default(),
                solvers: vec![],
            };

            test(
                program,
                vec![PallasField::from(0), PallasField::from(1)],
                vec![vec![]; 3],
                vec![PallasField::from(4), PallasField::from(4)],
            );
        }

        #[test]
        fn fold() {
            // def main(public field acc, field e) -> field {
            //     return acc + e
            // }

            // called with init 2 and round private inputs [1, 2, 3]
            // should return (((2 + 1) + 2) + 3) = 8

            let program = Prog {
                arguments: vec![
                    Parameter::public(Variable::new(0)),
                    Parameter::private(Variable::new(1)),
                ],
                return_count: 1,
                statements: vec![Statement::constraint(
                    LinComb::from(Variable::new(0)) + LinComb::from(Variable::new(1)),
                    Variable::public(0),
                    None,
                )],
                module_map: Default::default(),
                solvers: vec![],
            };

            test(
                program,
                vec![PallasField::from(2)],
                vec![
                    vec![PallasField::from(1)],
                    vec![PallasField::from(2)],
                    vec![PallasField::from(3)],
                ],
                vec![PallasField::from(8)],
            );
        }

        #[test]
        fn complex_fold() {
            // def main(public field[2] acc, field[2] e) -> field[2] {
            //     return [acc[0] + e[0], acc[1] + e[1]]
            // }

            // called with init [2, 3] and round private inputs [[1, 2], [3, 4], [5, 6]]
            // should return [2 + 1 + 3 + 5, 3 + 2 + 4 + 6] = [11, 15]

            let program = Prog {
                arguments: vec![
                    Parameter::public(Variable::new(0)),
                    Parameter::public(Variable::new(1)),
                    Parameter::private(Variable::new(2)),
                    Parameter::private(Variable::new(3)),
                ],
                return_count: 2,
                statements: vec![
                    Statement::constraint(
                        LinComb::from(Variable::new(0)) + LinComb::from(Variable::new(2)),
                        Variable::public(0),
                        None,
                    ),
                    Statement::constraint(
                        LinComb::from(Variable::new(1)) + LinComb::from(Variable::new(3)),
                        Variable::public(1),
                        None,
                    ),
                ],
                module_map: Default::default(),
                solvers: vec![],
            };

            test(
                program,
                vec![PallasField::from(2), PallasField::from(3)],
                vec![
                    vec![PallasField::from(1), PallasField::from(2)],
                    vec![PallasField::from(3), PallasField::from(4)],
                    vec![PallasField::from(5), PallasField::from(6)],
                ],
                vec![PallasField::from(11), PallasField::from(15)],
            );
        }
    }
}
