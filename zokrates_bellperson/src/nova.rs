use std::collections::BTreeMap;

use crate::Computation;
use bellperson::gadgets::num::AllocatedNum;
use bellperson::SynthesisError;
use ff::Field as FFField;
use nova_snark::errors::NovaError;
pub use nova_snark::traits::circuit::StepCircuit;
pub use nova_snark::traits::circuit::TrivialTestCircuit;
use nova_snark::traits::Group;
pub use nova_snark::PublicParams as GPublicParams;
pub use nova_snark::RecursiveSNARK as GRecursiveSNARK;
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
    computation: Computation<'ast, T, Vec<Statement<'ast, T>>>,
}

impl<'ast, T> TryFrom<Computation<'ast, T, Vec<Statement<'ast, T>>>> for NovaComputation<'ast, T> {
    type Error = Error;
    fn try_from(c: Computation<'ast, T, Vec<Statement<'ast, T>>>) -> Result<Self, Self::Error> {
        let return_count = c.program.return_count;
        let public_input_count = c.program.public_count() - return_count;

        if public_input_count != return_count {
            return Err(Error::User(format!("Number of return values must match number of public input values for Nova circuits, found `{} != {}`", c.program.return_count, c.program.arguments.len())));
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
type RecursiveSNARK<'ast, T> = GRecursiveSNARK<G1<T>, G2<T>, C1<'ast, T>, C2<T>>;

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
    T: Field
        + BellpersonFieldExtensions<BellpersonField = <<T as Cycle>::Point as Group>::Scalar>
        + Cycle,
>(
    program: Prog<T>,
) -> Result<PublicParams<T>, Error> {
    Ok(GPublicParams::setup(
        NovaComputation::try_from(Computation::without_witness(program))?,
        TrivialTestCircuit::default(),
    ))
}

pub fn verify<T: NovaField>(
    params: &PublicParams<T>,
    proof: RecursiveSNARK<T>,
    steps_count: usize,
    arguments: Vec<T>,
) -> Result<(), Error> {
    let z0_primary: Vec<_> = arguments.into_iter().map(|a| a.into_bellperson()).collect();
    let z0_secondary = vec![<<T as Cycle>::Point as Group>::Base::one()];

    dbg!(proof
        .verify(params, steps_count, z0_primary, z0_secondary)
        .map(|_| ())
        .map_err(Error::Internal))
}

pub fn prove<'ast, T: NovaField>(
    public_parameters: &PublicParams<'ast, T>,
    program: Prog<'ast, T>,
    arguments: Vec<T>,
    steps: Vec<Vec<T>>,
) -> Result<Option<RecursiveSNARK<'ast, T>>, Error> {
    let private_input_count = program.private_input_count();

    assert!(steps.iter().all(|v| v.len() == private_input_count));

    let steps_count = steps.len();

    if steps_count == 0 {
        return Ok(None);
    }

    let c_primary = NovaComputation::try_from(Computation::without_witness(program))?;
    let c_secondary = TrivialTestCircuit::default();
    let z0_primary: Vec<_> = arguments.into_iter().map(|a| a.into_bellperson()).collect();

    let z0_secondary = vec![<<T as Cycle>::Point as Group>::Base::one()];

    let mut proof = None;

    for steps_private in steps {
        let mut c_primary = c_primary.clone();
        c_primary.step_private = Some(steps_private);

        proof = Some(RecursiveSNARK::prove_step(
            public_parameters,
            proof,
            c_primary.clone(),
            c_secondary.clone(),
            z0_primary.clone(),
            z0_secondary.clone(),
        )?);
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
                .chain(self.step_private.clone().unwrap())
                .collect();
            witness = interpreter
                .execute(self.computation.program.clone(), &inputs)
                .unwrap();
        }

        // allocate the inputs
        for (p, allocated_num) in self.computation.program.arguments.iter().zip(input) {
            symbols.insert(p.id, allocated_num.get_variable());
        }

        // allocate the outputs

        let outputs: Vec<_> = self
            .computation
            .program
            .returns()
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
            .clone()
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
        let output = interpreter
            .execute(self.computation.program.clone(), &inputs)
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

        fn test<T: NovaField>(program: Prog<T>, arguments: Vec<T>, step_privates: Vec<Vec<T>>) {
            let steps_count = step_privates.len();
            let params = generate_public_parameters(program.clone()).unwrap();
            let proof = prove(&params, program.clone(), arguments.clone(), step_privates).unwrap();
            assert!(verify(&params, proof.unwrap(), steps_count, arguments).is_ok());
        }

        #[test]
        fn empty() {
            let program: Prog<PallasField> = Prog::default();
            test(program, vec![], vec![vec![]; 3]);
        }

        #[test]
        fn identity() {
            let program: Prog<PallasField> = Prog {
                arguments: vec![Parameter::public(Variable::new(0))],
                return_count: 1,
                statements: vec![Statement::constraint(Variable::new(0), Variable::public(0))],
            };

            test(program, vec![PallasField::from(0)], vec![vec![]; 3]);
        }

        #[test]
        fn plus_one() {
            let program = Prog {
                arguments: vec![Parameter::public(Variable::new(42))],
                return_count: 1,
                statements: vec![Statement::constraint(
                    LinComb::from(Variable::new(42)) + LinComb::one(),
                    Variable::public(0),
                )],
            };

            test(program, vec![PallasField::from(3)], vec![vec![]; 3]);
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
                    ),
                    Statement::constraint(
                        LinComb::from(Variable::new(51)) + LinComb::from(Variable::new(42)),
                        Variable::public(1),
                    ),
                ],
            };

            test(
                program,
                vec![PallasField::from(0), PallasField::from(1)],
                vec![vec![]; 3],
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
                )],
            };

            test(
                program,
                vec![PallasField::from(2)],
                vec![
                    vec![PallasField::from(1)],
                    vec![PallasField::from(2)],
                    vec![PallasField::from(3)],
                ],
            );
        }
    }
}
