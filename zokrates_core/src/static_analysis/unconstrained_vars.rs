use crate::flat_absy::{FlatParameter, FlatVariable};
use crate::ir::visitor::Visitor;
use crate::ir::Directive;
use crate::ir::{Prog, Statement};
use std::collections::HashSet;
use std::fmt;
use zokrates_field::Field;

#[derive(Debug, Default)]
pub struct UnconstrainedVariableDetector {
    pub(crate) variables: HashSet<FlatVariable>,
}

pub struct UnconstrainedVariableDetectorIterator<T, I: IntoIterator<Item = Statement<T>>> {
    pub statements: I,
    pub detector: Option<UnconstrainedVariableDetector>,
}

impl<T: Field, I: Iterator<Item = Statement<T>>> Iterator
    for UnconstrainedVariableDetectorIterator<T, I>
{
    type Item = Statement<T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.statements
            .next()
            .map(|v| {
                self.detector.as_mut().unwrap().visit_statement(&v);
                v
            })
            .or_else(|| {
                let d = std::mem::take(&mut self.detector)?;
                if d.variables.is_empty() {
                    None
                } else {
                    Some(Statement::UnconstrainedVariables)
                }
            })
    }
}

#[derive(Debug, PartialEq)]
pub struct Error(usize);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Found unconstrained variables during IR analysis (found {} occurrence{}). If this is intentional, use the `--allow-unconstrained-variables` flag.",
            self.0,
            if self.0 == 1 { "" } else { "s" }
        )
    }
}

impl UnconstrainedVariableDetector {
    pub fn detect<T: Field>(p: &Prog<T>) -> Result<(), Error> {
        let mut instance = Self::default();
        instance.visit_module(p);

        if instance.variables.is_empty() {
            Ok(())
        } else {
            Err(Error(instance.variables.len()))
        }
    }
}

impl<T: Field> Visitor<T> for UnconstrainedVariableDetector {
    fn visit_argument(&mut self, p: &FlatParameter) {
        if p.private {
            self.variables.insert(p.id);
        }
    }
    fn visit_variable(&mut self, v: &FlatVariable) {
        self.variables.remove(v);
    }
    fn visit_directive(&mut self, d: &Directive<T>) {
        self.variables.extend(d.outputs.iter());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::flat_absy::FlatVariable;
    use crate::ir::{LinComb, Prog, QuadComb, Statement};
    use crate::solvers::Solver;
    use zokrates_field::Bn128Field;

    #[test]
    fn unconstrained_private_input() {
        // def main(_0) -> (1):
        //     (1 * ~one) * (42 * ~one) == 1 * ~out_0
        //     return ~out_0

        let _0 = FlatParameter::private(FlatVariable::new(0)); // unused private parameter

        let one = FlatVariable::one();
        let out_0 = FlatVariable::public(0);

        let p: Prog<Bn128Field> = Prog {
            arguments: vec![_0],
            statements: vec![Statement::constraint(
                QuadComb::from_linear_combinations(
                    LinComb::summand(1, one),
                    LinComb::summand(42, one),
                ),
                LinComb::summand(1, out_0),
            )],
            returns: vec![out_0],
        };

        let result = UnconstrainedVariableDetector::detect(&p);
        assert_eq!(
            result.expect_err("expected an error").to_string(),
            "Found unconstrained variables during IR analysis (found 1 occurrence). If this is intentional, use the `--allow-unconstrained-variables` flag."
        );
    }

    #[test]
    fn constrained_private_input() {
        // def main(_0) -> (1):
        //     (1 * ~one) * (1 * _0) == 1 * ~out_0
        //     return ~out_0

        let _0 = FlatParameter::private(FlatVariable::new(0));
        let out_0 = FlatVariable::public(0);

        let p: Prog<Bn128Field> = Prog {
            arguments: vec![_0],
            statements: vec![Statement::definition(out_0, LinComb::from(_0.id))],
            returns: vec![out_0],
        };

        let result = UnconstrainedVariableDetector::detect(&p);
        assert_eq!(result, Ok(()));
    }

    #[test]
    fn constrained_directive() {
        // def main(_0) -> (1):
        //     # _1, _2 = ConditionEq((-42) * ~one + 1 * _0)
        //     ((-42) * ~one + 1 * _0) * (1 * _2) == 1 * _1
        //     (1 * ~one + (-1) * _1) * ((-42) * ~one + 1 * _0) == 0
        //     (1 * ~one) * (1 * ~one + (-1) * _1) == 1 * ~out_0
        //     return ~out_0

        let v_0 = FlatParameter::private(FlatVariable::new(0));
        let v_1 = FlatVariable::new(1);
        let v_2 = FlatVariable::new(2);

        let out_0 = FlatVariable::public(0);
        let one = FlatVariable::one();

        let p: Prog<Bn128Field> = Prog {
            arguments: vec![v_0],
            statements: vec![
                Statement::Directive(Directive {
                    inputs: vec![(LinComb::summand(-42, one) + LinComb::summand(1, v_0.id)).into()],
                    outputs: vec![v_1, v_2],
                    solver: Solver::ConditionEq,
                }),
                Statement::constraint(
                    QuadComb::from_linear_combinations(
                        LinComb::summand(-42, one) + LinComb::summand(1, v_0.id),
                        LinComb::summand(1, v_2),
                    ),
                    LinComb::summand(1, v_1),
                ),
                Statement::constraint(
                    QuadComb::from_linear_combinations(
                        LinComb::summand(1, one) + LinComb::summand(-1, v_1),
                        LinComb::summand(-42, one) + LinComb::summand(1, v_0.id),
                    ),
                    LinComb::zero(),
                ),
                Statement::constraint(
                    QuadComb::from_linear_combinations(
                        LinComb::summand(1, one),
                        LinComb::summand(1, one) + LinComb::summand(-1, v_1),
                    ),
                    LinComb::summand(1, out_0),
                ),
            ],
            returns: vec![out_0],
        };

        let result = UnconstrainedVariableDetector::detect(&p);
        assert_eq!(result, Ok(()));
    }
}
