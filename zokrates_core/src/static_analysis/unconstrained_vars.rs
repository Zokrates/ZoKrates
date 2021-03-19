use crate::flat_absy::FlatVariable;
use crate::ir::folder::Folder;
use crate::ir::Directive;
use crate::ir::Prog;
use std::collections::HashSet;
use zokrates_field::Field;

#[derive(Debug)]
pub struct UnconstrainedVariableDetector {
    pub(self) variables: HashSet<FlatVariable>,
}

impl UnconstrainedVariableDetector {
    fn new<T: Field>(p: &Prog<T>) -> Self {
        UnconstrainedVariableDetector {
            variables: p
                .parameters()
                .iter()
                .filter(|p| p.private)
                .map(|p| p.id)
                .collect(),
        }
    }
    pub fn detect<T: Field>(p: Prog<T>) -> Prog<T> {
        let mut instance = Self::new(&p);
        let p = instance.fold_module(p);

        // we should probably handle this case instead of asserting at some point
        assert!(
            instance.variables.is_empty(),
            "Unconstrained variables are not allowed (found {} occurrence{})",
            instance.variables.len(),
            if instance.variables.len() == 1 {
                ""
            } else {
                "s"
            }
        );
        p
    }
}

impl<T: Field> Folder<T> for UnconstrainedVariableDetector {
    fn fold_argument(&mut self, p: FlatVariable) -> FlatVariable {
        p
    }
    fn fold_variable(&mut self, v: FlatVariable) -> FlatVariable {
        self.variables.remove(&v);
        v
    }
    fn fold_directive(&mut self, d: Directive<T>) -> Directive<T> {
        self.variables.extend(d.outputs.iter());
        d
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::flat_absy::FlatVariable;
    use crate::ir::{Function, LinComb, Prog, QuadComb, Statement};
    use crate::solvers::Solver;
    use zokrates_field::Bn128Field;

    #[test]
    #[should_panic]
    fn should_detect_unconstrained_private_input() {
        // def main(_0) -> (1):
        //     (1 * ~one) * (42 * ~one) == 1 * ~out_0
        //     return ~out_0

        let _0 = FlatVariable::new(0); // unused var

        let one = FlatVariable::one();
        let out_0 = FlatVariable::public(0);

        let main: Function<Bn128Field> = Function {
            id: "main".to_string(),
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

        let p: Prog<Bn128Field> = Prog {
            private: vec![true],
            main,
        };

        UnconstrainedVariableDetector::detect(p);
    }

    #[test]
    fn should_pass_with_constrained_private_input() {
        // def main(_0) -> (1):
        //     (1 * ~one) * (1 * _0) == 1 * ~out_0
        //     return ~out_0

        let _0 = FlatVariable::new(0);
        let out_0 = FlatVariable::public(0);

        let main: Function<Bn128Field> = Function {
            id: "main".to_string(),
            arguments: vec![_0],
            statements: vec![Statement::definition(out_0, LinComb::from(_0))],
            returns: vec![out_0],
        };

        let p: Prog<Bn128Field> = Prog {
            private: vec![true],
            main,
        };

        UnconstrainedVariableDetector::detect(p);
    }

    #[test]
    fn should_pass_with_directive() {
        // def main(_0) -> (1):
        //     # _1, _2 = ConditionEq((-42) * ~one + 1 * _0)
        //     ((-42) * ~one + 1 * _0) * (1 * _2) == 1 * _1
        //     (1 * ~one + (-1) * _1) * ((-42) * ~one + 1 * _0) == 0
        //     (1 * ~one) * (1 * ~one + (-1) * _1) == 1 * ~out_0
        //     return ~out_0

        let _0 = FlatVariable::new(0);
        let _1 = FlatVariable::new(1);
        let _2 = FlatVariable::new(2);

        let out_0 = FlatVariable::public(0);
        let one = FlatVariable::one();

        let main: Function<Bn128Field> = Function {
            id: "main".to_string(),
            arguments: vec![_0],
            statements: vec![
                Statement::Directive(Directive {
                    inputs: vec![(LinComb::summand(-42, one) + LinComb::summand(1, _0)).into()],
                    outputs: vec![_1, _2],
                    solver: Solver::ConditionEq,
                }),
                Statement::constraint(
                    QuadComb::from_linear_combinations(
                        LinComb::summand(-42, one) + LinComb::summand(1, _0),
                        LinComb::summand(1, _2),
                    ),
                    LinComb::summand(1, _1),
                ),
                Statement::constraint(
                    QuadComb::from_linear_combinations(
                        LinComb::summand(1, one) + LinComb::summand(-1, _1),
                        LinComb::summand(-42, one) + LinComb::summand(1, _0),
                    ),
                    LinComb::zero(),
                ),
                Statement::constraint(
                    QuadComb::from_linear_combinations(
                        LinComb::summand(1, one),
                        LinComb::summand(1, one) + LinComb::summand(-1, _1),
                    ),
                    LinComb::summand(1, out_0),
                ),
            ],
            returns: vec![out_0],
        };

        let p: Prog<Bn128Field> = Prog {
            private: vec![true],
            main,
        };

        UnconstrainedVariableDetector::detect(p);
    }
}
