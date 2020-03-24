use crate::ir::Prog;
use flat_absy::FlatVariable;
use ir::folder::{fold_directive, Folder};
use ir::Directive;
use std::collections::HashSet;
use zokrates_field::field::Field;

#[derive(Debug)]
pub struct UnconstrainedInputDetector {
    pub(self) variables: HashSet<FlatVariable>,
}

impl UnconstrainedInputDetector {
    pub fn new<T: Field>(p: &Prog<T>) -> Self {
        UnconstrainedInputDetector {
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
            format!(
                "Unconstrained private parameters are not allowed (found {} occasions)",
                instance.variables.len()
            )
        );
        p
    }
}

impl<T: Field> Folder<T> for UnconstrainedInputDetector {
    fn fold_argument(&mut self, p: FlatVariable) -> FlatVariable {
        p
    }
    fn fold_variable(&mut self, v: FlatVariable) -> FlatVariable {
        self.variables.remove(&v);
        v
    }
    fn fold_directive(&mut self, d: Directive<T>) -> Directive<T> {
        self.variables.extend(d.outputs.iter());
        fold_directive(self, d)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use flat_absy::FlatVariable;
    use ir::{Function, LinComb, Prog, QuadComb, Statement};
    use num::Zero;
    use solvers::Solver;
    use zokrates_field::field::FieldPrime;

    #[test]
    #[should_panic]
    fn should_detect_unconstrained_private_input() {
        // def main(private x) -> (1):
        //   return 42

        let x = FlatVariable::new(0);

        let main: Function<FieldPrime> = Function {
            id: "main".to_string(),
            arguments: vec![x],
            statements: vec![Statement::constraint(
                QuadComb::from_linear_combinations(
                    LinComb::summand(1, FlatVariable::one()),
                    LinComb::summand(42, FlatVariable::one()),
                ),
                LinComb::summand(1, FlatVariable::public(0)),
            )],
            returns: vec![FlatVariable::public(0)],
        };

        let p: Prog<FieldPrime> = Prog {
            private: vec![true],
            main,
        };

        UnconstrainedInputDetector::detect(p);
    }

    #[test]
    fn should_pass_with_private_input() {
        // def main(private x) -> (1):
        //   y = x
        //   return y

        let x = FlatVariable::new(0);
        let y = FlatVariable::new(1);

        let main: Function<FieldPrime> = Function {
            id: "main".to_string(),
            arguments: vec![x],
            statements: vec![Statement::definition(y, LinComb::from(x))],
            returns: vec![y],
        };

        let p: Prog<FieldPrime> = Prog {
            private: vec![true],
            main,
        };

        UnconstrainedInputDetector::detect(p);
    }

    #[test]
    fn should_pass_with_directive() {
        // def main(private x) -> (1):
        //   return if x == 42 then 1 else 0 fi

        let x = FlatVariable::new(0);
        let _1 = FlatVariable::new(1);
        let _2 = FlatVariable::new(2);
        let out_0 = FlatVariable::public(0);
        let one = FlatVariable::one();

        let main: Function<FieldPrime> = Function {
            id: "main".to_string(),
            arguments: vec![x],
            statements: vec![
                Statement::Directive(Directive {
                    inputs: vec![LinComb::summand(-42, one) + LinComb::summand(1, x)],
                    outputs: vec![_1, _2],
                    solver: Solver::ConditionEq,
                }),
                Statement::constraint(
                    QuadComb::from_linear_combinations(
                        LinComb::summand(-42, one) + LinComb::summand(1, x),
                        LinComb::summand(1, _2),
                    ),
                    LinComb::summand(1, _1),
                ),
                Statement::constraint(
                    QuadComb::from_linear_combinations(
                        LinComb::summand(1, one) + LinComb::summand(-1, _1),
                        LinComb::summand(-42, one) + LinComb::summand(1, x),
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

        let p: Prog<FieldPrime> = Prog {
            private: vec![true],
            main,
        };

        UnconstrainedInputDetector::detect(p);
    }
}
