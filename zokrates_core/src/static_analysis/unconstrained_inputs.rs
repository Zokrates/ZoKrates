use crate::ir::Prog;
use flat_absy::{FlatParameter, FlatVariable};
use ir::folder::Folder;
use std::collections::HashSet;
use zokrates_field::field::Field;

#[derive(Debug)]
pub struct UnconstrainedInputDetector {
    parameters: Vec<FlatParameter>,
    pub(self) variables: HashSet<FlatVariable>,
}

impl UnconstrainedInputDetector {
    pub fn new<T: Field>(p: &Prog<T>) -> Self {
        UnconstrainedInputDetector {
            parameters: p.parameters(),
            variables: HashSet::new(),
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
        match self.parameters.get(p.id()) {
            Some(param) => {
                if param.private {
                    self.variables.insert(p);
                }
            }
            _ => {}
        }
        p
    }
    fn fold_variable(&mut self, v: FlatVariable) -> FlatVariable {
        self.variables.remove(&v);
        v
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use flat_absy::FlatVariable;
    use ir::{Function, LinComb, Prog, QuadComb, Statement};
    use zokrates_field::field::FieldPrime;

    #[test]
    #[should_panic]
    fn should_detect_unconstrained_inputs() {
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
    fn should_pass_unconstrained_inputs_check() {
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
}
