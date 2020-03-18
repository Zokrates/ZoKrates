use crate::ir::Prog;
use flat_absy::FlatVariable;
use ir::folder::Folder;
use std::collections::HashSet;
use zokrates_field::field::Field;

pub struct UnconstrainedInputDetector {
    pub(self) variables: HashSet<FlatVariable>,
}

impl UnconstrainedInputDetector {
    pub fn new<T: Field>(p: &Prog<T>) -> Self {
        UnconstrainedInputDetector {
            variables: p
                .parameters()
                .iter()
                .filter(|fp| fp.private) // we care only about private parameters
                .map(|fp| fp.id)
                .collect(),
        }
    }
    pub fn detect<T: Field>(p: Prog<T>) -> Prog<T> {
        let mut detector = Self::new(&p);
        let p = detector.fold_module(p);

        // we should probably handle this case instead of asserting at some point
        assert!(
            detector.variables.is_empty(),
            format!(
                "Unconstrained private parameters are not allowed (found {} occasions)",
                detector.variables.len()
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
}
