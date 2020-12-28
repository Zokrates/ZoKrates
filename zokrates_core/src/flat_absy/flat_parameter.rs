use crate::flat_absy::flat_variable::FlatVariable;
use std::collections::HashMap;
use std::fmt;

#[derive(Clone, PartialEq)]
pub struct FlatParameter {
    pub id: FlatVariable,
    pub private: bool,
}

impl FlatParameter {
    fn new(id: FlatVariable, private: bool) -> Self {
        FlatParameter { id, private }
    }

    pub fn public(v: FlatVariable) -> Self {
        Self::new(v, false)
    }

    pub fn private(v: FlatVariable) -> Self {
        Self::new(v, true)
    }
}

impl fmt::Display for FlatParameter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let visibility = if self.private { "private " } else { "" };
        write!(f, "{}{}", visibility, self.id)
    }
}

impl fmt::Debug for FlatParameter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "FlatParameter(id: {:?})", self.id)
    }
}

impl FlatParameter {
    pub fn apply_substitution(
        self,
        substitution: &HashMap<FlatVariable, FlatVariable>,
    ) -> FlatParameter {
        FlatParameter {
            id: *substitution.get(&self.id).unwrap(),
            private: self.private,
        }
    }
}
