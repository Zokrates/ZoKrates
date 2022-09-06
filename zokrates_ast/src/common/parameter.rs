use super::variable::Variable;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;

#[derive(Serialize, Deserialize, Hash, Eq, PartialEq, Clone, Copy)]
pub struct Parameter {
    pub id: Variable,
    pub private: bool,
}

impl Parameter {
    fn new(id: Variable, private: bool) -> Self {
        Parameter { id, private }
    }

    pub fn public(v: Variable) -> Self {
        Self::new(v, false)
    }

    pub fn private(v: Variable) -> Self {
        Self::new(v, true)
    }
}

impl fmt::Display for Parameter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let visibility = if self.private { "private " } else { "" };
        write!(f, "{}{}", visibility, self.id)
    }
}

impl fmt::Debug for Parameter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Parameter(id: {:?})", self.id)
    }
}

impl Parameter {
    pub fn apply_substitution(self, substitution: &HashMap<Variable, Variable>) -> Parameter {
        Parameter {
            id: *substitution.get(&self.id).unwrap(),
            private: self.private,
        }
    }
}
