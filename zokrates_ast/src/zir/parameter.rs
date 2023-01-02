use crate::zir::Variable;
use serde::{Deserialize, Serialize};
use std::fmt;

#[derive(Clone, PartialEq, Hash, Eq, Serialize, Deserialize)]
pub struct Parameter<'ast> {
    #[serde(borrow)]
    pub id: Variable<'ast>,
    pub private: bool,
}

impl<'ast> Parameter<'ast> {
    #[cfg(test)]
    pub fn private(v: Variable<'ast>) -> Self {
        Parameter {
            id: v,
            private: true,
        }
    }
}

impl<'ast> fmt::Display for Parameter<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let visibility = if self.private { "private " } else { "" };
        write!(f, "{}{} {}", visibility, self.id.get_type(), self.id.id)
    }
}

impl<'ast> fmt::Debug for Parameter<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Parameter(variable: {:?})", self.id)
    }
}
