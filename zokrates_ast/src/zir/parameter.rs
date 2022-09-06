use crate::zir::Variable;
use std::fmt;

#[derive(Clone, PartialEq, Eq)]
pub struct Parameter<'ast> {
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
