use crate::zir::Variable;
use std::fmt;

#[derive(Clone, PartialEq, Eq)]
pub struct Parameter<I> {
    pub id: Variable<I>,
    pub private: bool,
}

impl<I> Parameter<I> {
    #[cfg(test)]
    pub fn private(v: Variable<I>) -> Self {
        Parameter {
            id: v,
            private: true,
        }
    }
}

impl<I: fmt::Display> fmt::Display for Parameter<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let visibility = if self.private { "private " } else { "" };
        write!(f, "{}{} {}", visibility, self.id.get_type(), self.id.id)
    }
}

impl<I: fmt::Debug> fmt::Debug for Parameter<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Parameter(variable: {:?})", self.id)
    }
}
