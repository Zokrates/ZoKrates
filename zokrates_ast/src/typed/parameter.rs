use crate::typed::types::DeclarationConstant;
use crate::typed::GVariable;
use std::fmt;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct GParameter<I, S> {
    pub id: GVariable<I, S>,
    pub private: bool,
}

impl<I, S> From<GVariable<I, S>> for GParameter<I, S> {
    fn from(v: GVariable<I, S>) -> Self {
        GParameter {
            id: v,
            private: true,
        }
    }
}

pub type DeclarationParameter<I, T> = GParameter<I, DeclarationConstant<I, T>>;

impl<I: fmt::Display, S: fmt::Display> fmt::Display for GParameter<I, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let visibility = if self.private { "private " } else { "" };
        write!(f, "{}{} {}", visibility, self.id._type, self.id.id)
    }
}

impl<I: fmt::Debug, S: fmt::Debug> fmt::Debug for GParameter<I, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Parameter(variable: {:?})", self.id)
    }
}
