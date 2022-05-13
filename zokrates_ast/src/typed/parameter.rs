use crate::typed::types::DeclarationConstant;
use crate::typed::GVariable;
use std::fmt;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct GParameter<'ast, S> {
    pub id: GVariable<'ast, S>,
    pub private: bool,
}

impl<'ast, S> From<GVariable<'ast, S>> for GParameter<'ast, S> {
    fn from(v: GVariable<'ast, S>) -> Self {
        GParameter {
            id: v,
            private: true,
        }
    }
}

pub type DeclarationParameter<'ast, T> = GParameter<'ast, DeclarationConstant<'ast, T>>;

impl<'ast, S: fmt::Display> fmt::Display for GParameter<'ast, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let visibility = if self.private { "private " } else { "" };
        write!(f, "{}{} {}", visibility, self.id._type, self.id.id)
    }
}

impl<'ast, S: fmt::Debug> fmt::Debug for GParameter<'ast, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Parameter(variable: {:?})", self.id)
    }
}
