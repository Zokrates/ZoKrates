use crate::typed_absy::types::Constant;
use crate::typed_absy::GVariable;
use std::fmt;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct GParameter<'ast, S> {
    pub id: GVariable<'ast, S>,
    pub private: bool,
}

#[cfg(test)]
impl<'ast, S> From<GVariable<'ast, S>> for GParameter<'ast, S> {
    fn from(v: GVariable<'ast, S>) -> Self {
        GParameter {
            id: v,
            private: true,
        }
    }
}

pub type DeclarationParameter<'ast> = GParameter<'ast, Constant<'ast>>;

impl<'ast, S: fmt::Display + Clone> fmt::Display for GParameter<'ast, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let visibility = if self.private { "private " } else { "" };
        write!(f, "{}{} {}", visibility, self.id.get_type(), self.id.id)
    }
}

impl<'ast, S: fmt::Debug> fmt::Debug for GParameter<'ast, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Parameter(variable: {:?})", self.id)
    }
}
