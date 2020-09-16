use crate::typed_absy::GVariable;
use std::fmt;
use typed_absy::types::Constant;

#[derive(Clone, PartialEq, Eq)]
pub struct GParameter<'ast, S> {
    pub id: GVariable<'ast, S>,
    pub private: bool,
}

impl<'ast, S> GParameter<'ast, S> {
    #[cfg(test)]
    pub fn private(v: GVariable<'ast, S>) -> Self {
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
