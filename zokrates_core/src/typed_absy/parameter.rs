use crate::typed_absy::GVariable;
use std::fmt;
use typed_absy::types::Constant;
use typed_absy::TryFrom;
use typed_absy::UExpression;

#[derive(Clone, PartialEq, Eq)]
pub struct GParameter<'ast, S> {
    pub id: GVariable<'ast, S>,
    pub private: bool,
}

impl<'ast, S> GParameter<'ast, S> {
    #[cfg(test)]
    pub fn private(v: GVariable<'ast, S>) -> Self {
        Parameter {
            id: v,
            private: true,
        }
    }
}

pub type DeclarationParameter<'ast> = GParameter<'ast, Constant<'ast>>;
pub type ConcreteParameter<'ast> = GParameter<'ast, usize>;
pub type Parameter<'ast, T> = GParameter<'ast, UExpression<'ast, T>>;

impl<'ast, T> TryFrom<Parameter<'ast, T>> for ConcreteParameter<'ast> {
    type Error = ();

    fn try_from(t: Parameter<'ast, T>) -> Result<Self, Self::Error> {
        unimplemented!()
    }
}

impl<'ast, T> From<ConcreteParameter<'ast>> for Parameter<'ast, T> {
    fn from(t: ConcreteParameter<'ast>) -> Self {
        unimplemented!()
    }
}

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
