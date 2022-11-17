use super::{Node, VariableNode};
use std::fmt;

#[derive(Clone, PartialEq)]
pub struct Parameter<'ast> {
    pub id: VariableNode<'ast>,
    pub is_private: Option<bool>,
}

impl<'ast> Parameter<'ast> {
    pub fn new(v: VariableNode<'ast>, is_private: Option<bool>) -> Self {
        Parameter { id: v, is_private }
    }

    pub fn private(v: VariableNode<'ast>) -> Self {
        Self::new(v, Some(true))
    }

    pub fn public(v: VariableNode<'ast>) -> Self {
        Self::new(v, Some(false))
    }
}

pub type ParameterNode<'ast> = Node<Parameter<'ast>>;

impl<'ast> fmt::Display for Parameter<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let visibility = if let Some(true) = self.is_private {
            "private "
        } else {
            ""
        };

        write!(
            f,
            "{}{} {}",
            visibility,
            self.id.value.get_type(),
            self.id.value.id
        )
    }
}

impl<'ast> fmt::Debug for Parameter<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Parameter(variable: {:?}, private: {:?})",
            self.id, self.is_private
        )
    }
}
