use crate::absy::{Node, VariableNode};
use std::fmt;

#[derive(Clone, PartialEq)]
pub struct Parameter<'ast> {
    pub id: VariableNode<'ast>,
    pub is_private: bool,
}

impl<'ast> Parameter<'ast> {
    pub fn new(v: VariableNode<'ast>) -> Self {
        Parameter {
            id: v,
            is_private: true,
        }
    }

    pub fn is_private(mut self, is_private: bool) -> Self {
        self.is_private = is_private;
        self
    }
}

pub type ParameterNode<'ast> = Node<Parameter<'ast>>;

impl<'ast> fmt::Display for Parameter<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let visibility = if self.is_private { "private " } else { "" };
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
