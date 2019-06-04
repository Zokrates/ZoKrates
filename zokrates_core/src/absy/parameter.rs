use crate::absy::{Node, VariableNode};
use std::fmt;

#[derive(Clone, PartialEq)]
pub struct Parameter<'ast> {
    pub id: VariableNode<'ast>,
    pub private: bool,
}

impl<'ast> Parameter<'ast> {
    pub fn new(v: VariableNode<'ast>, private: bool) -> Self {
        Parameter { id: v, private }
    }

    pub fn public(v: VariableNode<'ast>) -> Self {
        Parameter {
            id: v,
            private: false,
        }
    }

    pub fn private(v: VariableNode<'ast>) -> Self {
        Parameter {
            id: v,
            private: true,
        }
    }
}

pub type ParameterNode<'ast> = Node<Parameter<'ast>>;

impl<'ast> fmt::Display for Parameter<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let visibility = if self.private { "private " } else { "" };
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
            self.id, self.private
        )
    }
}
