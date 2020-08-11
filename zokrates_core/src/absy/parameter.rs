use crate::absy::{Node, VariableNode};
use std::fmt;

#[derive(Clone, PartialEq)]
pub struct Parameter<'ast, T> {
    pub id: VariableNode<'ast, T>,
    pub private: bool,
}

impl<'ast, T> Parameter<'ast, T> {
    pub fn new(v: VariableNode<'ast, T>, private: bool) -> Self {
        Parameter { id: v, private }
    }

    pub fn public(v: VariableNode<'ast, T>) -> Self {
        Parameter {
            id: v,
            private: false,
        }
    }

    pub fn private(v: VariableNode<'ast, T>) -> Self {
        Parameter {
            id: v,
            private: true,
        }
    }
}

pub type ParameterNode<'ast, T> = Node<Parameter<'ast, T>>;

impl<'ast, T: fmt::Display> fmt::Display for Parameter<'ast, T> {
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

impl<'ast, T: fmt::Debug> fmt::Debug for Parameter<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Parameter(variable: {:?}, private: {:?})",
            self.id, self.private
        )
    }
}
