use crate::absy::types::UnresolvedType;
use crate::absy::{Node, UnresolvedTypeNode};
use std::fmt;

use crate::absy::Identifier;

#[derive(Clone, PartialEq)]
pub struct Variable<'ast, T> {
    pub id: Identifier<'ast>,
    pub _type: UnresolvedTypeNode<'ast, T>,
}

pub type VariableNode<'ast, T> = Node<Variable<'ast, T>>;

impl<'ast, T> Variable<'ast, T> {
    pub fn new<S: Into<&'ast str>>(id: S, t: UnresolvedTypeNode<'ast, T>) -> Variable<'ast, T> {
        Variable {
            id: id.into(),
            _type: t,
        }
    }

    pub fn get_type(&self) -> &UnresolvedType<'ast, T> {
        &self._type.value
    }
}

impl<'ast, T: fmt::Display> fmt::Display for Variable<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self._type, self.id,)
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for Variable<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Variable(type: {:?}, id: {:?})", self._type, self.id,)
    }
}
