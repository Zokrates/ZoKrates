use crate::absy::types::UnresolvedType;
use crate::absy::{Node, UnresolvedTypeNode};
use std::fmt;

use crate::absy::Identifier;

#[derive(Clone, PartialEq)]
pub struct Variable<'ast> {
    pub id: Identifier<'ast>,
    pub _type: UnresolvedTypeNode<'ast>,
}

pub type VariableNode<'ast> = Node<Variable<'ast>>;

impl<'ast> Variable<'ast> {
    pub fn new<S: Into<&'ast str>>(id: S, t: UnresolvedTypeNode<'ast>) -> Variable<'ast> {
        Variable {
            id: id.into(),
            _type: t,
        }
    }

    pub fn get_type(&self) -> &UnresolvedType<'ast> {
        &self._type.value
    }
}

impl<'ast> fmt::Display for Variable<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self._type, self.id,)
    }
}

impl<'ast> fmt::Debug for Variable<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Variable(type: {:?}, id: {:?})", self._type, self.id,)
    }
}
