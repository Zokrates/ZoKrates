use crate::absy::Node;
use std::fmt;
use types::Type;

use crate::absy::Identifier;

#[derive(Clone, PartialEq, Hash, Eq)]
pub struct Variable<'ast> {
    pub id: Identifier<'ast>,
    pub _type: Type,
}

pub type VariableNode<'ast> = Node<Variable<'ast>>;

impl<'ast> Variable<'ast> {
    pub fn new<S: Into<&'ast str>>(id: S, t: Type) -> Variable<'ast> {
        Variable {
            id: id.into(),
            _type: t,
        }
    }

    pub fn field_element<S: Into<&'ast str>>(id: S) -> Variable<'ast> {
        Variable {
            id: id.into(),
            _type: Type::FieldElement,
        }
    }

    pub fn boolean<S: Into<&'ast str>>(id: S) -> Variable<'ast> {
        Variable {
            id: id.into(),
            _type: Type::Boolean,
        }
    }

    pub fn field_array<S: Into<&'ast str>>(id: S, size: usize) -> Variable<'ast> {
        Variable {
            id: id.into(),
            _type: Type::FieldElementArray(size),
        }
    }

    pub fn get_type(&self) -> Type {
        self._type.clone()
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
