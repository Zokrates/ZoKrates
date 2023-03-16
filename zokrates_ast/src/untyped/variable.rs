use super::types::UnresolvedType;
use super::{Node, UnresolvedTypeNode};
use std::fmt;

use super::Identifier;

#[derive(Clone, PartialEq)]
pub struct Variable<'ast> {
    pub is_mutable: bool,
    pub id: Identifier<'ast>,
    pub ty: UnresolvedTypeNode<'ast>,
}

pub type VariableNode<'ast> = Node<Variable<'ast>>;

impl<'ast> Variable<'ast> {
    pub fn new<S: Into<&'ast str>>(
        id: S,
        t: UnresolvedTypeNode<'ast>,
        is_mutable: bool,
    ) -> Variable<'ast> {
        Variable {
            is_mutable,
            id: id.into(),
            ty: t,
        }
    }

    pub fn immutable<S: Into<&'ast str>>(id: S, t: UnresolvedTypeNode<'ast>) -> Self {
        Self::new(id, t, false)
    }

    pub fn mutable<S: Into<&'ast str>>(id: S, t: UnresolvedTypeNode<'ast>) -> Self {
        Self::new(id, t, true)
    }

    pub fn get_type(&self) -> &UnresolvedType<'ast> {
        &self.ty.value
    }
}

impl<'ast> fmt::Display for Variable<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self.ty, self.id,)
    }
}

impl<'ast> fmt::Debug for Variable<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Variable(type: {:?}, id: {:?}, is_mutable: {:?})",
            self.ty, self.id, self.is_mutable
        )
    }
}
