use crate::zir::types::MemberId;
use serde::{Deserialize, Serialize};
use std::fmt;

use crate::typed::Identifier as CoreIdentifier;

#[derive(Debug, PartialEq, Clone, Hash, Eq, Serialize, Deserialize)]
pub enum Identifier<'ast> {
    #[serde(borrow)]
    Basic(CoreIdentifier<'ast>),
    Select(Box<Identifier<'ast>>, u32),
    Member(Box<Identifier<'ast>>, MemberId),
    Element(Box<Identifier<'ast>>, u32),
}

impl<'ast> Identifier<'ast> {
    pub fn select(self, index: u32) -> Self {
        Self::Select(Box::new(self), index)
    }

    pub fn member(self, member: MemberId) -> Self {
        Self::Member(Box::new(self), member)
    }

    pub fn element(self, index: u32) -> Self {
        Self::Element(Box::new(self), index)
    }
}

impl<'ast> fmt::Display for Identifier<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Identifier::Basic(i) => write!(f, "{}", i),
            Identifier::Select(i, index) => write!(f, "{}~{}", i, index),
            Identifier::Member(i, m) => write!(f, "{}.{}", i, m),
            Identifier::Element(i, index) => write!(f, "{}.{}", i, index),
        }
    }
}

// this is only used in tests but somehow cfg(test) does not work
impl<'ast> From<&'ast str> for Identifier<'ast> {
    fn from(id: &'ast str) -> Identifier<'ast> {
        Identifier::Basic(id.into())
    }
}
