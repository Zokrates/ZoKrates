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

impl<'ast> fmt::Display for Identifier<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Identifier::Basic(i) => write!(f, "{}", i),
            Identifier::Select(box i, index) => write!(f, "{}~{}", i, index),
            Identifier::Member(box i, m) => write!(f, "{}.{}", i, m),
            Identifier::Element(box i, index) => write!(f, "{}.{}", i, index),
        }
    }
}

// this is only used in tests but somehow cfg(test) does not work
impl<'ast> From<&'ast str> for Identifier<'ast> {
    fn from(id: &'ast str) -> Identifier<'ast> {
        Identifier::Basic(id.into())
    }
}
