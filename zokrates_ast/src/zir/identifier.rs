use crate::zir::types::MemberId;
use serde::{Deserialize, Serialize};
use std::fmt;

use crate::typed::Identifier as CoreIdentifier;

#[derive(Debug, PartialEq, Clone, Hash, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Identifier<'ast> {
    #[serde(borrow)]
    Source(SourceIdentifier<'ast>),
    Internal(usize),
}

#[derive(Debug, PartialEq, Clone, Hash, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum SourceIdentifier<'ast> {
    #[serde(borrow)]
    Basic(CoreIdentifier<'ast>),
    Select(Box<SourceIdentifier<'ast>>, u32),
    Member(Box<SourceIdentifier<'ast>>, MemberId),
    Element(Box<SourceIdentifier<'ast>>, u32),
}

impl<'ast> Identifier<'ast> {
    pub fn internal<T: Into<usize>>(id: T) -> Self {
        Identifier::Internal(id.into())
    }
}

impl<'ast> fmt::Display for Identifier<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Identifier::Source(s) => write!(f, "{}", s),
            Identifier::Internal(i) => write!(f, "i{}", i),
        }
    }
}

impl<'ast> fmt::Display for SourceIdentifier<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            SourceIdentifier::Basic(i) => write!(f, "{}", i),
            SourceIdentifier::Select(box i, index) => write!(f, "{}~{}", i, index),
            SourceIdentifier::Member(box i, m) => write!(f, "{}.{}", i, m),
            SourceIdentifier::Element(box i, index) => write!(f, "{}.{}", i, index),
        }
    }
}

// this is only used in tests but somehow cfg(test) does not work
impl<'ast> From<&'ast str> for Identifier<'ast> {
    fn from(id: &'ast str) -> Identifier<'ast> {
        Identifier::Source(SourceIdentifier::Basic(id.into()))
    }
}
