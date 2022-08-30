use crate::zir::types::MemberId;
use std::fmt;

use crate::typed::Identifier as CoreIdentifier;

#[derive(Debug, PartialEq, Clone, Hash, Eq)]
pub enum Identifier<'ast> {
    Source(SourceIdentifier<'ast>),
}

#[derive(Debug, PartialEq, Clone, Hash, Eq)]
pub enum SourceIdentifier<'ast> {
    Basic(CoreIdentifier<'ast>),
    Select(Box<SourceIdentifier<'ast>>, u32),
    Member(Box<SourceIdentifier<'ast>>, MemberId),
    Element(Box<SourceIdentifier<'ast>>, u32),
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

impl<'ast> fmt::Display for Identifier<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Identifier::Source(s) => write!(f, "{}", s),
        }
    }
}

// this is only used in tests but somehow cfg(test) does not work
impl<'ast> From<&'ast str> for Identifier<'ast> {
    fn from(id: &'ast str) -> Identifier<'ast> {
        Identifier::Source(SourceIdentifier::Basic(id.into()))
    }
}
