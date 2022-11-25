use crate::zir::types::MemberId;
use std::fmt;

use crate::typed::Identifier as CoreIdentifier;

#[derive(Debug, PartialEq, Clone, Hash, Eq)]
pub enum Identifier<I> {
    Source(SourceIdentifier<I>),
}

#[derive(Debug, PartialEq, Clone, Hash, Eq)]
pub enum SourceIdentifier<I> {
    Basic(CoreIdentifier<I>),
    Select(Box<SourceIdentifier<I>>, u32),
    Member(Box<SourceIdentifier<I>>, MemberId),
    Element(Box<SourceIdentifier<I>>, u32),
}

impl<I: fmt::Display> fmt::Display for SourceIdentifier<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            SourceIdentifier::Basic(i) => write!(f, "{}", i),
            SourceIdentifier::Select(box i, index) => write!(f, "{}~{}", i, index),
            SourceIdentifier::Member(box i, m) => write!(f, "{}.{}", i, m),
            SourceIdentifier::Element(box i, index) => write!(f, "{}.{}", i, index),
        }
    }
}

impl<I: fmt::Display> fmt::Display for Identifier<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Identifier::Source(s) => write!(f, "{}", s),
        }
    }
}

// this is only used in tests but somehow cfg(test) does not work
// impl<I> From<I> for Identifier<I> {
//     fn from(id: I) -> Identifier<I> {
//         Identifier::Source(SourceIdentifier::Basic(id.into()))
//     }
// }
