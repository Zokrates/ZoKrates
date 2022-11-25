use crate::typed::CanonicalConstantIdentifier;
use std::fmt;

pub trait IdTrait:
    fmt::Display
    + fmt::Debug
    + PartialEq
    + Eq
    + Clone
    + PartialOrd
    + Ord
    + PartialEq<&'static str>
    + for<'a> From<&'a str>
{
}

pub type SourceIdentifier<I> = I;

#[derive(Debug, PartialEq, Clone, Hash, Eq, PartialOrd, Ord)]
pub enum CoreIdentifier<I> {
    Source(ShadowedIdentifier<I>),
    Call(usize),
    Constant(CanonicalConstantIdentifier<I>),
    Condition(usize),
}

impl<I: fmt::Display> fmt::Display for CoreIdentifier<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CoreIdentifier::Source(s) => write!(f, "{}", s),
            CoreIdentifier::Call(i) => write!(f, "#CALL_RETURN_AT_INDEX_{}", i),
            CoreIdentifier::Constant(c) => write!(f, "{}/{}", c.module.display(), c.id),
            CoreIdentifier::Condition(i) => write!(f, "#CONDITION_{}", i),
        }
    }
}

impl<I> From<CanonicalConstantIdentifier<I>> for CoreIdentifier<I> {
    fn from(s: CanonicalConstantIdentifier<I>) -> CoreIdentifier<I> {
        CoreIdentifier::Constant(s)
    }
}

/// A identifier for a variable
#[derive(Debug, PartialEq, Clone, Hash, Eq, PartialOrd, Ord)]
pub struct Identifier<I> {
    /// the id of the variable
    pub id: CoreIdentifier<I>,
    /// the version of the variable, used after SSA transformation
    pub version: usize,
}

#[derive(Debug, PartialEq, Clone, Hash, Eq, PartialOrd, Ord)]
pub struct ShadowedIdentifier<I> {
    pub id: SourceIdentifier<I>,
    pub shadow: usize,
}

impl<I> ShadowedIdentifier<I> {
    pub fn shadow(id: SourceIdentifier<I>, shadow: usize) -> Self {
        Self { id, shadow }
    }
}

impl<I: fmt::Display> fmt::Display for ShadowedIdentifier<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.shadow == 0 {
            write!(f, "{}", self.id)
        } else {
            write!(f, "{}_{}", self.id, self.shadow)
        }
    }
}

impl<I: fmt::Display> fmt::Display for Identifier<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.version == 0 {
            write!(f, "{}", self.id)
        } else {
            write!(f, "{}_{}", self.id, self.version)
        }
    }
}

impl<I> From<CanonicalConstantIdentifier<I>> for Identifier<I> {
    fn from(id: CanonicalConstantIdentifier<I>) -> Identifier<I> {
        Identifier::from(CoreIdentifier::Constant(id))
    }
}

impl<I> From<CoreIdentifier<I>> for Identifier<I> {
    fn from(id: CoreIdentifier<I>) -> Identifier<I> {
        Identifier { id, version: 0 }
    }
}

impl<I> From<ShadowedIdentifier<I>> for CoreIdentifier<I> {
    fn from(id: ShadowedIdentifier<I>) -> CoreIdentifier<I> {
        CoreIdentifier::Source(id)
    }
}

impl<I> Identifier<I> {
    pub fn version(mut self, version: usize) -> Self {
        self.version = version;
        self
    }
}

// these two From implementations are only used in tests but somehow cfg(test) doesn't work
// impl<I> From<& str> for CoreIdentifier<I> {
//     fn from(s: &str) -> CoreIdentifier {
//         CoreIdentifier::Source(ShadowedIdentifier::shadow(s, 0))
//     }
// }

// impl<I> From<I> for Identifier<I> {
//     fn from(id: I) -> Identifier<I> {
//         Identifier::from(CoreIdentifier::from(id))
//     }
// }
