use crate::typed::CanonicalConstantIdentifier;
use std::fmt;

pub type SourceIdentifier<'ast> = &'ast str;

#[derive(Debug, PartialEq, Clone, Hash, Eq, PartialOrd, Ord)]
pub enum CoreIdentifier<'ast> {
    Source(&'ast str),
    Call(usize),
    Constant(CanonicalConstantIdentifier<'ast>),
    Condition(usize),
}

impl<'ast> fmt::Display for CoreIdentifier<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CoreIdentifier::Source(s) => write!(f, "{}", s),
            CoreIdentifier::Call(i) => write!(f, "#CALL_RETURN_AT_INDEX_{}", i),
            CoreIdentifier::Constant(c) => write!(f, "{}/{}", c.module.display(), c.id),
            CoreIdentifier::Condition(i) => write!(f, "#CONDITION_{}", i),
        }
    }
}

impl<'ast> From<&'ast str> for CoreIdentifier<'ast> {
    fn from(s: &str) -> CoreIdentifier {
        CoreIdentifier::Source(s)
    }
}

impl<'ast> From<CanonicalConstantIdentifier<'ast>> for CoreIdentifier<'ast> {
    fn from(s: CanonicalConstantIdentifier<'ast>) -> CoreIdentifier<'ast> {
        CoreIdentifier::Constant(s)
    }
}

/// A identifier for a variable
#[derive(Debug, PartialEq, Clone, Hash, Eq, PartialOrd, Ord)]
pub struct Identifier<'ast> {
    /// the id of the variable with its shadowing id
    pub id: ShadowedIdentifier<'ast>,
    /// the version of the variable, used after SSA transformation
    pub version: usize,
}

#[derive(Debug, PartialEq, Clone, Hash, Eq, PartialOrd, Ord)]
pub struct ShadowedIdentifier<'ast> {
    pub id: CoreIdentifier<'ast>,
    pub shadow: usize,
}

impl<'ast> ShadowedIdentifier<'ast> {
    pub fn top_level(id: CoreIdentifier<'ast>) -> Self {
        Self::nth(id, 0)
    }

    pub fn function_level(id: CoreIdentifier<'ast>) -> Self {
        Self::nth(id, 1)
    }

    pub fn nth(id: CoreIdentifier<'ast>, shadow: usize) -> Self {
        Self {
            id,
            shadow
        }
    }
}

impl<'ast> fmt::Display for ShadowedIdentifier<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.shadow == 0 {
            write!(f, "{}", self.id)
        } else {
            write!(f, "{}_{}", self.id, self.shadow)
        }
    }
}

// impl<'ast> TryInto<&'ast str> for Identifier<'ast> {
//     type Error = ();

//     fn try_into(self) -> Result<&'ast str, Self::Error> {
//         match self.id {
//             CoreIdentifier::Source(i) => Ok(i),
//             _ => Err(()),
//         }
//     }
// }

impl<'ast> fmt::Display for Identifier<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.version == 0 {
            write!(f, "{}", self.id)
        } else {
            write!(f, "{}_{}", self.id, self.version)
        }
    }
}

impl<'ast> From<CanonicalConstantIdentifier<'ast>> for Identifier<'ast> {
    fn from(id: CanonicalConstantIdentifier<'ast>) -> Identifier<'ast> {
        Identifier::from(ShadowedIdentifier { id: CoreIdentifier::Constant(id), shadow: 0})
    }
}

impl<'ast> From<&'ast str> for Identifier<'ast> {
    fn from(id: &'ast str) -> Identifier<'ast> {
        Identifier::from(ShadowedIdentifier::top_level(CoreIdentifier::Source(id)))
    }
}

impl<'ast> From<CoreIdentifier<'ast>> for ShadowedIdentifier<'ast> {
    fn from(id: CoreIdentifier<'ast>) -> ShadowedIdentifier<'ast> {
        Self::nth(id, 1)
    }
}

impl<'ast> From<&'ast str> for ShadowedIdentifier<'ast> {
    fn from(id: &'ast str) -> ShadowedIdentifier<'ast> {
            Self::nth(id.into(), 1)
    }
}

impl<'ast> From<ShadowedIdentifier<'ast>> for Identifier<'ast> {
    fn from(id: ShadowedIdentifier<'ast>) -> Identifier<'ast> {
        Identifier { id, version: 0 }
    }
}

impl<'ast> From<CoreIdentifier<'ast>> for Identifier<'ast> {
    fn from(id: CoreIdentifier<'ast>) -> Identifier<'ast> {
        Identifier::from(ShadowedIdentifier::from(id))
    }
}

impl<'ast> Identifier<'ast> {
    pub fn version(mut self, version: usize) -> Self {
        self.version = version;
        self
    }
}
