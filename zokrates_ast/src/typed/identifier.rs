use crate::typed::CanonicalConstantIdentifier;
use serde::{Deserialize, Serialize};
use std::fmt;

pub type SourceIdentifier<'ast> = std::borrow::Cow<'ast, str>;

#[derive(Debug, PartialEq, Clone, Hash, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum CoreIdentifier<'ast> {
    #[serde(borrow)]
    Source(ShadowedIdentifier<'ast>),
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

impl<'ast> FrameIdentifier<'ast> {
    pub fn in_frame(self, frame: usize) -> FrameIdentifier<'ast> {
        FrameIdentifier { frame, ..self }
    }
}

impl<'ast> Identifier<'ast> {
    pub fn in_frame(self, frame: usize) -> Identifier<'ast> {
        Identifier {
            id: self.id.in_frame(frame),
            ..self
        }
    }
}

impl<'ast> CoreIdentifier<'ast> {
    pub fn in_frame(self, frame: usize) -> FrameIdentifier<'ast> {
        FrameIdentifier { id: self, frame }
    }
}

impl<'ast> From<CanonicalConstantIdentifier<'ast>> for FrameIdentifier<'ast> {
    fn from(s: CanonicalConstantIdentifier<'ast>) -> FrameIdentifier<'ast> {
        FrameIdentifier::from(CoreIdentifier::Constant(s))
    }
}

/// A identifier for a variable in a given call frame
#[derive(Debug, PartialEq, Clone, Hash, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct FrameIdentifier<'ast> {
    /// the id of the variable
    #[serde(borrow)]
    pub id: CoreIdentifier<'ast>,
    /// the frame of the variable
    pub frame: usize,
}

/// A identifier for a variable
#[derive(Debug, PartialEq, Clone, Hash, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Identifier<'ast> {
    /// the id of the variable
    #[serde(borrow)]
    pub id: FrameIdentifier<'ast>,
    /// the version of the variable, used after SSA transformation
    pub version: usize,
}

#[derive(Debug, PartialEq, Clone, Hash, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ShadowedIdentifier<'ast> {
    #[serde(borrow)]
    pub id: SourceIdentifier<'ast>,
    pub shadow: usize,
}

impl<'ast> ShadowedIdentifier<'ast> {
    pub fn shadow(id: SourceIdentifier<'ast>, shadow: usize) -> Self {
        Self { id, shadow }
    }
}

impl<'ast> fmt::Display for ShadowedIdentifier<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.shadow == 0 {
            write!(f, "{}", self.id)
        } else {
            write!(f, "{}_s{}", self.id, self.shadow)
        }
    }
}

impl<'ast> fmt::Display for Identifier<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.version == 0 {
            write!(f, "{}", self.id)
        } else {
            write!(f, "{}_v{}", self.id, self.version)
        }
    }
}

impl<'ast> fmt::Display for FrameIdentifier<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.frame == 0 {
            write!(f, "{}", self.id)
        } else {
            write!(f, "{}_f{}", self.id, self.frame)
        }
    }
}

impl<'ast> From<CanonicalConstantIdentifier<'ast>> for Identifier<'ast> {
    fn from(id: CanonicalConstantIdentifier<'ast>) -> Identifier<'ast> {
        Identifier::from(FrameIdentifier::from(CoreIdentifier::Constant(id)))
    }
}

impl<'ast> From<FrameIdentifier<'ast>> for Identifier<'ast> {
    fn from(id: FrameIdentifier<'ast>) -> Identifier<'ast> {
        Identifier { id, version: 0 }
    }
}

impl<'ast> From<CoreIdentifier<'ast>> for Identifier<'ast> {
    fn from(id: CoreIdentifier<'ast>) -> Identifier<'ast> {
        Identifier {
            id: FrameIdentifier::from(id),
            version: 0,
        }
    }
}

impl<'ast> From<CoreIdentifier<'ast>> for FrameIdentifier<'ast> {
    fn from(id: CoreIdentifier<'ast>) -> FrameIdentifier<'ast> {
        FrameIdentifier { id, frame: 0 }
    }
}

impl<'ast> From<ShadowedIdentifier<'ast>> for CoreIdentifier<'ast> {
    fn from(id: ShadowedIdentifier<'ast>) -> CoreIdentifier<'ast> {
        CoreIdentifier::Source(id)
    }
}

impl<'ast> Identifier<'ast> {
    pub fn version(mut self, version: usize) -> Self {
        self.version = version;
        self
    }
}

// these two From implementations are only used in tests but somehow cfg(test) doesn't work
impl<'ast> From<&'ast str> for CoreIdentifier<'ast> {
    fn from(s: &str) -> CoreIdentifier {
        CoreIdentifier::Source(ShadowedIdentifier::shadow(std::borrow::Cow::Borrowed(s), 0))
    }
}

impl<'ast> From<&'ast str> for Identifier<'ast> {
    fn from(id: &'ast str) -> Identifier<'ast> {
        Identifier::from(FrameIdentifier::from(CoreIdentifier::from(id)))
    }
}
