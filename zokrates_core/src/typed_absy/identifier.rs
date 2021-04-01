use std::convert::TryInto;
use std::fmt;

#[derive(Debug, PartialEq, Clone, Hash, Eq)]
pub enum CoreIdentifier<'ast> {
    Source(&'ast str),
    Internal(&'static str, usize),
    Call(usize),
}

impl<'ast> fmt::Display for CoreIdentifier<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CoreIdentifier::Source(s) => write!(f, "{}", s),
            CoreIdentifier::Internal(s, i) => write!(f, "#INTERNAL#_{}_{}", s, i),
            CoreIdentifier::Call(i) => write!(f, "#CALL_RETURN_AT_INDEX_{}", i),
        }
    }
}

impl<'ast> From<&'ast str> for CoreIdentifier<'ast> {
    fn from(s: &str) -> CoreIdentifier {
        CoreIdentifier::Source(s)
    }
}

/// A identifier for a variable
#[derive(Debug, PartialEq, Clone, Hash, Eq)]
pub struct Identifier<'ast> {
    /// the id of the variable
    pub id: CoreIdentifier<'ast>,
    /// the version of the variable, used after SSA transformation
    pub version: usize,
}

impl<'ast> TryInto<&'ast str> for Identifier<'ast> {
    type Error = ();

    fn try_into(self) -> Result<&'ast str, Self::Error> {
        match self.id {
            CoreIdentifier::Source(i) => Ok(i),
            _ => Err(()),
        }
    }
}

impl<'ast> fmt::Display for Identifier<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.version == 0 {
            write!(f, "{}", self.id)
        } else {
            write!(f, "{}_{}", self.id, self.version)
        }
    }
}

impl<'ast> From<&'ast str> for Identifier<'ast> {
    fn from(id: &'ast str) -> Identifier<'ast> {
        Identifier::from(CoreIdentifier::Source(id))
    }
}

impl<'ast> From<CoreIdentifier<'ast>> for Identifier<'ast> {
    fn from(id: CoreIdentifier<'ast>) -> Identifier<'ast> {
        Identifier { id, version: 0 }
    }
}

impl<'ast> Identifier<'ast> {
    pub fn version(mut self, version: usize) -> Self {
        self.version = version;
        self
    }
}
