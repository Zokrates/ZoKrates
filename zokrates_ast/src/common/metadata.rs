use crate::untyped::Position;
use serde::{Deserialize, Serialize};
use std::fmt;

#[derive(Clone, Debug, PartialEq, Hash, Eq, Default, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SourceMetadata {
    pub file: String,
    pub position: Position,
    pub message: Option<String>,
}

impl SourceMetadata {
    pub fn new(file: String, position: Position) -> Self {
        Self {
            file,
            position,
            message: None,
        }
    }
    pub fn message(mut self, message: Option<String>) -> Self {
        self.message = message;
        self
    }
}

impl fmt::Display for SourceMetadata {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.file, self.position)?;
        match &self.message {
            Some(m) => write!(f, ": \"{}\"", m),
            None => write!(f, ""),
        }
    }
}
