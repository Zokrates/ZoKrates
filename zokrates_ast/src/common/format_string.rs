use std::fmt;

use serde::{Deserialize, Serialize};

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Hash, Serialize, Deserialize)]
pub struct FormatString {
    pub parts: Vec<String>,
}

impl fmt::Display for FormatString {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.parts.join("{}"))
    }
}

impl FormatString {
    pub fn len(&self) -> usize {
        self.parts.len() - 1
    }

    pub fn is_empty(&self) -> bool {
        self.parts.len() == 1
    }
}

impl From<&str> for FormatString {
    fn from(s: &str) -> Self {
        let parts = s.split("{}").map(|p| p.to_string());
        FormatString {
            parts: parts.collect(),
        }
    }
}
