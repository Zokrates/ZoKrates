//! Module containing structs and enums to represent imports.
//!
//! @file imports.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.org>
//! @date 2018

use std::fmt;

#[derive(PartialEq, Clone, Serialize, Deserialize)]
pub struct Import {
	source: String,
	alias: Option<String>
}

impl Import {
	pub fn new(source: String) -> Import {
		Import {
			source,
			alias: None
		}
	}

	pub fn new_with_alias(source: String, alias: String) -> Import {
		Import {
			source,
			alias: Some(alias)
		}
	}
}

impl fmt::Display for Import {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match &self.alias {
			&Some(ref a) => write!(f, "import {} as {}", self.source, a),
			&None => write!(f, "import {}", self.source)
		}
	}
}

impl fmt::Debug for Import {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match &self.alias {
			&Some(ref a) => write!(f, "import(source: {}, alias: {})", self.source, a),
			&None => write!(f, "import(source: {})", self.source)
		}
    }
}