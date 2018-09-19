//! Module containing structs and enums to represent imports.
//!
//! @file imports.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use std::fmt;
use absy::*;
use flat_absy::*;
use field::Field;
use std::io;

#[derive(PartialEq, Debug)]
pub struct Error {
	message: String
}

impl Error {
	pub fn new<T: Into<String>>(message: T) -> Error {
		Error {
			message: message.into()
		}
	}
}

impl fmt::Display for Error {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{}", self.message)
	}
}

impl From<io::Error> for Error {
	fn from(error: io::Error) -> Self {
		Error {
			message: format!("I/O Error: {:?}", error)
		}
	}
}

#[derive(PartialEq, Clone, Serialize, Deserialize)]
pub struct Import {
	source: String,
	alias: Option<String>,
}

impl Import {
	pub fn new(source: String) -> Import {
		Import {
			source: source,
			alias: None,
		}
	}

	pub fn get_alias(&self) -> &Option<String> {
		&self.alias
	}

	pub fn new_with_alias(source: String, alias: &String) -> Import {
		Import {
			source: source,
			alias: Some(alias.clone()),
		}
	}

	pub fn get_source(&self) -> &String {
		&self.source
	}
}

impl fmt::Display for Import {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self.alias {
			Some(ref alias) => {
				write!(f, "import {} as {}", self.source, alias)
			},
			None => {
				write!(f, "import {}", self.source)
			}
		}
	}
}

impl fmt::Debug for Import {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    	match self.alias {
			Some(ref alias) => {
				write!(f, "import(source: {}, alias: {})", self.source, alias)
			},
			None => {
				write!(f, "import(source: {})", self.source)
			}
	    }
	}
}

pub struct Importer {

}

impl Importer {
	pub fn new() -> Importer {
		Importer {

		}
	}

	pub	fn apply_imports<T: Field>(&self, origins: Vec<(FlatProg<T>, String)>, destination: Prog<T>) -> Prog<T> {
		let imported_mains = origins.iter().map(|origin| {
			match origin {
				&(ref program, ref alias) => {
					match program.functions.iter().find(|fun| fun.id == "main") {
			        	Some(fun) => {
			        		let mut f = fun.clone();
			        		f.id = alias.to_string();
			        		f
			        	},
			        	None => panic!("no main")
			        }
				}
			}
		}).collect();

		Prog {
			imports: vec![],
			functions: destination.clone().functions,
			imported_functions: imported_mains
		}
	}
}

#[cfg(test)]
mod tests {

	use super::*;

	#[test]
	fn create_with_no_alias() {
		assert_eq!(Import::new("./foo/bar/baz.code".to_string()), Import {
			source: String::from("./foo/bar/baz.code"),
			alias: None,
		});
	}

	#[test]
	fn create_with_alias() {
		assert_eq!(Import::new_with_alias("./foo/bar/baz.code".to_string(), &"myalias".to_string()), Import {
			source: String::from("./foo/bar/baz.code"),
			alias: Some("myalias".to_string()),
		});
	}
}