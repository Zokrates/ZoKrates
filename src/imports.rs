//! Module containing structs and enums to represent imports.
//!
//! @file imports.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use std::fmt;
use absy::*;
use field::Field;
use std::path::PathBuf;

#[derive(PartialEq, Debug)]
pub struct Error {
	message: String
}

impl fmt::Display for Error {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{}", self.message)
	}
}

#[derive(PartialEq, Clone, Serialize, Deserialize)]
pub struct Import {
	source: PathBuf,
	alias: String,
	base: PathBuf
}

impl Import {
	pub fn new(source: String, base: &PathBuf) -> Import {
		Import {
			source: PathBuf::from(source.clone()),
			alias: PathBuf::from(source).file_stem().unwrap().to_os_string().to_string_lossy().to_string(),
			base: base.clone()
		}
	}

	pub fn resolve(&self) -> Result<PathBuf,Error> {
		let mut path = self.base.parent().unwrap().to_owned();
		let source = self.source.strip_prefix("./").unwrap();
		path.push(&source);

		Ok(path)
	}

	pub fn alias(&self) -> String {
		self.alias.clone()
	}

	pub fn new_with_alias(source: String, base: &PathBuf, alias: &String) -> Import {
		Import {
			source: PathBuf::from(source.clone()),
			alias: alias.clone(),
			base: base.clone()
		}
	}
}

impl fmt::Display for Import {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "import {} as {}", self.source.clone().into_os_string().into_string().unwrap(), self.alias)
	}
}

impl fmt::Debug for Import {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "import(source: {}, alias: {})", self.source.clone().into_os_string().into_string().unwrap(), self.alias)
    }
}

pub struct Importer {

}

impl Importer {
	pub fn new() -> Importer {
		Importer {

		}
	}

	pub	fn apply_imports<T: Field>(&self, origins: Vec<(Prog<T>, String)>, destination: Prog<T>) -> Prog<T> {
		let mut imported_mains: Vec<Function<T>> = origins.iter().map(|origin| {
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

		imported_mains.append(&mut destination.clone().functions);

		Prog {
			imports: vec![],
			functions: imported_mains
		}
	}
}

#[cfg(test)]
mod tests {

	use super::*;

	#[test]
	fn create_with_no_alias() {
		assert_eq!(Import::new("./foo/bar/baz.code".to_string(), &PathBuf::from("/path/to/dir")), Import {
			source: PathBuf::from("./foo/bar/baz.code"),
			alias: "baz".to_string(),
			base: PathBuf::from("/path/to/dir")
		});
	}

	#[test]
	fn create_with_alias() {
		assert_eq!(Import::new_with_alias("./foo/bar/baz.code".to_string(), &PathBuf::from("/path/to/dir"), &"myalias".to_string()), Import {
			source: PathBuf::from("./foo/bar/baz.code"),
			alias: "myalias".to_string(),
			base: PathBuf::from("/path/to/dir")
		});
	}
}