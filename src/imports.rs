//! Module containing structs and enums to represent imports.
//!
//! @file imports.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.org>
//! @date 2018

use std::fmt;
use absy::*;
use field::Field;
use std::path::PathBuf;
use std::fs::File;
use parser::parse_program;
use semantics::Checker;
use flatten::Flattener;
use field::FieldPrime;


#[derive(PartialEq, Debug)]
pub struct Error {
	message: String
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

	// pub fn new_with_alias(source: String, alias: String) -> Import {
	// 	Import {
	// 		source,
	// 		alias: Some(alias)
	// 	}
	// }
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
	use field::FieldPrime;

	#[test]
	fn resolve_imports_test() {

	}
}