//! Module containing structs and enums to represent imports.
//!
//! @file imports.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use compile::CompileError;
use std::io::BufRead;
use compile::compile_aux;
use std::fmt;
use absy::*;
use flat_absy::*;
use field::Field;
use std::path::PathBuf;
use std::io;

pub struct CompiledImport<T: Field> {
	pub flat_func: FlatFunction<T>,
}

impl<T: Field> CompiledImport<T> {
	fn new(prog: FlatProg<T>, alias: String) -> CompiledImport<T> {
		match prog.functions.iter().find(|fun| fun.id == "main") {
        	Some(fun) => {
        		let mut f = fun.clone();
        		f.id = alias.to_string();
        		CompiledImport { flat_func: f }
        	},
        	None => panic!("no main")
        }
	}
}

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
	source: PathBuf,
	alias: String,
}

impl Import {
	pub fn new(source: String) -> Import {
		Import {
			source: PathBuf::from(source.clone()),
			alias: PathBuf::from(source).file_stem().unwrap().to_os_string().to_string_lossy().to_string(),
		}
	}

	pub fn alias(&self) -> String {
		self.alias.clone()
	}

	pub fn new_with_alias(source: String, alias: &String) -> Import {
		Import {
			source: PathBuf::from(source.clone()),
			alias: alias.clone(),
		}
	}

	pub fn get_source(&self) -> &PathBuf {
		&self.source
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

	pub	fn apply_imports<T: Field, S: BufRead, E: Into<Error>>(&self, destination: Prog<T>, location: PathBuf, resolve_option: Option<fn(&PathBuf) -> Result<S, E>>, should_include_gadgets: bool) -> Result<Prog<T>, CompileError<T>> {

		let mut origins: Vec<CompiledImport<T>> = vec![];

	    // to resolve imports, we need a resolver
	    match resolve_option {
	    	Some(resolve) => {
	    		// we have a resolver, pass each import through it
		    	for import in destination.imports.iter() {
		    		// find the absolute path for the import, based on the path of the file which imports it
		    		let absolute_import_path = location.join(import.get_source());
		    		match resolve(&absolute_import_path) {
		    			Ok(mut res) => {
				    		let compiled = compile_aux(&mut res, absolute_import_path.parent().unwrap().to_path_buf(), resolve_option, should_include_gadgets)?;
					    	origins.push(CompiledImport::new(compiled, import.alias()));
				    	},
		    			Err(err) => return Err(CompileError::ImportError(err.into()))
		    		}
		    	}
	    	},
	    	None => {
	    		if destination.imports.len() > 0 {
	    			return Err(Error::new("Can't resolve import without a resolver").into())
	    		}
	    	}
	    }

	    #[cfg(feature = "libsnark")]
	    {
	    	use libsnark::{get_sha256_constraints};
	    	use standard::R1CS;
	    	use serde_json::from_str;

		    if should_include_gadgets {
		    	// inject globals
			    let r1cs: R1CS = from_str(&get_sha256_constraints()).unwrap();

			    compiled_imports.push((FlatProg::from(r1cs), "sha256libsnark".to_string()));
		    }
	   	}


		Ok(Prog {
			imports: vec![],
			functions: destination.clone().functions,
			imported_functions: origins.iter().map(|o| o.flat_func.clone()).collect()
		})
	}
}

#[cfg(test)]
mod tests {

	use super::*;

	#[test]
	fn create_with_no_alias() {
		assert_eq!(Import::new("./foo/bar/baz.code".to_string()), Import {
			source: PathBuf::from("./foo/bar/baz.code"),
			alias: "baz".to_string(),
		});
	}

	#[test]
	fn create_with_alias() {
		assert_eq!(Import::new_with_alias("./foo/bar/baz.code".to_string(), &"myalias".to_string()), Import {
			source: PathBuf::from("./foo/bar/baz.code"),
			alias: "myalias".to_string(),
		});
	}
}