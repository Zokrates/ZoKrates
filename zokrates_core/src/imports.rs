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
use std::io;

pub struct CompiledImport<T: Field> {
	pub flat_func: FlatFunction<T>,
}

impl<T: Field> CompiledImport<T> {
	fn new(prog: FlatProg<T>, alias: String) -> CompiledImport<T> {
		match prog.functions.iter().find(|fun| fun.id == "main") {
        	Some(fun) => {
				CompiledImport { flat_func: 
					FlatFunction {
						id: alias,
						..fun.clone()
					}
				}
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

	pub	fn apply_imports<T: Field, S: BufRead, E: Into<Error>>(&self, destination: Prog<T>, location: Option<String>, resolve_option: Option<fn(&Option<String>, &String) -> Result<(S, String, String), E>>, should_include_gadgets: bool) -> Result<Prog<T>, CompileError<T>> {

		let mut origins: Vec<CompiledImport<T>> = vec![];

	    // to resolve imports, we need a resolver
	    match resolve_option {
	    	Some(resolve) => {
	    		// we have a resolver, pass each import through it
		    	for import in destination.imports.iter() {
		    		// find the absolute path for the import, based on the path of the file which imports it
		    		match resolve(&location, &import.source) {
		    			Ok((mut reader, location, auto_alias)) => {
				    		let compiled = compile_aux(&mut reader, Some(location), resolve_option, should_include_gadgets)?;
				    		let alias = match import.alias {
				    			Some(ref alias) => alias.clone(),
				    			None => auto_alias
				    		};
					    	origins.push(CompiledImport::new(compiled, alias));
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
	    	use libsnark::{get_sha256_constraints, get_ethsha256_constraints};
	    	use standard::{R1CS,DirectiveR1CS};
	    	use serde_json::from_str;
			use helpers::{DirectiveStatement, Helper, LibsnarkGadgetHelper};

		    if should_include_gadgets {
		    	// inject globals
			    let r1cs : R1CS = from_str(&get_sha256_constraints()).unwrap();
				let dr1cs : DirectiveR1CS = DirectiveR1CS { r1cs: r1cs,
					directive : Some(LibsnarkGadgetHelper::Sha256Compress) 
				};
			    origins.push(CompiledImport::new(FlatProg::from(dr1cs), "sha256libsnark".to_string()));

			    let r1cs: R1CS = from_str(&get_ethsha256_constraints()).unwrap();
				let dr1cs : DirectiveR1CS = DirectiveR1CS { r1cs: r1cs,
					directive : Some(LibsnarkGadgetHelper::Sha256Ethereum)
				};
			    origins.push(CompiledImport::new(FlatProg::from(dr1cs), "ethSha256libsnark".to_string()));
		    }
	   	}
	  

		Ok(Prog {
			imports: vec![],
			functions: destination.clone().functions,
			imported_functions: origins.into_iter().map(|o| o.flat_func).collect()
		})
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