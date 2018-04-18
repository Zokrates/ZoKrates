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


#[derive(PartialEq, Clone, Serialize, Deserialize)]
pub struct Import {
	source: PathBuf,
	alias: Option<String>,
	base: PathBuf
}

impl Import {
	pub fn new(source: String, base: &PathBuf) -> Import {
		Import {
			source: PathBuf::from(source),
			alias: None,
			base: base.clone()
		}
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
		match &self.alias {
			&Some(ref a) => write!(f, "import {} as {}", self.source.clone().into_os_string().into_string().unwrap(), a),
			&None => write!(f, "import {}", self.source.clone().into_os_string().into_string().unwrap())
		}
	}
}

impl fmt::Debug for Import {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match &self.alias {
			&Some(ref a) => write!(f, "import(source: {}, alias: {})", self.source.clone().into_os_string().into_string().unwrap(), a),
			&None => write!(f, "import(source: {})", self.source.clone().into_os_string().into_string().unwrap())
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

	pub fn resolve_imports<T: Field>(&self, prog: Prog<T>) -> Result<Prog<T>,String> {
		let mut p = prog.clone();
		let imported_functions: Result<Vec<Function<T>>, String> = p.imports
			.clone()
			.into_iter()
			.map(|i| self.resolve_import::<T>(i))
			.collect();

		match imported_functions {
			Ok(mut funs) => {
				funs.append(&mut p.functions);
				Ok(Prog {
					imports: vec![],
					functions: funs
				})
			},
			Err(e) => Err(e)
		}
	}

	fn resolve_import<T: Field>(&self, import: Import) -> Result<Function<T>,String> {
		let mut path = import.base.parent().unwrap().to_owned();
		let source = import.source.strip_prefix("./").unwrap();
		path.push(&source);

		let file = match File::open(&path) {
            Ok(file) => file,
            Err(why) => panic!("couldn't open {}: {}", path.display(), why),
        };

        let program_ast_without_imports = match parse_program(file, path) {
        	Ok(prog) => prog,
        	Err(why) => panic!(why.to_string())
        };

        let program_ast = match self.resolve_imports(program_ast_without_imports) {
        	Ok(prog) => prog,
        	Err(why) => panic!(why.to_string())
        };

                    // check semantics
        match Checker::new().check_program(program_ast.clone()) {
            Ok(()) => (),
            Err(why) => panic!(why.to_string())
        };

        // flatten input program
        let program_flattened =
            Flattener::new(FieldPrime::get_required_bits()).flatten_program(program_ast);

        match program_flattened.functions.into_iter().find(|fun| fun.id == "main") {
        	Some(mut fun) => {
        		fun.id = source.file_stem().unwrap().to_os_string().to_string_lossy().to_string();
        		Ok(fun)
        	},
        	None => panic!("no main")
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