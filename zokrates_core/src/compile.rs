//! Module containing the complete compilation pipeline.
//!
//! @file compile.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018
use std::io::{BufRead};
use std::fmt;
use std::path::PathBuf;
use field::{Field};
use absy::{Prog};
use flat_absy::{FlatProg};
use parser::{self, parse_program};
use imports::{self, Importer};
use semantics::{self, Checker};
use optimizer::{Optimizer};
use flatten::Flattener;
use std::io::{self};

#[derive(Debug)]
pub enum CompileError<T: Field> {
	ParserError(parser::Error<T>),
	ImportError(imports::Error),
	SemanticError(semantics::Error),
	ReadError(io::Error),
}

impl<T: Field> From<parser::Error<T>> for CompileError<T> {
	fn from(error: parser::Error<T>) -> Self {
		CompileError::ParserError(error)
	}
}

impl<T: Field> From<imports::Error> for CompileError<T> {
	fn from(error: imports::Error) -> Self {
		CompileError::ImportError(error)
	}
}

impl<T: Field> From<io::Error> for CompileError<T> {
	fn from(error: io::Error) -> Self {
		CompileError::ReadError(error)
	}
}

impl<T: Field> From<semantics::Error> for CompileError<T> {
	fn from(error: semantics::Error) -> Self {
		CompileError::SemanticError(error)
	}
}

impl<T: Field> fmt::Display for CompileError<T> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		let res = match *self {
			CompileError::ParserError(ref e) => format!("Syntax error: {}", e),
			CompileError::SemanticError(ref e) => format!("Semantic error: {}", e),
			CompileError::ReadError(ref e) => format!("Read error: {}", e),
			CompileError::ImportError(ref e) => format!("Import error: {}", e),
		};
		write!(f, "{}", res)
	}
}

pub fn compile<T: Field, R: BufRead, S: BufRead, E: Into<imports::Error>>(reader: &mut R, location: PathBuf, resolve_option: Option<fn(&PathBuf) -> Result<S, E>>, should_optimize: bool, should_include_gadgets: bool) -> Result<FlatProg<T>, CompileError<T>> {

	let compiled = compile_aux(reader, location, resolve_option, should_include_gadgets);

	match compiled {
		Ok(c) => match should_optimize {
			true => Ok(Optimizer::new().optimize_program(c)),
			_ => Ok(c)
		}
		err => err
	}
}

pub fn compile_aux<T: Field, R: BufRead, S: BufRead, E: Into<imports::Error>>(reader: &mut R, location: PathBuf, resolve_option: Option<fn(&PathBuf) -> Result<S, E>>, should_include_gadgets: bool) -> Result<FlatProg<T>, CompileError<T>> {
    let program_ast_without_imports: Prog<T> = parse_program(reader)?; 
    	
    let program_ast = Importer::new().apply_imports(program_ast_without_imports, location, resolve_option, should_include_gadgets)?;

    // check semantics
    let typed_ast = Checker::new().check_program(program_ast)?;

    // flatten input program
    let program_flattened =
        Flattener::new(T::get_required_bits()).flatten_program(typed_ast);

    Ok(program_flattened)
}

#[cfg(test)]
mod test {
	use super::*;
	use field::FieldPrime;
	use std::io::{BufReader, Empty};

	#[test]
	fn no_resolver_with_imports() {
		let mut r = BufReader::new(r#"
			import "./path/to/file" as foo
			def main() -> (field):
			   return foo()
		"#.as_bytes());
		let res: Result<FlatProg<FieldPrime>, CompileError<FieldPrime>> = compile(&mut r, PathBuf::from("./path/to/file"), None::<fn(&PathBuf) -> Result<BufReader<Empty>, io::Error>>, false, false);
		assert_eq!(format!("{}", res.unwrap_err()), "Import error: Can't resolve import without a resolver".to_string()); 
	}

	#[test]
	fn no_resolver_without_imports() {
		let mut r = BufReader::new(r#"
			def main() -> (field):
			   return 1
		"#.as_bytes());
		let res: Result<FlatProg<FieldPrime>, CompileError<FieldPrime>> = compile(&mut r, PathBuf::from("./path/to/file"), None::<fn(&PathBuf) -> Result<BufReader<Empty>, io::Error>>, false, false);
		assert!(res.is_ok()); 
	}
}