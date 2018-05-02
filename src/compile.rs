//! Module containing the complete compilation pipeline.
//!
//! @file compile.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018
use std::fs::File;
use std::path::{PathBuf};
use std::fmt;
use field::{Field, FieldPrime};
use absy::{Prog};
use flat_absy::{FlatProg};
use parser::{self, parse_program};
use semantics::{self, Checker};
use flatten::Flattener;
use std::io::{self};

#[derive(Debug)]
pub enum CompileError<T: Field> {
	ParserError(parser::Error<T>),
	SemanticError(semantics::Error),
	ReadError(io::Error)
}

impl<T: Field> From<parser::Error<T>> for CompileError<T> {
	fn from(error: parser::Error<T>) -> Self {
		CompileError::ParserError(error)
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

impl fmt::Display for CompileError<FieldPrime> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		let res = match *self {
			CompileError::ParserError(ref e) => format!("Syntax error: {}", e),
			CompileError::SemanticError(ref e) => format!("Semantic error: {}", e),
			CompileError::ReadError(ref e) => format!("Read error: {}", e)
		};
		write!(f, "{}", res)
	}
}

pub fn compile<T: Field>(path: PathBuf) -> Result<FlatProg<T>, CompileError<T>> {
	let file = File::open(&path)?;

    let program_ast: Prog<T> = parse_program(file)?;

    // check semantics
    Checker::new().check_program(program_ast.clone())?;

    // flatten input program
    let program_flattened =
        Flattener::new(T::get_required_bits()).flatten_program(program_ast);

    Ok(program_flattened)
}