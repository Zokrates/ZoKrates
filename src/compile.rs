//! Module containing the complete compilation pipeline.
//!
//! @file compile.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.org>
//! @date 2018
use std::fs::File;
use std::path::{Path, PathBuf};
use std::collections::HashMap;
use std::string::String;
use field::{Field, FieldPrime};
use absy::{Prog};
use parser::{self, parse_program};
use imports::{self, Importer};
use semantics::{self, Checker};
use flatten::Flattener;

#[derive(PartialEq, Debug)]
pub enum CompileError<T: Field> {
	ParserError(parser::Error<T>),
	ImportError(imports::Error),
	SemanticError(semantics::Error)
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

impl<T: Field> From<semantics::Error> for CompileError<T> {
	fn from(error: semantics::Error) -> Self {
		CompileError::SemanticError(error)
	}
}

pub fn compile<T: Field>(path: PathBuf) -> Result<Prog<T>, CompileError<T>> {
	let file = File::open(&path).unwrap();

    let program_ast_without_imports: Prog<T> = parse_program(file, path.to_owned()).unwrap();

    let mut compiled_imports: Vec<(Prog<T>, String)> = vec![];

    for import in program_ast_without_imports.clone().imports {
    	let path = import.resolve()?;
    	let compiled = compile(path)?;
    	compiled_imports.push((compiled, import.alias()));
    }
    	
    let program_ast = Importer::new().apply_imports(compiled_imports, program_ast_without_imports);

    // check semantics
    Checker::new().check_program(program_ast.clone()).unwrap();

    // flatten input program
    let program_flattened =
        Flattener::new(T::get_required_bits()).flatten_program(program_ast);

    Ok(program_flattened)
}