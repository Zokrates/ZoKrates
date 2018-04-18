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
use parser::{parse_program, Error};
use imports::Importer;
use semantics::Checker;
use flatten::Flattener;

pub fn compile<T: Field>(path: PathBuf) -> Result<Prog<T>,()> {
	let file = File::open(&path).unwrap();

    let program_ast_without_imports: Prog<T> = parse_program(file, path.to_owned()).unwrap();

    let program_ast = Importer::new().resolve_imports(program_ast_without_imports).unwrap();

    // check semantics
    Checker::new().check_program(program_ast.clone()).unwrap();

    // flatten input program
    let program_flattened =
        Flattener::new(T::get_required_bits()).flatten_program(program_ast);

    Ok(program_flattened)
}