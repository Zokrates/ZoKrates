//! Module containing the complete compilation pipeline.
//!
//! @file compile.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018
use absy::Prog;
use field::Field;
use flat_absy::FlatProg;
use flatten::Flattener;
use imports::{self, Importer};
use optimizer::Optimizer;
use parser::{self, parse_program};
use semantics::{self, Checker};
use static_analysis::Analyse;
use std::fmt;
use std::io;
use std::io::BufRead;

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

pub fn compile<T: Field, R: BufRead, S: BufRead, E: Into<imports::Error>>(
    reader: &mut R,
    location: Option<String>,
    resolve_option: Option<fn(&Option<String>, &String) -> Result<(S, String, String), E>>,
) -> Result<FlatProg<T>, CompileError<T>> {
    let compiled = compile_aux(reader, location, resolve_option)?;
    Ok(Optimizer::new().optimize_program(compiled))
}

pub fn compile_aux<T: Field, R: BufRead, S: BufRead, E: Into<imports::Error>>(
    reader: &mut R,
    location: Option<String>,
    resolve_option: Option<fn(&Option<String>, &String) -> Result<(S, String, String), E>>,
) -> Result<FlatProg<T>, CompileError<T>> {
    let program_ast_without_imports: Prog<T> = parse_program(reader)?;

    let program_ast = Importer::new().apply_imports(
        program_ast_without_imports,
        location.clone(),
        resolve_option,
    )?;

    // check semantics
    let typed_ast = Checker::new().check_program(program_ast)?;

    // analyse (unroll and constant propagation)
    let typed_ast = typed_ast.analyse();

    // flatten input program
    let program_flattened = Flattener::new(T::get_required_bits()).flatten_program(typed_ast);

    // analyse (constant propagation after call resolution)
    let program_flattened = program_flattened.analyse();

    Ok(program_flattened)
}

#[cfg(test)]
mod test {
    use super::*;
    use field::FieldPrime;
    use std::io::{BufReader, Empty};

    #[test]
    fn no_resolver_with_imports() {
        let mut r = BufReader::new(
            r#"
			import "./path/to/file" as foo
			def main() -> (field):
			   return foo()
		"#
            .as_bytes(),
        );
        let res: Result<FlatProg<FieldPrime>, CompileError<FieldPrime>> = compile(
            &mut r,
            Some(String::from("./path/to/file")),
            None::<
                fn(&Option<String>, &String)
                    -> Result<(BufReader<Empty>, String, String), io::Error>,
            >,
        );
        assert_eq!(
            format!("{}", res.unwrap_err()),
            "Import error: Can't resolve import without a resolver".to_string()
        );
    }

    #[test]
    fn no_resolver_without_imports() {
        let mut r = BufReader::new(
            r#"
			def main() -> (field):
			   return 1
		"#
            .as_bytes(),
        );
        let res: Result<FlatProg<FieldPrime>, CompileError<FieldPrime>> = compile(
            &mut r,
            Some(String::from("./path/to/file")),
            None::<
                fn(&Option<String>, &String)
                    -> Result<(BufReader<Empty>, String, String), io::Error>,
            >,
        );
        assert!(res.is_ok());
    }
}
