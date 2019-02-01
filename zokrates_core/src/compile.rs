//! Module containing the complete compilation pipeline.
//!
//! @file compile.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018
use absy::Prog;
use flat_absy::FlatProg;
use flatten::Flattener;
use imports::{self, Importer};
use ir;
use optimizer::Optimizer;
use parser::{self, parse_program};
use semantics::{self, Checker};
use static_analysis::Analyse;
use std::fmt;
use std::io;
use std::io::BufRead;
use zokrates_field::field::Field;

#[derive(Debug)]
pub struct CompileErrors<T: Field>(Vec<CompileError<T>>);

impl<T: Field> From<CompileError<T>> for CompileErrors<T> {
    fn from(e: CompileError<T>) -> CompileErrors<T> {
        CompileErrors(vec![e])
    }
}

impl<T: Field> fmt::Display for CompileErrors<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            self.0
                .iter()
                .map(|e| format!("{}", e))
                .collect::<Vec<_>>()
                .join("\n\n")
        )
    }
}

#[derive(Debug)]
pub enum CompileErrorInner<T: Field> {
    ParserError(parser::Error<T>),
    ImportError(imports::Error),
    SemanticError(semantics::Error),
    ReadError(io::Error),
}

impl<T: Field> CompileErrorInner<T> {
    pub fn with_context(self, context: &Option<String>) -> CompileError<T> {
        CompileError {
            value: self,
            context: context.clone(),
        }
    }
}

#[derive(Debug)]
pub struct CompileError<T: Field> {
    context: Option<String>,
    value: CompileErrorInner<T>,
}

impl<T: Field> CompileErrors<T> {
    pub fn with_context(self, context: Option<String>) -> Self {
        CompileErrors(
            self.0
                .into_iter()
                .map(|e| CompileError {
                    context: context.clone(),
                    ..e
                })
                .collect(),
        )
    }
}

impl<T: Field> fmt::Display for CompileError<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let context = match self.context {
            Some(ref x) => x.clone(),
            None => "???".to_string(),
        };
        write!(f, "{}:{}", context, self.value)
    }
}

impl<T: Field> From<parser::Error<T>> for CompileErrorInner<T> {
    fn from(error: parser::Error<T>) -> Self {
        CompileErrorInner::ParserError(error)
    }
}

impl<T: Field> From<imports::Error> for CompileErrorInner<T> {
    fn from(error: imports::Error) -> Self {
        CompileErrorInner::ImportError(error)
    }
}

impl<T: Field> From<io::Error> for CompileErrorInner<T> {
    fn from(error: io::Error) -> Self {
        CompileErrorInner::ReadError(error)
    }
}

impl<T: Field> From<semantics::Error> for CompileErrorInner<T> {
    fn from(error: semantics::Error) -> Self {
        CompileErrorInner::SemanticError(error)
    }
}

impl<T: Field> fmt::Display for CompileErrorInner<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let res = match *self {
            CompileErrorInner::ParserError(ref e) => format!("{}", e),
            CompileErrorInner::SemanticError(ref e) => format!("{}", e),
            CompileErrorInner::ReadError(ref e) => format!("{}", e),
            CompileErrorInner::ImportError(ref e) => format!("{}", e),
        };
        write!(f, "{}", res)
    }
}

pub fn compile<T: Field, R: BufRead, S: BufRead, E: Into<imports::Error>>(
    reader: &mut R,
    location: Option<String>,
    resolve_option: Option<fn(&Option<String>, &String) -> Result<(S, String, String), E>>,
) -> Result<ir::Prog<T>, CompileErrors<T>> {
    let compiled = compile_aux(reader, location, resolve_option)?;
    Ok(ir::Prog::from(Optimizer::new().optimize_program(compiled)))
}

pub fn compile_aux<T: Field, R: BufRead, S: BufRead, E: Into<imports::Error>>(
    reader: &mut R,
    location: Option<String>,
    resolve_option: Option<fn(&Option<String>, &String) -> Result<(S, String, String), E>>,
) -> Result<FlatProg<T>, CompileErrors<T>> {
    let program_ast_without_imports: Prog<T> = parse_program(reader)
        .map_err(|e| CompileErrors::from(CompileErrorInner::from(e).with_context(&location)))?;

    let program_ast = Importer::new().apply_imports(
        program_ast_without_imports,
        location.clone(),
        resolve_option,
    )?;

    // check semantics
    let typed_ast = Checker::new()
        .check_program(program_ast)
        .map_err(|errors| {
            CompileErrors(
                errors
                    .into_iter()
                    .map(|e| CompileErrorInner::from(e).with_context(&location))
                    .collect(),
            )
        })?;

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
    use std::io::{BufReader, Empty};
    use zokrates_field::field::FieldPrime;

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
        let res: Result<ir::Prog<FieldPrime>, CompileErrors<FieldPrime>> = compile(
            &mut r,
            Some(String::from("./path/to/file")),
            None::<
                fn(
                    &Option<String>,
                    &String,
                ) -> Result<(BufReader<Empty>, String, String), io::Error>,
            >,
        );

        assert!(res
            .unwrap_err()
            .to_string()
            .contains(&"Can't resolve import without a resolver"));
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
        let res: Result<ir::Prog<FieldPrime>, CompileErrors<FieldPrime>> = compile(
            &mut r,
            Some(String::from("./path/to/file")),
            None::<
                fn(
                    &Option<String>,
                    &String,
                ) -> Result<(BufReader<Empty>, String, String), io::Error>,
            >,
        );
        assert!(res.is_ok());
    }
}
