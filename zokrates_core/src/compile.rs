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
use semantics::{self, Checker};
use static_analysis::Analyse;
use std::fmt;
use std::io;
use std::io::BufRead;
use zokrates_field::field::Field;
use zokrates_pest_ast as pest;

#[derive(Debug)]
pub struct CompileErrors(Vec<CompileError>);

impl From<CompileError> for CompileErrors {
    fn from(e: CompileError) -> CompileErrors {
        CompileErrors(vec![e])
    }
}

impl fmt::Display for CompileErrors {
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
pub enum CompileErrorInner {
    ParserError(pest::Error),
    ImportError(imports::Error),
    SemanticError(semantics::Error),
    ReadError(io::Error),
}

impl CompileErrorInner {
    pub fn with_context(self, context: &Option<String>) -> CompileError {
        CompileError {
            value: self,
            context: context.clone(),
        }
    }
}

#[derive(Debug)]
pub struct CompileError {
    context: Option<String>,
    value: CompileErrorInner,
}

impl CompileErrors {
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

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let context = match self.context {
            Some(ref x) => x.clone(),
            None => "???".to_string(),
        };
        write!(f, "{}:{}", context, self.value)
    }
}

impl From<pest::Error> for CompileErrorInner {
    fn from(error: pest::Error) -> Self {
        CompileErrorInner::ParserError(error)
    }
}

impl From<imports::Error> for CompileErrorInner {
    fn from(error: imports::Error) -> Self {
        CompileErrorInner::ImportError(error)
    }
}

impl From<io::Error> for CompileErrorInner {
    fn from(error: io::Error) -> Self {
        CompileErrorInner::ReadError(error)
    }
}

impl From<semantics::Error> for CompileErrorInner {
    fn from(error: semantics::Error) -> Self {
        CompileErrorInner::SemanticError(error)
    }
}

impl fmt::Display for CompileErrorInner {
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
) -> Result<ir::Prog<T>, CompileErrors> {
    let compiled = compile_aux(reader, location, resolve_option)?;
    Ok(ir::Prog::from(Optimizer::new().optimize_program(compiled)))
}

pub fn compile_aux<T: Field, R: BufRead, S: BufRead, E: Into<imports::Error>>(
    reader: &mut R,
    location: Option<String>,
    resolve_option: Option<fn(&Option<String>, &String) -> Result<(S, String, String), E>>,
) -> Result<FlatProg<T>, CompileErrors> {
    let mut source = String::new();
    reader.read_to_string(&mut source).unwrap();
    let ast = pest::generate_ast(&source)
        .map_err(|e| CompileErrors::from(CompileErrorInner::from(e).with_context(&location)))?;
    let program_ast_without_imports: Prog<T> = Prog::from(ast);

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
    let program_flattened = Flattener::flatten(typed_ast);

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
        let res: Result<ir::Prog<FieldPrime>, CompileErrors> = compile(
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
        let res: Result<ir::Prog<FieldPrime>, CompileErrors> = compile(
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
