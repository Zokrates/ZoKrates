//! Module containing the complete compilation pipeline.
//!
//! @file compile.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018
use absy::{Module, ModuleId, Program};
use flatten::Flattener;
use imports::{self, Importer};
use ir;
use optimizer::Optimize;
use semantics::{self, Checker};
use static_analysis::Analyse;
use std::collections::HashMap;
use std::fmt;
use std::io;
use std::path::PathBuf;
use typed_absy::abi::Abi;
use typed_arena::Arena;
use zokrates_field::field::Field;
use zokrates_pest_ast as pest;

#[derive(Debug)]
pub struct CompilationArtifacts<T: Field> {
    prog: ir::Prog<T>,
    abi: Abi,
}

impl<T: Field> CompilationArtifacts<T> {
    pub fn prog(&self) -> &ir::Prog<T> {
        &self.prog
    }

    pub fn abi(&self) -> &Abi {
        &self.abi
    }
}

#[derive(Debug)]
pub struct CompileErrors(pub Vec<CompileError>);

impl From<CompileError> for CompileErrors {
    fn from(e: CompileError) -> CompileErrors {
        CompileErrors(vec![e])
    }
}

#[derive(Debug)]
pub enum CompileErrorInner {
    ParserError(pest::Error),
    ImportError(imports::Error),
    SemanticError(semantics::ErrorInner),
    ReadError(io::Error),
}

impl CompileErrorInner {
    pub fn in_file(self, context: &PathBuf) -> CompileError {
        CompileError {
            value: self,
            file: context.clone(),
        }
    }
}

#[derive(Debug)]
pub struct CompileError {
    file: PathBuf,
    value: CompileErrorInner,
}

impl CompileError {
    pub fn file(&self) -> &PathBuf {
        &self.file
    }

    pub fn value(&self) -> &CompileErrorInner {
        &self.value
    }
}

impl CompileErrors {
    pub fn with_context(self, file: PathBuf) -> Self {
        CompileErrors(
            self.0
                .into_iter()
                .map(|e| CompileError {
                    file: file.clone(),
                    ..e
                })
                .collect(),
        )
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

impl From<semantics::Error> for CompileError {
    fn from(error: semantics::Error) -> Self {
        CompileError {
            value: CompileErrorInner::SemanticError(error.inner),
            file: error.module_id,
        }
    }
}

impl fmt::Display for CompileErrorInner {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            CompileErrorInner::ParserError(ref e) => write!(f, "{}", e),
            CompileErrorInner::SemanticError(ref e) => write!(f, "{}", e),
            CompileErrorInner::ReadError(ref e) => write!(f, "{}", e),
            CompileErrorInner::ImportError(ref e) => write!(f, "{}", e),
        }
    }
}

// See zokrates_fs_resolver for the spec
pub type Resolve<'a, E> = &'a dyn Fn(PathBuf, PathBuf) -> Result<(String, PathBuf), E>;

type FilePath = PathBuf;

pub fn compile<T: Field, E: Into<imports::Error>>(
    source: String,
    location: FilePath,
    resolve_option: Option<Resolve<E>>,
) -> Result<CompilationArtifacts<T>, CompileErrors> {
    let arena = Arena::new();

    let source = arena.alloc(source);
    let compiled = compile_program(source, location.clone(), resolve_option, &arena)?;

    // check semantics
    let typed_ast = Checker::check(compiled).map_err(|errors| {
        CompileErrors(errors.into_iter().map(|e| CompileError::from(e)).collect())
    })?;

    let abi = typed_ast.abi();

    // analyse (unroll and constant propagation)
    let typed_ast = typed_ast.analyse();

    // flatten input program
    let program_flattened = Flattener::flatten(typed_ast);

    // analyse (constant propagation after call resolution)
    let program_flattened = program_flattened.analyse();

    // convert to ir
    let ir_prog = ir::Prog::from(program_flattened);

    // optimize
    let optimized_ir_prog = ir_prog.optimize();

    Ok(CompilationArtifacts {
        prog: optimized_ir_prog,
        abi: abi,
    })
}

pub fn compile_program<'ast, T: Field, E: Into<imports::Error>>(
    source: &'ast str,
    location: FilePath,
    resolve_option: Option<Resolve<E>>,
    arena: &'ast Arena<String>,
) -> Result<Program<'ast, T>, CompileErrors> {
    let mut modules = HashMap::new();

    let main = compile_module(
        &source,
        location.clone(),
        resolve_option,
        &mut modules,
        &arena,
    )?;

    modules.insert(location.clone(), main);

    Ok(Program {
        main: location,
        modules,
    })
}

pub fn compile_module<'ast, T: Field, E: Into<imports::Error>>(
    source: &'ast str,
    location: FilePath,
    resolve_option: Option<Resolve<E>>,
    modules: &mut HashMap<ModuleId, Module<'ast, T>>,
    arena: &'ast Arena<String>,
) -> Result<Module<'ast, T>, CompileErrors> {
    let ast = pest::generate_ast(&source)
        .map_err(|e| CompileErrors::from(CompileErrorInner::from(e).in_file(&location)))?;
    let module_without_imports: Module<T> = Module::from(ast);

    Importer::new().apply_imports(
        module_without_imports,
        location.clone(),
        resolve_option,
        modules,
        &arena,
    )
}

#[cfg(test)]
mod test {
    use super::*;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn no_resolver_with_imports() {
        let source = r#"
			import "./path/to/file" as foo
			def main() -> (field):
			   return foo()
		"#
        .to_string();
        let res: Result<CompilationArtifacts<FieldPrime>, CompileErrors> =
            compile(source, "./path/to/file".into(), None::<Resolve<io::Error>>);
        assert!(res.unwrap_err().0[0]
            .value()
            .to_string()
            .contains(&"Can't resolve import without a resolver"));
    }

    #[test]
    fn no_resolver_without_imports() {
        let source = r#"
			def main() -> (field):
			   return 1
		"#
        .to_string();
        let res: Result<CompilationArtifacts<FieldPrime>, CompileErrors> =
            compile(source, "./path/to/file".into(), None::<Resolve<io::Error>>);
        assert!(res.is_ok());
    }
}
