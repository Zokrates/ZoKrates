//! Module containing the complete compilation pipeline.
//!
//! @file compile.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018
use crate::imports::{self, Importer};
use crate::macros;
use crate::optimizer::optimize;
use crate::semantics::{self, Checker};
use macros::process_macros;
use std::collections::HashMap;
use std::fmt;
use std::io;
use std::path::{Path, PathBuf};
use typed_arena::Arena;
use zokrates_analysis::{self, analyse};
use zokrates_ast::ir::{self, from_flat::from_flat};
use zokrates_ast::typed::abi::Abi;
use zokrates_ast::untyped::{Module, OwnedModuleId, Program};
use zokrates_ast::zir::ZirProgram;
use zokrates_codegen::from_program_and_config;
pub use zokrates_common::{CompileConfig, Resolver};
use zokrates_field::Field;
use zokrates_pest_ast as pest;

#[derive(Debug)]
pub struct CompilationArtifacts<'ast, T, I: IntoIterator<Item = ir::Statement<'ast, T>>> {
    prog: ir::ProgIterator<'ast, T, I>,
    abi: Abi,
}

impl<'ast, T, I: IntoIterator<Item = ir::Statement<'ast, T>>> CompilationArtifacts<'ast, T, I> {
    pub fn prog(self) -> ir::ProgIterator<'ast, T, I> {
        self.prog
    }

    pub fn abi(&self) -> &Abi {
        &self.abi
    }

    pub fn into_inner(self) -> (ir::ProgIterator<'ast, T, I>, Abi) {
        (self.prog, self.abi)
    }

    pub fn collect(self) -> CompilationArtifacts<'ast, T, Vec<ir::Statement<'ast, T>>> {
        CompilationArtifacts {
            prog: self.prog.collect(),
            abi: self.abi,
        }
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
    MacroError(macros::Error),
    SemanticError(semantics::ErrorInner),
    ReadError(io::Error),
    AnalysisError(zokrates_analysis::Error),
}

impl CompileErrorInner {
    pub fn in_file(self, context: &Path) -> CompileError {
        CompileError {
            value: self,
            file: context.to_path_buf(),
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

impl From<macros::Error> for CompileErrorInner {
    fn from(error: macros::Error) -> Self {
        CompileErrorInner::MacroError(error)
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

impl From<zokrates_analysis::Error> for CompileErrorInner {
    fn from(error: zokrates_analysis::Error) -> Self {
        CompileErrorInner::AnalysisError(error)
    }
}

impl fmt::Display for CompileErrorInner {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            CompileErrorInner::ParserError(ref e) => write!(f, "\n\t{}", e),
            CompileErrorInner::MacroError(ref e) => write!(f, "\n\t{}", e),
            CompileErrorInner::SemanticError(ref e) => {
                let location = e.pos().map(|p| format!("{}", p.from)).unwrap_or_default();
                write!(f, "{}\n\t{}", location, e.message())
            }
            CompileErrorInner::ReadError(ref e) => write!(f, "\n\t{}", e),
            CompileErrorInner::ImportError(ref e) => {
                let location = e.span().map(|p| format!("{}", p.from)).unwrap_or_default();
                write!(f, "{}\n\t{}", location, e.message())
            }
            CompileErrorInner::AnalysisError(ref e) => write!(f, "\n\t{}", e),
        }
    }
}

type FilePath = PathBuf;

pub fn compile<'ast, T: Field, E: Into<imports::Error>>(
    source: String,
    location: FilePath,
    resolver: Option<&dyn Resolver<E>>,
    config: CompileConfig,
    arena: &'ast Arena<String>,
) -> Result<
    CompilationArtifacts<'ast, T, impl IntoIterator<Item = ir::Statement<'ast, T>> + 'ast>,
    CompileErrors,
> {
    let (typed_ast, abi): (zokrates_ast::zir::ZirProgram<'_, T>, _) =
        check_with_arena(source, location, resolver, &config, arena)?;

    // flatten input program
    log::debug!("Flatten");
    let program_flattened = from_program_and_config(typed_ast, config);

    // convert to ir
    log::debug!("Convert to IR");
    let ir_prog = from_flat(program_flattened);

    // optimize
    log::debug!("Optimise IR");
    let optimized_ir_prog = optimize(ir_prog);

    // clean (remove blocks)
    let clean_ir_prog = optimized_ir_prog.clean();

    Ok(CompilationArtifacts {
        prog: clean_ir_prog,
        abi,
    })
}

pub fn check<T: Field, E: Into<imports::Error>>(
    source: String,
    location: FilePath,
    resolver: Option<&dyn Resolver<E>>,
    config: &CompileConfig,
) -> Result<(), CompileErrors> {
    let arena = Arena::new();

    check_with_arena::<T, _>(source, location, resolver, config, &arena).map(|_| ())
}

fn check_with_arena<'ast, T: Field, E: Into<imports::Error>>(
    source: String,
    location: FilePath,
    resolver: Option<&dyn Resolver<E>>,
    config: &CompileConfig,
    arena: &'ast Arena<String>,
) -> Result<(ZirProgram<'ast, T>, Abi), CompileErrors> {
    let source = arena.alloc(source);

    log::debug!("Parse program with entry file {}", location.display());

    let compiled = parse_program::<T, E>(source, location, resolver, arena)?;

    log::debug!("Check semantics");

    // check semantics
    let typed_ast = Checker::check(compiled)
        .map_err(|errors| CompileErrors(errors.into_iter().map(CompileError::from).collect()))?;

    log::trace!("\n{}", typed_ast);

    let main_module = typed_ast.main.clone();

    log::debug!("Run static analysis");

    // analyse (unroll and constant propagation)
    analyse(typed_ast, config)
        .map_err(|e| CompileErrors(vec![CompileErrorInner::from(e).in_file(&main_module)]))
}

pub fn parse_program<'ast, T: Field, E: Into<imports::Error>>(
    source: &'ast str,
    location: FilePath,
    resolver: Option<&dyn Resolver<E>>,
    arena: &'ast Arena<String>,
) -> Result<Program<'ast>, CompileErrors> {
    let mut modules = HashMap::new();

    let main = parse_module::<T, E>(source, location.clone(), resolver, &mut modules, arena)?;

    modules.insert(location.clone(), main);

    Ok(Program {
        main: location,
        modules,
    })
}

pub fn parse_module<'ast, T: Field, E: Into<imports::Error>>(
    source: &'ast str,
    location: FilePath,
    resolver: Option<&dyn Resolver<E>>,
    modules: &mut HashMap<OwnedModuleId, Module<'ast>>,
    arena: &'ast Arena<String>,
) -> Result<Module<'ast>, CompileErrors> {
    log::debug!("Generate pest AST for {}", location.display());

    let ast = pest::generate_ast(source)
        .map_err(|e| CompileErrors::from(CompileErrorInner::from(e).in_file(&location)))?;

    log::debug!("Process macros for {}", location.display());

    let ast = process_macros::<T>(ast)
        .map_err(|e| CompileErrors::from(CompileErrorInner::from(e).in_file(&location)))?;

    log::debug!("Generate absy for {}", location.display());

    let module_without_imports: Module = Module::from(ast);

    log::debug!("Apply imports to absy for {}", location.display());

    Importer::apply_imports::<T, E>(
        module_without_imports,
        location.clone(),
        resolver,
        modules,
        arena,
    )
}

#[cfg(test)]
mod test {
    use super::*;
    use zokrates_field::Bn128Field;

    #[test]
    fn no_resolver_with_imports() {
        let source = r#"
            import "./path/to/file" as foo;
            def main() -> field {
                return foo();
            }
        "#
        .to_string();
        let arena = Arena::new();
        let res: Result<CompilationArtifacts<Bn128Field, _>, CompileErrors> = compile(
            source,
            "./path/to/file".into(),
            None::<&dyn Resolver<io::Error>>,
            CompileConfig::default(),
            &arena,
        )
        .map(|res| res.collect());

        let e = res.unwrap_err();
        assert!(e.0[0]
            .value()
            .to_string()
            .contains("Cannot resolve import without a resolver"));
    }

    #[test]
    fn no_resolver_without_imports() {
        let source = r#"
            def main() -> field {
                return 1;
            }
        "#
        .to_string();

        let arena = Arena::new();

        let res: Result<CompilationArtifacts<Bn128Field, _>, CompileErrors> = compile(
            source,
            "./path/to/file".into(),
            None::<&dyn Resolver<io::Error>>,
            CompileConfig::default(),
            &arena,
        );
        assert!(res.is_ok());
    }

    mod abi {
        use super::*;
        use zokrates_ast::typed::abi::*;
        use zokrates_ast::typed::types::*;

        #[test]
        fn use_struct_declaration_types() {
            // when importing types and renaming them, we use the canonical struct names in the ABI

            // // main.zok
            // from foo import Foo as FooMain;
            //
            // // foo.zok
            // from bar import Bar as BarFoo;
            // struct Foo { BarFoo b; }
            //
            // // bar.zok
            // struct Bar { field a; }

            // Expected resolved type for FooMain:
            // Foo { Bar b; }

            let main = r#"
from "foo" import Foo as FooMain;
def main(FooMain f) {
    return;
}
"#;

            struct CustomResolver;

            impl<E> Resolver<E> for CustomResolver {
                fn resolve(
                    &self,
                    _: PathBuf,
                    import_location: PathBuf,
                ) -> Result<(String, PathBuf), E> {
                    let loc = import_location.display().to_string();
                    if loc == "main" {
                        Ok((
                            r#"
from "foo" import Foo as FooMain;
def main(FooMain f) {
    return;
}
"#
                            .into(),
                            "main".into(),
                        ))
                    } else if loc == "foo" {
                        Ok((
                            r#"
from "bar" import Bar as BarFoo;
struct Foo {
    BarFoo b;
}
"#
                            .into(),
                            "foo".into(),
                        ))
                    } else if loc == "bar" {
                        Ok((
                            r#"
struct Bar { field a; }
"#
                            .into(),
                            "bar".into(),
                        ))
                    } else {
                        unreachable!()
                    }
                }
            }

            let arena = Arena::new();

            let artifacts = compile::<Bn128Field, io::Error>(
                main.to_string(),
                "main".into(),
                Some(&CustomResolver),
                CompileConfig::default(),
                &arena,
            )
            .unwrap();

            assert_eq!(
                artifacts.abi,
                Abi {
                    inputs: vec![AbiInput {
                        name: "f".into(),
                        public: true,
                        ty: ConcreteType::Struct(ConcreteStructType::new(
                            "foo".into(),
                            "Foo".into(),
                            vec![],
                            vec![ConcreteStructMember {
                                id: "b".into(),
                                ty: Box::new(ConcreteType::Struct(ConcreteStructType::new(
                                    "bar".into(),
                                    "Bar".into(),
                                    vec![],
                                    vec![ConcreteStructMember::new(
                                        "a".into(),
                                        ConcreteType::FieldElement
                                    )]
                                )))
                            }]
                        ))
                    }],
                    output: ConcreteType::Tuple(GTupleType::new(vec![]))
                }
            );
        }
    }
}
