//! Module containing the complete compilation pipeline.
//!
//! @file compile.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018
use crate::absy::{Module, ModuleId, Program};
use crate::flatten::Flattener;
use crate::imports::{self, Importer};
use crate::ir;
use crate::macros;
use crate::parser::Position;
use crate::semantics::{self, Checker};
use crate::static_analysis;
use crate::static_analysis::Analyse;
use crate::typed_absy::abi::Abi;
use crate::zir::ZirProgram;
use macros::process_macros;
use std::collections::HashMap;
use std::fmt;
use std::io;
use std::path::Path;
use std::path::PathBuf;
use typed_arena::Arena;
use zokrates_common::Resolver;
use zokrates_field::Field;
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

#[derive(Debug, PartialEq)]
pub struct CompileError {
    pub module: PathBuf,
    pub position: Option<(Position, Position)>,
    pub message: String,
}

impl CompileError {
    pub fn in_module(module: PathBuf, message: String) -> Self {
        Self {
            module,
            message,
            position: None,
        }
    }

    pub fn pos(mut self, pos: (Position, Position)) -> Self {
        self.position = Some(pos);
        self
    }

    pub fn message(&self) -> &str {
        &self.message
    }

    pub fn module(&self) -> &Path {
        &self.module
    }
}

impl From<CompileError> for CompileErrors {
    fn from(e: CompileError) -> Self {
        CompileErrors(vec![e])
    }
}

#[derive(Debug, PartialEq)]
pub struct CompileErrors(pub Vec<CompileError>);

impl CompileErrors {
    pub fn len(&self) -> usize {
        self.0.len()
    }
}

type FilePath = PathBuf;

pub fn compile<T: Field, E: ToString>(
    source: String,
    location: FilePath,
    resolver: Option<&dyn Resolver<E>>,
) -> Result<CompilationArtifacts<T>, CompileErrors> {
    let arena = Arena::new();

    let (typed_ast, abi) = check_with_arena(source, location, resolver, &arena)?;

    // flatten input program
    let program_flattened = Flattener::flatten(typed_ast);

    // analyse (constant propagation after call resolution)
    let program_flattened = program_flattened.analyse();

    // convert to ir
    let ir_prog = ir::Prog::from(program_flattened);

    // optimize
    let optimized_ir_prog = ir_prog.optimize();

    // analyse (check for unused constraints)
    let optimized_ir_prog = optimized_ir_prog.analyse();

    Ok(CompilationArtifacts {
        prog: optimized_ir_prog,
        abi,
    })
}

pub fn check<T: Field, E: ToString>(
    source: String,
    location: FilePath,
    resolver: Option<&dyn Resolver<E>>,
) -> Result<(), CompileErrors> {
    let arena = Arena::new();

    check_with_arena::<T, _>(source, location, resolver, &arena).map(|_| ())
}

fn check_with_arena<'ast, T: Field, E: ToString>(
    source: String,
    location: FilePath,
    resolver: Option<&dyn Resolver<E>>,
    arena: &'ast Arena<String>,
) -> Result<(ZirProgram<'ast, T>, Abi), CompileErrors> {
    let source = arena.alloc(source);
    let compiled = compile_program::<T, E>(source, location, resolver, &arena)?;

    // check semantics
    let typed_ast = Checker::check(compiled)?;

    let main_module = typed_ast.main.clone();

    // analyse (unroll and constant propagation)
    typed_ast.analyse().map_err(|e| CompileErrors(vec![e]))
}

pub fn compile_program<'ast, T: Field, E: ToString>(
    source: &'ast str,
    location: FilePath,
    resolver: Option<&dyn Resolver<E>>,
    arena: &'ast Arena<String>,
) -> Result<Program<'ast>, CompileErrors> {
    let mut modules = HashMap::new();

    let main = compile_module::<T, E>(&source, location.clone(), resolver, &mut modules, &arena)?;

    modules.insert(location.clone(), main);

    Ok(Program {
        main: location,
        modules,
    })
}

pub fn compile_module<'ast, T: Field, E: ToString>(
    source: &'ast str,
    location: FilePath,
    resolver: Option<&dyn Resolver<E>>,
    modules: &mut HashMap<ModuleId, Module<'ast>>,
    arena: &'ast Arena<String>,
) -> Result<Module<'ast>, CompileErrors> {
    let ast = pest::generate_ast(&source).map_err(|e| CompileError {
        module: location.clone(),
        message: e.to_string(),
        position: None,
    })?;

    let ast = process_macros::<T>(ast)?;

    let module_without_imports: Module = Module::from(ast);

    Importer::apply_imports::<T, E>(
        module_without_imports,
        location.clone(),
        resolver,
        modules,
        &arena,
    )
}

#[cfg(test)]
mod test {
    use super::*;
    use zokrates_field::Bn128Field;

    #[test]
    fn no_resolver_with_imports() {
        let source = r#"
			import "./path/to/file" as foo
			def main() -> field:
			   return foo()
		"#
        .to_string();
        let res: Result<CompilationArtifacts<Bn128Field>, CompileErrors> = compile(
            source,
            "./path/to/file".into(),
            None::<&dyn Resolver<io::Error>>,
        );
        assert!(res.unwrap_err().0[0]
            .message()
            .to_string()
            .contains(&"Can't resolve import without a resolver"));
    }

    #[test]
    fn no_resolver_without_imports() {
        let source = r#"
			def main() -> field:
			   return 1
		"#
        .to_string();
        let res: Result<CompilationArtifacts<Bn128Field>, CompileErrors> = compile(
            source,
            "./path/to/file".into(),
            None::<&dyn Resolver<io::Error>>,
        );
        assert!(res.is_ok());
    }

    mod abi {
        use super::*;
        use crate::typed_absy::abi::*;
        use crate::typed_absy::types::*;

        #[test]
        fn use_struct_declaration_types() {
            // when importing types and renaming them, we use the canonical struct names in the ABI

            // // main.zok
            // from foo import Foo as FooMain
            //
            // // foo.zok
            // from bar import Bar as BarFoo
            // struct Foo { BarFoo b }
            //
            // // bar.zok
            // struct Bar { field a }

            // Expected resolved type for FooMain:
            // Foo { Bar b }

            let main = r#"
from "foo" import Foo as FooMain
def main(FooMain f):
    return
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
from "foo" import Foo as FooMain
def main(FooMain f):
    return
"#
                            .into(),
                            "main".into(),
                        ))
                    } else if loc == "foo" {
                        Ok((
                            r#"
from "bar" import Bar as BarFoo
struct Foo {
    BarFoo b
}
"#
                            .into(),
                            "foo".into(),
                        ))
                    } else if loc == "bar" {
                        Ok((
                            r#"
struct Bar { field a }
"#
                            .into(),
                            "bar".into(),
                        ))
                    } else {
                        unreachable!()
                    }
                }
            }

            let artifacts = compile::<Bn128Field, io::Error>(
                main.to_string(),
                "main".into(),
                Some(&CustomResolver),
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
                            vec![ConcreteStructMember {
                                id: "b".into(),
                                ty: box ConcreteType::Struct(ConcreteStructType::new(
                                    "bar".into(),
                                    "Bar".into(),
                                    vec![ConcreteStructMember {
                                        id: "a".into(),
                                        ty: box ConcreteType::FieldElement
                                    }]
                                ))
                            }]
                        ))
                    }],
                    outputs: vec![]
                }
            );
        }
    }
}
