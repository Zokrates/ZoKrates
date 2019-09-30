//! Module containing structs and enums to represent imports.
//!
//! @file imports.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use crate::absy::*;
use crate::compile::compile_module;
use crate::compile::{CompileErrorInner, CompileErrors, Resolve};
use crate::embed::FlatEmbed;
use crate::parser::Position;
use std::collections::HashMap;
use std::fmt;
use std::io;

use typed_arena::Arena;
use zokrates_field::field::Field;

#[derive(PartialEq, Debug)]
pub struct Error {
    pos: Option<(Position, Position)>,
    message: String,
}

impl Error {
    pub fn new<T: Into<String>>(message: T) -> Error {
        Error {
            pos: None,
            message: message.into(),
        }
    }

    fn with_pos(self, pos: Option<(Position, Position)>) -> Error {
        Error { pos, ..self }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let location = self
            .pos
            .map(|p| format!("{}", p.0))
            .unwrap_or("?".to_string());
        write!(f, "{}\n\t{}", location, self.message)
    }
}

impl From<io::Error> for Error {
    fn from(error: io::Error) -> Self {
        Error {
            pos: None,
            message: format!("I/O Error: {}", error),
        }
    }
}

#[derive(PartialEq, Clone)]
pub struct Import<'ast> {
    source: Identifier<'ast>,
    alias: Option<Identifier<'ast>>,
}

pub type ImportNode<'ast> = Node<Import<'ast>>;

impl<'ast> Import<'ast> {
    pub fn new(source: Identifier<'ast>) -> Import<'ast> {
        Import {
            source: source,
            alias: None,
        }
    }

    pub fn get_alias(&self) -> &Option<Identifier<'ast>> {
        &self.alias
    }

    pub fn new_with_alias(source: Identifier<'ast>, alias: Identifier<'ast>) -> Import<'ast> {
        Import {
            source: source,
            alias: Some(alias),
        }
    }

    pub fn alias(mut self, alias: Option<Identifier<'ast>>) -> Self {
        self.alias = alias;
        self
    }

    pub fn get_source(&self) -> &Identifier<'ast> {
        &self.source
    }
}

impl<'ast> fmt::Display for Import<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.alias {
            Some(ref alias) => write!(f, "import {} as {}", self.source, alias),
            None => write!(f, "import {}", self.source),
        }
    }
}

impl<'ast> fmt::Debug for Import<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.alias {
            Some(ref alias) => write!(f, "import(source: {}, alias: {})", self.source, alias),
            None => write!(f, "import(source: {})", self.source),
        }
    }
}

pub struct Importer {}

impl Importer {
    pub fn new() -> Importer {
        Importer {}
    }

    pub fn apply_imports<'ast, T: Field, E: Into<Error>>(
        &self,
        destination: Module<'ast, T>,
        location: String,
        resolve_option: Option<Resolve<E>>,
        modules: &mut HashMap<ModuleId, Module<'ast, T>>,
        arena: &'ast Arena<String>,
    ) -> Result<Module<'ast, T>, CompileErrors> {
        let mut functions: Vec<_> = vec![];

        for import in destination.imports {
            let pos = import.pos();
            let import = import.value;
            let alias = import.alias;
            // handle the case of special bellman and packing imports
            if import.source.starts_with("EMBED") {
                match import.source.as_ref() {
                    "EMBED/sha256round" => {
                        let alias = alias.unwrap_or("sha256round");

                        functions.push(
                            FunctionDeclaration {
                                id: &alias,
                                symbol: FunctionSymbol::Flat(FlatEmbed::Sha256Round),
                            }
                            .start_end(pos.0, pos.1),
                        );
                    }
                    "EMBED/unpack" => {
                        let alias = alias.unwrap_or("unpack");

                        functions.push(
                            FunctionDeclaration {
                                id: &alias,
                                symbol: FunctionSymbol::Flat(FlatEmbed::Unpack),
                            }
                            .start_end(pos.0, pos.1),
                        );
                    }
                    s => {
                        return Err(CompileErrorInner::ImportError(
                            Error::new(format!("Embed {} not found. Options are \"EMBED/sha256round\", \"EMBED/unpack\"", s)).with_pos(Some(pos)),
                        )
                        .with_context(&location)
                        .into());
                    }
                }
            } else {
                // to resolve imports, we need a resolver
                match resolve_option {
                    Some(resolve) => match resolve(location.clone(), import.source.to_string()) {
                        Ok((source, location)) => {
                            let source = arena.alloc(source);
                            let alias = import.alias.unwrap_or_else(|| {
                                std::path::Path::new(import.source)
                                    .file_stem()
                                    .unwrap()
                                    .to_str()
                                    .unwrap()
                            });

                            let compiled =
                                compile_module(source, location, resolve_option, modules, &arena)
                                    .map_err(|e| e.with_context(import.source.to_string()))?;

                            modules.insert(import.source.to_string(), compiled);

                            functions.push(
                                FunctionDeclaration {
                                    id: &alias,
                                    symbol: FunctionSymbol::There(
                                        FunctionImport::with_id_in_module(
                                            "main",
                                            import.source.clone(),
                                        )
                                        .start_end(pos.0, pos.1),
                                    ),
                                }
                                .start_end(pos.0, pos.1),
                            );
                        }
                        Err(err) => {
                            return Err(CompileErrorInner::ImportError(
                                err.into().with_pos(Some(pos)),
                            )
                            .with_context(&location)
                            .into());
                        }
                    },
                    None => {
                        return Err(CompileErrorInner::from(Error::new(
                            "Can't resolve import without a resolver",
                        ))
                        .with_context(&location)
                        .into());
                    }
                }
            }
        }

        functions.extend(destination.functions);

        Ok(Module {
            imports: vec![],
            functions: functions,
        })
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn create_with_no_alias() {
        assert_eq!(
            Import::new("./foo/bar/baz.zok"),
            Import {
                source: "./foo/bar/baz.zok",
                alias: None,
            }
        );
    }

    #[test]
    fn create_with_alias() {
        assert_eq!(
            Import::new_with_alias("./foo/bar/baz.zok", &"myalias"),
            Import {
                source: "./foo/bar/baz.zok",
                alias: Some("myalias"),
            }
        );
    }
}
