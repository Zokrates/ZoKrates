//! Module containing structs and enums to represent imports.
//!
//! @file imports.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use crate::absy::*;
use crate::compile::compile_module;
use crate::compile::{CompileErrorInner, CompileErrors};
use crate::embed::FlatEmbed;
use crate::parser::Position;
use std::collections::HashMap;
use std::fmt;
use std::io;
use std::path::PathBuf;

use typed_arena::Arena;
use zokrates_common::Resolver;
use zokrates_field::{Bn128Field, Field};

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
            .unwrap_or_else(|| "?".to_string());
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

pub struct Importer;

impl Importer {
    pub fn apply_imports<'ast, T: Field, E: Into<Error>>(
        destination: Module<'ast>,
        location: PathBuf,
        resolver: Option<&dyn Resolver<E>>,
        modules: &mut HashMap<OwnedModuleId, Module<'ast>>,
        arena: &'ast Arena<String>,
    ) -> Result<Module<'ast>, CompileErrors> {
        let mut symbols: Vec<_> = vec![];

        for symbol in destination.symbols {
            match symbol.value.symbol {
                Symbol::Here(ref s) => match s {
                    SymbolDefinition::Import(ImportDirective::Main(main)) => {
                        let pos = main.pos();
                        let module_id = &main.value.source;

                        match resolver {
                            Some(res) => {
                                match res.resolve(location.clone(), module_id.to_path_buf()) {
                                    Ok((source, new_location)) => {
                                        // generate an alias from the imported path if none was given explicitly
                                        let alias = main.value.alias.or(
                                            module_id
                                                .file_stem()
                                                .ok_or_else(|| {
                                                    CompileErrors::from(
                                                        CompileErrorInner::ImportError(Error::new(
                                                            format!(
                                                                "Could not determine alias for import {}",
                                                                module_id.display()
                                                            ),
                                                        ))
                                                            .in_file(&location),
                                                    )
                                                })?
                                                .to_str()
                                        );

                                        match modules.get(&new_location) {
                                            Some(_) => {}
                                            None => {
                                                let source = arena.alloc(source);

                                                let compiled = compile_module::<T, E>(
                                                    source,
                                                    new_location.clone(),
                                                    resolver,
                                                    modules,
                                                    &arena,
                                                )?;

                                                assert!(modules
                                                    .insert(new_location.clone(), compiled)
                                                    .is_none());
                                            }
                                        };

                                        symbols.push(
                                            SymbolDeclaration {
                                                id: alias,
                                                symbol: Symbol::There(
                                                    SymbolImport::with_id_in_module(
                                                        "main",
                                                        new_location,
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
                                        .in_file(&location)
                                        .into());
                                    }
                                }
                            }
                            None => {
                                return Err(CompileErrorInner::from(Error::new(
                                    "Cannot resolve import without a resolver",
                                ))
                                .in_file(&location)
                                .into());
                            }
                        }
                    }
                    SymbolDefinition::Import(ImportDirective::From(from)) => {
                        let pos = from.pos();
                        let module_id = &from.value.source;

                        match module_id.to_str().unwrap() {
                            "EMBED" => {
                                for symbol in &from.value.symbols {
                                    match symbol.id {
                                        #[cfg(feature = "bellman")]
                                        "sha256round" => {
                                            if T::id() != Bn128Field::id() {
                                                return Err(CompileErrorInner::ImportError(
                                                    Error::new(format!(
                                                        "Embed sha256round cannot be used with curve {}",
                                                        T::name()
                                                    ))
                                                        .with_pos(Some(pos)),
                                                ).in_file(&location).into());
                                            } else {
                                                symbols.push(
                                                    SymbolDeclaration {
                                                        id: Some(symbol.get_alias()),
                                                        symbol: Symbol::Flat(
                                                            FlatEmbed::Sha256Round,
                                                        ),
                                                    }
                                                    .start_end(pos.0, pos.1),
                                                )
                                            }
                                        }
                                        "unpack" => symbols.push(
                                            SymbolDeclaration {
                                                id: Some(symbol.get_alias()),
                                                symbol: Symbol::Flat(FlatEmbed::Unpack),
                                            }
                                            .start_end(pos.0, pos.1),
                                        ),
                                        "u64_to_bits" => symbols.push(
                                            SymbolDeclaration {
                                                id: Some(symbol.get_alias()),
                                                symbol: Symbol::Flat(FlatEmbed::U64ToBits),
                                            }
                                            .start_end(pos.0, pos.1),
                                        ),
                                        "u32_to_bits" => symbols.push(
                                            SymbolDeclaration {
                                                id: Some(symbol.get_alias()),
                                                symbol: Symbol::Flat(FlatEmbed::U32ToBits),
                                            }
                                            .start_end(pos.0, pos.1),
                                        ),
                                        "u16_to_bits" => symbols.push(
                                            SymbolDeclaration {
                                                id: Some(symbol.get_alias()),
                                                symbol: Symbol::Flat(FlatEmbed::U16ToBits),
                                            }
                                            .start_end(pos.0, pos.1),
                                        ),
                                        "u8_to_bits" => symbols.push(
                                            SymbolDeclaration {
                                                id: Some(symbol.get_alias()),
                                                symbol: Symbol::Flat(FlatEmbed::U8ToBits),
                                            }
                                            .start_end(pos.0, pos.1),
                                        ),
                                        "u64_from_bits" => symbols.push(
                                            SymbolDeclaration {
                                                id: Some(symbol.get_alias()),
                                                symbol: Symbol::Flat(FlatEmbed::U64FromBits),
                                            }
                                            .start_end(pos.0, pos.1),
                                        ),
                                        "u32_from_bits" => symbols.push(
                                            SymbolDeclaration {
                                                id: Some(symbol.get_alias()),
                                                symbol: Symbol::Flat(FlatEmbed::U32FromBits),
                                            }
                                            .start_end(pos.0, pos.1),
                                        ),
                                        "u16_from_bits" => symbols.push(
                                            SymbolDeclaration {
                                                id: Some(symbol.get_alias()),
                                                symbol: Symbol::Flat(FlatEmbed::U16FromBits),
                                            }
                                            .start_end(pos.0, pos.1),
                                        ),
                                        "u8_from_bits" => symbols.push(
                                            SymbolDeclaration {
                                                id: Some(symbol.get_alias()),
                                                symbol: Symbol::Flat(FlatEmbed::U8FromBits),
                                            }
                                            .start_end(pos.0, pos.1),
                                        ),
                                        s => {
                                            return Err(CompileErrorInner::ImportError(
                                                Error::new(format!("Embed {} not found", s))
                                                    .with_pos(Some(pos)),
                                            )
                                            .in_file(&location)
                                            .into())
                                        }
                                    }
                                }
                            }
                            _ => {
                                for symbol in &from.value.symbols {
                                    match resolver {
                                        Some(res) => {
                                            match res
                                                .resolve(location.clone(), module_id.to_path_buf())
                                            {
                                                Ok((source, new_location)) => {
                                                    match modules.get(&new_location) {
                                                        Some(_) => {}
                                                        None => {
                                                            let source = arena.alloc(source);

                                                            let compiled = compile_module::<T, E>(
                                                                source,
                                                                new_location.clone(),
                                                                resolver,
                                                                modules,
                                                                &arena,
                                                            )?;

                                                            assert!(modules
                                                                .insert(
                                                                    new_location.clone(),
                                                                    compiled
                                                                )
                                                                .is_none());
                                                        }
                                                    };

                                                    symbols.push(
                                                        SymbolDeclaration {
                                                            id: Some(symbol.get_alias()),
                                                            symbol: Symbol::There(
                                                                SymbolImport::with_id_in_module(
                                                                    symbol.id,
                                                                    new_location,
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
                                                    .in_file(&location)
                                                    .into());
                                                }
                                            }
                                        }
                                        None => {
                                            return Err(CompileErrorInner::from(Error::new(
                                                "Cannot resolve import without a resolver",
                                            ))
                                            .in_file(&location)
                                            .into());
                                        }
                                    }
                                }
                            }
                        }
                    }
                    _ => symbols.push(symbol),
                },
                _ => unreachable!(),
            }
        }

        Ok(Module::with_symbols(symbols))
    }
}
