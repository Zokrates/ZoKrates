//! Module containing structs and enums to represent imports.
//!
//! @file imports.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use crate::absy::*;
use crate::compile::compile_module;
use crate::compile::{CompileErrorInner, CompileErrors};
use crate::parser::Position;
use std::collections::HashMap;
use std::fmt;
use std::io;
use std::io::BufRead;
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

#[derive(PartialEq, Clone, Serialize, Deserialize)]
pub struct Import {
    source: String,
    alias: Option<String>,
}

pub type ImportNode = Node<Import>;

impl Import {
    pub fn new(source: String) -> Import {
        Import {
            source: source,
            alias: None,
        }
    }

    pub fn get_alias(&self) -> &Option<String> {
        &self.alias
    }

    pub fn new_with_alias(source: String, alias: &String) -> Import {
        Import {
            source: source,
            alias: Some(alias.clone()),
        }
    }

    pub fn alias(mut self, alias: Option<String>) -> Self {
        self.alias = alias;
        self
    }

    pub fn get_source(&self) -> &String {
        &self.source
    }
}

impl fmt::Display for Import {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.alias {
            Some(ref alias) => write!(f, "import {} as {}", self.source, alias),
            None => write!(f, "import {}", self.source),
        }
    }
}

impl fmt::Debug for Import {
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

    // Inject dependencies declared for `destination`
    // The lifetime of the Program before injection outlives the lifetime after
    pub fn apply_imports<'before, 'after, T: Field, S: BufRead, E: Into<Error>>(
        &self,
        destination: Module<'before, T>,
        location: Option<String>,
        resolve_option: Option<fn(&Option<String>, &String) -> Result<(S, String, String), E>>,
        modules: &mut HashMap<ModuleId, Module<T>>,
    ) -> Result<Module<'after, T>, CompileErrors>
    where
        'before: 'after,
    {
        unimplemented!()
    }
    // {
    //     let mut functions: Vec<_> = vec![];

    //     for import in destination.imports {
    //         let pos = import.pos();
    //         let import = import.value;
    //         // handle the case of special bellman and packing imports
    //         if import.source.starts_with("BELLMAN") {
    //             match import.source.as_ref() {
    //                 "BELLMAN/sha256round" => {
    //                     use crate::standard::sha_round;

    //                     let compiled = sha_round();

    //                     let alias = match import.alias {
    //                         Some(alias) => {
    //                             if alias == "sha256" {
    //                                 alias.clone()
    //                             } else {
    //                                 return Err(CompileErrorInner::from(Error::new(format!(
    //                                     "Aliasing gadgets is not supported, found alias {}",
    //                                     alias
    //                                 )))
    //                                 .with_context(&location)
    //                                 .into());
    //                             }
    //                         }
    //                         None => String::from("sha256"),
    //                     };

    //                     functions.push(
    //                         FunctionDeclaration {
    //                             id: &alias,
    //                             symbol: FunctionSymbol::Flat(compiled),
    //                         }
    //                         .start_end(pos.0, pos.1),
    //                     );
    //                 }
    //                 s => {
    //                     return Err(CompileErrorInner::ImportError(
    //                         Error::new(format!("Gadget {} not found", s)).with_pos(Some(pos)),
    //                     )
    //                     .with_context(&location)
    //                     .into());
    //                 }
    //             }
    //         } else if import.source.starts_with("PACKING") {
    //             use crate::types::conversions::split;

    //             match import.source.as_ref() {
    //                 "PACKING/split" => {
    //                     let compiled = split();
    //                     let alias = match import.alias {
    //                         Some(alias) => {
    //                             if alias == "split" {
    //                                 alias.clone()
    //                             } else {
    //                                 return Err(CompileErrorInner::from(Error::new(format!(
    //                                     "Aliasing gadgets is not supported, found alias {}",
    //                                     alias
    //                                 )))
    //                                 .with_context(&location)
    //                                 .into());
    //                             }
    //                         }
    //                         None => String::from("split"),
    //                     };

    //                     functions.push(
    //                         FunctionDeclaration {
    //                             id: &alias,
    //                             symbol: FunctionSymbol::Flat(compiled),
    //                         }
    //                         .start_end(pos.0, pos.1),
    //                     );
    //                 }
    //                 s => {
    //                     return Err(CompileErrorInner::ImportError(
    //                         Error::new(format!("Packing helper {} not found", s))
    //                             .with_pos(Some(pos)),
    //                     )
    //                     .with_context(&location)
    //                     .into());
    //                 }
    //             }
    //         } else {
    //             // to resolve imports, we need a resolver
    //             match resolve_option {
    //                 Some(resolve) => match resolve(&location, &import.source) {
    //                     Ok((mut reader, location, auto_alias)) => {

    //                         let mut source = String::new();
    //                         reader.read_to_string(&mut source).unwrap();

    //                         let compiled = compile_module(
    //                             &source,
    //                             Some(location),
    //                             resolve_option,
    //                             modules,
    //                         )
    //                         .map_err(|e| e.with_context(Some(import.source.clone())))?;
    //                         let alias = import.alias.clone().unwrap_or(auto_alias);

    //                         modules.insert(import.source.clone(), compiled);

    //                         functions.push(
    //                             FunctionDeclaration {
    //                                 id: &alias,
    //                                 symbol: FunctionSymbol::There(
    //                                     FunctionImport::with_id_in_module(
    //                                         "main",
    //                                         import.source.clone(),
    //                                     )
    //                                     .start_end(pos.0, pos.1),
    //                                 ),
    //                             }
    //                             .start_end(pos.0, pos.1),
    //                         );
    //                     }
    //                     Err(err) => {
    //                         return Err(CompileErrorInner::ImportError(
    //                             err.into().with_pos(Some(pos)),
    //                         )
    //                         .with_context(&location)
    //                         .into());
    //                     }
    //                 },
    //                 None => {
    //                     return Err(CompileErrorInner::from(Error::new(
    //                         "Can't resolve import without a resolver",
    //                     ))
    //                     .with_context(&location)
    //                     .into());
    //                 }
    //             }
    //         }
    //     }

    //     functions.extend(destination.functions);

    //     Ok(Module {
    //         imports: vec![],
    //         functions: functions,
    //     })
    // }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn create_with_no_alias() {
        assert_eq!(
            Import::new("./foo/bar/baz.code".to_string()),
            Import {
                source: String::from("./foo/bar/baz.code"),
                alias: None,
            }
        );
    }

    #[test]
    fn create_with_alias() {
        assert_eq!(
            Import::new_with_alias("./foo/bar/baz.code".to_string(), &"myalias".to_string()),
            Import {
                source: String::from("./foo/bar/baz.code"),
                alias: Some("myalias".to_string()),
            }
        );
    }
}
