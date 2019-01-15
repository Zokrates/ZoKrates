//! Module containing structs and enums to represent imports.
//!
//! @file imports.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use absy::*;
use compile::compile_aux;
use compile::CompileError;
use flat_absy::*;
use std::fmt;
use std::io;
use std::io::BufRead;
use zokrates_field::field::Field;

pub struct CompiledImport<T: Field> {
    pub flat_func: FlatFunction<T>,
}

impl<T: Field> CompiledImport<T> {
    fn new(prog: FlatProg<T>, alias: String) -> CompiledImport<T> {
        match prog.functions.iter().find(|fun| fun.id == "main") {
            Some(fun) => CompiledImport {
                flat_func: FlatFunction {
                    id: alias,
                    ..fun.clone()
                },
            },
            None => panic!("no main"),
        }
    }
}

#[derive(PartialEq, Debug)]
pub struct Error {
    message: String,
}

impl Error {
    pub fn new<T: Into<String>>(message: T) -> Error {
        Error {
            message: message.into(),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl From<io::Error> for Error {
    fn from(error: io::Error) -> Self {
        Error {
            message: format!("I/O Error: {:?}", error),
        }
    }
}

#[derive(PartialEq, Clone, Serialize, Deserialize)]
pub struct Import {
    source: String,
    alias: Option<String>,
}

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

    pub fn apply_imports<T: Field, S: BufRead, E: Into<Error>>(
        &self,
        destination: Prog<T>,
        location: Option<String>,
        resolve_option: Option<fn(&Option<String>, &String) -> Result<(S, String, String), E>>,
    ) -> Result<Prog<T>, CompileError<T>> {
        let mut origins: Vec<CompiledImport<T>> = vec![];

        for import in destination.imports.iter() {
            // handle the case of special libsnark and packing imports
            if import.source.starts_with("LIBSNARK") {
                #[cfg(feature = "libsnark")]
                {
                    use helpers::LibsnarkGadgetHelper;
                    use libsnark::get_sha256round_constraints;
                    use serde_json::from_str;
                    use standard::{DirectiveR1CS, R1CS};
                    use std::io::BufReader;

                    match import.source.as_ref() {
                        "LIBSNARK/sha256round" => {
                            let r1cs: R1CS = from_str(&get_sha256round_constraints()).unwrap();
                            let dr1cs: DirectiveR1CS = DirectiveR1CS {
                                r1cs,
                                directive: LibsnarkGadgetHelper::Sha256Round,
                            };
                            let compiled = FlatProg::from(dr1cs);
                            let alias = match import.alias {
                                Some(ref alias) => alias.clone(),
                                None => String::from("sha256round"),
                            };
                            origins.push(CompiledImport::new(compiled, alias));
                        }
                        s => {
                            return Err(CompileError::ImportError(Error::new(format!(
                                "Gadget {} not found",
                                s
                            ))));
                        }
                    }
                }
            } else if import.source.starts_with("PACKING") {
                use types::conversions::{pack, unpack};

                match import.source.as_ref() {
                    "PACKING/pack128" => {
                        let compiled = pack(128);
                        let alias = match import.alias {
                            Some(ref alias) => alias.clone(),
                            None => String::from("pack128"),
                        };
                        origins.push(CompiledImport::new(compiled, alias));
                    }
                    "PACKING/unpack128" => {
                        let compiled = unpack(128);
                        let alias = match import.alias {
                            Some(ref alias) => alias.clone(),
                            None => String::from("unpack128"),
                        };
                        origins.push(CompiledImport::new(compiled, alias));
                    }
                    s => {
                        return Err(CompileError::ImportError(Error::new(format!(
                            "Packing helper {} not found",
                            s
                        ))));
                    }
                }
            } else {
                // to resolve imports, we need a resolver
                match resolve_option {
                    Some(resolve) => match resolve(&location, &import.source) {
                        Ok((mut reader, location, auto_alias)) => {
                            let compiled =
                                compile_aux(&mut reader, Some(location), resolve_option)?;
                            let alias = match import.alias {
                                Some(ref alias) => alias.clone(),
                                None => auto_alias,
                            };
                            origins.push(CompiledImport::new(compiled, alias));
                        }
                        Err(err) => return Err(CompileError::ImportError(err.into())),
                    },
                    None => {
                        return Err(Error::new("Can't resolve import without a resolver").into());
                    }
                }
            }
        }

        Ok(Prog {
            imports: vec![],
            functions: destination.clone().functions,
            imported_functions: origins.into_iter().map(|o| o.flat_func).collect(),
        })
    }
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
