use zokrates_field::field::Field;

use std::io::prelude::*;

use crate::parser::error::Error;
use crate::parser::tokenize::{next_token, Position, Token};

use super::function::parse_function;
use super::import::parse_import;

use crate::absy::{FunctionDeclaration, FunctionSymbol, Module, Node};

pub fn parse_module<T: Field, R: BufRead>(reader: &mut R) -> Result<Module<T>, Error<T>> {
    let mut current_line = 1;
    let mut lines = reader.lines();
    let mut functions = Vec::new();
    let mut imports = Vec::new();

    loop {
        match lines.next() {
            Some(Ok(ref x)) if x.trim().starts_with("//") || x.trim() == "" => current_line += 1,
            Some(Ok(ref x)) => {
                let p0 = Position {
                    line: current_line,
                    col: 1,
                };
                match next_token(x, &p0) {
                    (Token::Import, ref s1, ref p1) => match parse_import(s1, p1) {
                        Ok((import, p2)) => {
                            imports.push(import);
                            current_line = p2.line; // this is the line of the import statement
                            current_line += 1;
                        }
                        Err(err) => return Err(err),
                    },
                    (Token::Def, ref s1, ref p1) => match parse_function(&mut lines, s1, p1) {
                        Ok((identifier, function, p2)) => {
                            functions.push(Node::new(
                                p0,
                                p2,
                                FunctionDeclaration {
                                    id: identifier,
                                    symbol: FunctionSymbol::Here(function),
                                },
                            ));
                            current_line = p2.line; // this is the line of the return statement
                            current_line += 1;
                        }
                        Err(err) => return Err(err),
                    },
                    (t1, _, p1) => {
                        return Err(Error {
                            expected: vec![Token::Def],
                            got: t1,
                            pos: p1,
                        });
                    }
                }
            }
            None => break,
            Some(Err(err)) => panic!("Error while reading function definitions: {}", err),
        }
    }

    Ok(Module {
        functions: functions,
        imports,
    })
}
