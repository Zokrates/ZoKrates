use zokrates_field::field::Field;

use std::io::prelude::*;

use parser::error::Error;
use parser::tokenize::{next_token, Position, Token};

use super::function::parse_function;
use super::import::parse_import;

use absy::Prog;

pub fn parse_program<T: Field, R: BufRead>(reader: &mut R) -> Result<Prog<T>, Error<T>> {
    let mut current_line = 1;
    let mut lines = reader.lines();
    let mut functions = Vec::new();
    let mut imports = Vec::new();

    loop {
        match lines.next() {
            Some(Ok(ref x)) if x.trim().starts_with("//") || x.trim() == "" => current_line += 1,
            Some(Ok(ref x)) => match next_token(
                x,
                &Position {
                    line: current_line,
                    col: 1,
                },
            ) {
                (Token::Import, ref s1, ref p1) => match parse_import(s1, p1) {
                    Ok((import, p2)) => {
                        imports.push(import);
                        current_line = p2.line; // this is the line of the import statement
                        current_line += 1;
                    }
                    Err(err) => return Err(err),
                },
                (Token::Def, ref s1, ref p1) => match parse_function(&mut lines, s1, p1) {
                    Ok((function, p2)) => {
                        functions.push(function);
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
            },
            None => break,
            Some(Err(err)) => panic!("Error while reading function definitions: {}", err),
        }
    }

    Ok(Prog {
        functions,
        imports,
        imported_functions: vec![],
    })
}
