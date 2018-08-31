use field::Field;

use std::io::prelude::*;
use std::io::Lines;

use parser::tokenize::{next_token, Position, Token};
use parser::Error;

use super::statement::parse_statement;

use absy::{Function, Parameter, Statement, Variable};
use types::{Signature, Type};

pub fn parse_function<T: Field, R: BufRead>(
    mut lines: &mut Lines<R>,
    input: &String,
    pos: &Position,
) -> Result<(Function<T>, Position), Error<T>> {
    let mut current_line = pos.line;
    let id;
    let mut args = Vec::new();

    // parse function signature
    match next_token(input, pos) {
        (Token::Ide(x2), s2, p2) => {
            id = x2;
            match next_token(&s2, &p2) {
                (Token::Open, s3, p3) => {
                    let mut s = s3;
                    let mut p = p3;
                    loop {
                        match next_token(&s, &p) {
                            (Token::Private, s4, p4) => match next_token(&s4, &p4) {
                                (Token::Ide(x), s5, p5) => {
                                    args.push(Parameter {
                                        id: Variable::from(x),
                                        private: true,
                                    });
                                    match next_token(&s5, &p5) {
                                        (Token::Comma, s6, p6) => {
                                            s = s6;
                                            p = p6;
                                        }
                                        (Token::Close, s5, p5) => match next_token(&s5, &p5) {
                                            (Token::Colon, s6, p6) => match next_token(&s6, &p6) {
                                                (Token::InlineComment(_), _, _) => break,
                                                (Token::Unknown(ref x6), ..) if x6 == "" => break,
                                                (t6, _, p6) => {
                                                    return Err(Error {
                                                        expected: vec![Token::Unknown(
                                                            "".to_string(),
                                                        )],
                                                        got: t6,
                                                        pos: p6,
                                                    })
                                                }
                                            },
                                            (t6, _, p6) => {
                                                return Err(Error {
                                                    expected: vec![Token::Colon],
                                                    got: t6,
                                                    pos: p6,
                                                })
                                            }
                                        },
                                        (t5, _, p5) => {
                                            return Err(Error {
                                                expected: vec![Token::Comma, Token::Close],
                                                got: t5,
                                                pos: p5,
                                            })
                                        }
                                    }
                                }
                                (t5, _, p5) => {
                                    return Err(Error {
                                        expected: vec![Token::Comma, Token::Close],
                                        got: t5,
                                        pos: p5,
                                    })
                                }
                            },
                            (Token::Ide(x), s4, p4) => {
                                args.push(Parameter {
                                    id: Variable::from(x),
                                    private: false,
                                });
                                match next_token(&s4, &p4) {
                                    (Token::Comma, s5, p5) => {
                                        s = s5;
                                        p = p5;
                                    }
                                    (Token::Close, s4, p4) => match next_token(&s4, &p4) {
                                        (Token::Colon, s5, p5) => match next_token(&s5, &p5) {
                                            (Token::InlineComment(_), _, _) => break,
                                            (Token::Unknown(ref x6), ..) if x6 == "" => break,
                                            (t6, _, p6) => {
                                                return Err(Error {
                                                    expected: vec![Token::Unknown("".to_string())],
                                                    got: t6,
                                                    pos: p6,
                                                })
                                            }
                                        },
                                        (t5, _, p5) => {
                                            return Err(Error {
                                                expected: vec![Token::Colon],
                                                got: t5,
                                                pos: p5,
                                            })
                                        }
                                    },
                                    (t5, _, p5) => {
                                        return Err(Error {
                                            expected: vec![Token::Comma, Token::Close],
                                            got: t5,
                                            pos: p5,
                                        })
                                    }
                                }
                            }
                            (Token::Close, s4, p4) => {
                                // case of no parameters
                                match next_token(&s4, &p4) {
                                    (Token::Colon, s5, p5) => match next_token(&s5, &p5) {
                                        (Token::InlineComment(_), _, _) => break,
                                        (Token::Unknown(ref x6), ..) if x6 == "" => break,
                                        (t6, _, p6) => {
                                            return Err(Error {
                                                expected: vec![Token::Unknown("".to_string())],
                                                got: t6,
                                                pos: p6,
                                            })
                                        }
                                    },
                                    (t5, _, p5) => {
                                        return Err(Error {
                                            expected: vec![Token::Colon],
                                            got: t5,
                                            pos: p5,
                                        })
                                    }
                                }
                            }
                            (t4, _, p4) => {
                                return Err(Error {
                                    expected: vec![Token::Ide(String::from("ide")), Token::Close],
                                    got: t4,
                                    pos: p4,
                                })
                            }
                        }
                    }
                }
                (t3, _, p3) => {
                    return Err(Error {
                        expected: vec![Token::Open],
                        got: t3,
                        pos: p3,
                    })
                }
            }
        }
        (t2, _, p2) => {
            return Err(Error {
                expected: vec![Token::Ide(String::from("name"))],
                got: t2,
                pos: p2,
            })
        }
    }
    current_line += 1;

    // parse function body
    let mut stats = Vec::new();
    let return_count;
    loop {
        match lines.next() {
            Some(Ok(ref x)) if x.trim().starts_with("//") || x.trim() == "" => {} // skip
            Some(Ok(ref x)) => match parse_statement(
                &mut lines,
                x,
                &Position {
                    line: current_line,
                    col: 1,
                },
            ) {
                Ok((Statement::Return(list), ..)) => {
                    return_count = list.expressions.len();
                    stats.push(Statement::Return(list));
                    break;
                }
                Ok((statement, _, pos)) => {
                    stats.push(statement);
                    current_line = pos.line // update the interal line counter to continue where statement ended.
                }
                Err(err) => return Err(err),
            },
            None => panic!("Function {} does not return before program ends", id),
            Some(Err(err)) => panic!("Error while reading function statements: {}", err),
        }
        current_line += 1;
    }

    match stats.last() {
        Some(&Statement::Return(_)) => {}
        Some(x) => panic!("Last function statement not Return: {}", x),
        None => panic!("Error while checking last function statement"),
    }

    let input_count = args.len();

    Ok((
        Function {
            id: id,
            arguments: args,
            statements: stats,
            signature: Signature {
                inputs: vec![Type::FieldElement; input_count],
                outputs: vec![Type::FieldElement; return_count],
            },
        },
        Position {
            line: current_line,
            col: 1,
        },
    ))
}
