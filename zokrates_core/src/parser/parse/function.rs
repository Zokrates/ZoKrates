use zokrates_field::field::Field;

use std::io::prelude::*;
use std::io::Lines;

use parser::tokenize::{next_token, Position, Token};
use parser::Error;

use super::statement::parse_statement;

use absy::{
    Function, FunctionNode, Node, Parameter, ParameterNode, Statement, Variable, VariableNode,
};
use types::{Signature, Type};

fn parse_function_identifier<T: Field>(
    input: &String,
    pos: &Position,
) -> Result<(String, String, Position), Error<T>> {
    match next_token::<T>(&input, &pos) {
        (Token::Ide(x), s, p) => Ok((x, s, p)),
        (t, _, p) => Err(Error {
            expected: vec![Token::Ide(String::from("name"))],
            got: t,
            pos: p,
        }),
    }
}

fn parse_function_header<T: Field>(
    input: &String,
    pos: &Position,
) -> Result<(String, Vec<ParameterNode>, Signature), Error<T>> {
    // parse function identifier
    let (id, s, p) = parse_function_identifier(input, pos)?;

    // parse function arguments, enclosed by parentheses
    let (args, s, p) = match next_token(&s, &p) {
        (Token::Open, s1, p1) => match parse_function_arguments(s1, p1) {
            Ok((args, s2, p2)) => match next_token::<T>(&s2, &p2) {
                (Token::Close, s3, p3) => Ok((args, s3, p3)),
                (t3, _, p3) => {
                    return Err(Error {
                        expected: vec![Token::Close],
                        got: t3,
                        pos: p3,
                    });
                }
            },
            Err(e) => return Err(e),
        },
        (t1, _, p1) => {
            return Err(Error {
                expected: vec![Token::Open],
                got: t1,
                pos: p1,
            });
        }
    }?;

    // parse function return types, enclosed by parentheses
    let (return_types, s, p) = match next_token(&s, &p) {
        (Token::Arrow, s0, p0) => match next_token(&s0, &p0) {
            (Token::Open, s1, p1) => match parse_function_return_types(s1, p1) {
                Ok((types, s2, p2)) => match next_token::<T>(&s2, &p2) {
                    (Token::Close, s3, p3) => Ok((types, s3, p3)),
                    (t3, _, p3) => {
                        return Err(Error {
                            expected: vec![Token::Close],
                            got: t3,
                            pos: p3,
                        });
                    }
                },
                Err(e) => return Err(e),
            },
            (t1, _, p1) => {
                return Err(Error {
                    expected: vec![Token::Open],
                    got: t1,
                    pos: p1,
                });
            }
        },
        (t0, _, p0) => {
            return Err(Error {
                expected: vec![Token::Arrow],
                got: t0,
                pos: p0,
            });
        }
    }?;

    let sig = Signature {
        inputs: args.iter().map(|a| a.value.id.value.get_type()).collect(),
        outputs: return_types,
    };

    match next_token(&s, &p) {
        (Token::Colon, s5, p5) => match next_token(&s5, &p5) {
            (Token::InlineComment(_), _, _) => return Ok((id, args, sig)),
            (Token::Unknown(ref x6), ..) if x6 == "" => return Ok((id, args, sig)),
            (t6, _, p6) => {
                return Err(Error {
                    expected: vec![Token::Unknown("".to_string())],
                    got: t6,
                    pos: p6,
                });
            }
        },
        (t5, _, p5) => {
            return Err(Error {
                expected: vec![Token::Colon],
                got: t5,
                pos: p5,
            });
        }
    }
}

fn parse_function_argument_variable<T: Field>(
    input: &String,
    pos: &Position,
) -> Result<(VariableNode, String, Position), Error<T>> {
    let s4 = input;
    let p4 = pos;

    match next_token::<T>(&s4, &p4) {
        (Token::Type(t), s5, p5) => match next_token(&s5, &p5) {
            (Token::Ide(x), s6, p6) => Ok((Node::new(*pos, p6, Variable::new(x, t)), s6, p6)),
            (t6, _, p6) => Err(Error {
                expected: vec![Token::Ide(String::from("identifier"))],
                got: t6,
                pos: p6,
            }),
        },
        (t5, _, p5) => Err(Error {
            expected: vec![Token::Type(Type::FieldElement)],
            got: t5,
            pos: p5,
        }),
    }
}

fn parse_function_arguments<T: Field>(
    input: String,
    pos: Position,
) -> Result<(Vec<ParameterNode>, String, Position), Error<T>> {
    let mut args = Vec::new();
    let mut s = input;
    let mut p = pos;

    loop {
        match next_token(&s, &p) {
            (Token::Private, s1, p1) => {
                let (var, s2, p2) = parse_function_argument_variable::<T>(&s1, &p1)?;
                args.push(Node::new(p, p1, Parameter::private(var)));
                match next_token::<T>(&s2, &p2) {
                    (Token::Comma, s3, p3) => {
                        s = s3;
                        p = p3;
                    }
                    (Token::Close, _, _) => return Ok((args, s2, p2)),
                    (t3, _, p3) => {
                        return Err(Error {
                            expected: vec![Token::Comma, Token::Close],
                            got: t3,
                            pos: p3,
                        });
                    }
                }
            }
            (Token::Type(_), _, _) => {
                let (var, s2, p2) = parse_function_argument_variable::<T>(&s, &p)?;
                args.push(Node::new(p, p2, Parameter::public(var)));
                match next_token::<T>(&s2, &p2) {
                    (Token::Comma, s3, p3) => {
                        s = s3;
                        p = p3;
                    }
                    (Token::Close, _, _) => return Ok((args, s2, p2)),
                    (t3, _, p3) => {
                        return Err(Error {
                            expected: vec![Token::Comma, Token::Close],
                            got: t3,
                            pos: p3,
                        });
                    }
                }
            }
            (Token::Close, _, _) => return Ok((vec![], s, p)),
            (t4, _, p4) => {
                return Err(Error {
                    expected: vec![
                        Token::Type(Type::FieldElement),
                        Token::Private,
                        Token::Close,
                    ],
                    got: t4,
                    pos: p4,
                });
            }
        }
    }
}

fn parse_function_return_types<T: Field>(
    input: String,
    pos: Position,
) -> Result<(Vec<Type>, String, Position), Error<T>> {
    let mut types = Vec::new();
    let mut s = input;
    let mut p = pos;

    loop {
        match next_token(&s, &p) {
            (Token::Type(t), s1, p1) => {
                types.push(t);
                match next_token::<T>(&s1, &p1) {
                    (Token::Comma, s3, p3) => {
                        s = s3;
                        p = p3;
                    }
                    (Token::Close, _, _) => return Ok((types, s1, p1)),
                    (t3, _, p3) => {
                        return Err(Error {
                            expected: vec![Token::Comma, Token::Close],
                            got: t3,
                            pos: p3,
                        });
                    }
                }
            }
            (Token::Close, _, _) => return Ok((vec![], s, p)),
            (t4, _, p4) => {
                return Err(Error {
                    expected: vec![
                        Token::Type(Type::FieldElement),
                        Token::Private,
                        Token::Close,
                    ],
                    got: t4,
                    pos: p4,
                });
            }
        }
    }
}

pub fn parse_function<T: Field, R: BufRead>(
    mut lines: &mut Lines<R>,
    input: &String,
    pos: &Position,
) -> Result<(FunctionNode<T>, Position), Error<T>> {
    let mut current_line = pos.line;

    let (id, args, sig) = parse_function_header(input, pos)?;

    current_line += 1;

    // parse function body
    let mut stats = Vec::new();
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
                Ok((ref statements, _, ref pos)) => {
                    for stat in statements {
                        stats.push(stat.clone());
                    }
                    match statements[0].value {
                        Statement::Return(_) => {
                            break;
                        }
                        _ => {
                            current_line = pos.line // update the interal line counter to continue where statement ended.
                        }
                    }
                }
                Err(err) => return Err(err),
            },
            None => panic!("Function {} does not return before program ends", id),
            Some(Err(err)) => panic!("Error while reading function statements: {}", err),
        }
        current_line += 1;
    }

    match stats.last().clone().unwrap().value {
        Statement::Return(_) => {}
        ref x => panic!("Last function statement not Return: {}", x),
    }

    let next_pos = Position {
        line: current_line,
        col: 1,
    };

    Ok((
        Node::new(
            *pos,
            next_pos,
            Function {
                id: id,
                arguments: args,
                statements: stats,
                signature: sig,
            },
        ),
        next_pos,
    ))
}
