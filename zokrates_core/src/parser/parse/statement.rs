use zokrates_field::field::Field;

use std::io::prelude::*;
use std::io::Lines;

use parser::tokenize::{next_token, Position, Token};
use parser::Error;

use parser::tokenize::skip_whitespaces;

use super::expression::{
    parse_array_select, parse_expr, parse_expr1, parse_function_call, parse_term1,
};
use super::expression_list::parse_expression_list;

use absy::{
    Assignee, AssigneeNode, Expression, Node, Statement, StatementNode, Variable, VariableNode,
};
use types::Type;

pub fn parse_statement<T: Field, R: BufRead>(
    lines: &mut Lines<R>,
    input: &String,
    pos: &Position,
) -> Result<(Vec<StatementNode<T>>, String, Position), Error<T>> {
    match next_token::<T>(input, pos) {
        (Token::Type(t), s1, p1) => parse_declaration_definition(t, s1, p1),
        (Token::Ide(x1), s1, p1) => parse_statement1(x1, s1, p1),
        (Token::If, ..) | (Token::Open, ..) | (Token::Num(_), ..) => match parse_expr(input, pos) {
            Ok((e2, s2, p2)) => match next_token(&s2, &p2) {
                (Token::Eqeq, s3, p3) => match parse_expr(&s3, &p3) {
                    Ok((e4, s4, p4)) => match next_token(&s4, &p4) {
                        (Token::InlineComment(_), ref s5, _) => {
                            assert_eq!(s5, "");
                            Ok((
                                vec![Node::new(*pos, p4, Statement::Condition(e2, e4))],
                                s4,
                                p4,
                            ))
                        }
                        (Token::Unknown(ref t5), ref s5, _) if t5 == "" => {
                            assert_eq!(s5, "");
                            Ok((
                                vec![Node::new(*pos, p4, Statement::Condition(e2, e4))],
                                s4,
                                p4,
                            ))
                        }
                        (t5, _, p5) => Err(Error {
                            expected: vec![Token::Unknown("".to_string())],
                            got: t5,
                            pos: p5,
                        }),
                    },
                    Err(err) => Err(err),
                },
                (t3, _, p3) => Err(Error {
                    expected: vec![Token::Eqeq],
                    got: t3,
                    pos: p3,
                }),
            },
            Err(err) => Err(err),
        },
        (Token::For, s1, p1) => {
            match next_token(&s1, &p1) {
                (Token::Type(t), s0, p0) => {
                    match next_token(&s0, &p0) {
                        (Token::Ide(x2), s2, p2) => {
                            match next_token(&s2, &p2) {
                                (Token::In, s3, p3) => {
                                    match next_token(&s3, &p3) {
                                        (Token::Num(x4), s4, p4) => {
                                            match next_token(&s4, &p4) {
                                                (Token::Dotdot, s5, p5) => {
                                                    match next_token(&s5, &p5) {
                                                        (Token::Num(x6), s6, p6) => {
                                                            match next_token(&s6, &p6) {
                                                                (Token::Do, s7, p7) => {
                                                                    match next_token(&s7, &p7) {
                                                                        (
                                                                            Token::InlineComment(_),
                                                                            ref s8,
                                                                            _,
                                                                        ) => {
                                                                            assert_eq!(s8, "");
                                                                        }
                                                                        (
                                                                            Token::Unknown(ref t8),
                                                                            ref s8,
                                                                            _,
                                                                        )
                                                                            if t8 == "" =>
                                                                        {
                                                                            assert_eq!(s8, "");
                                                                        }
                                                                        (t8, _, p8) => {
                                                                            return Err(Error {
                                                                                expected: vec![
                                                                                    Token::Unknown(
                                                                                        "".to_string(),
                                                                                    ),
                                                                                ],
                                                                                got: t8,
                                                                                pos: p8,
                                                                            })
                                                                        }
                                                                    }
                                                                    let mut current_line = p7.line;
                                                                    let mut statements = Vec::new();
                                                                    loop {
                                                                        current_line += 1;
                                                                        match lines.next() {
                                                    Some(Ok(ref x)) if x.trim().starts_with("//") || x.trim() == "" => {}, // skip
                                                    Some(Ok(ref x)) if x.trim().starts_with("endfor") => {
                                                        let offset = skip_whitespaces(x);
                                                        let s8 = x[offset + 6..].to_string();
                                                        let p8 = Position{ line: current_line, col: offset + 7 };
                                                        match next_token(&s8, &p8) {
                                                            (Token::InlineComment(_), ref s9, _) => {
                                                                assert_eq!(s9, "");
                                                                return Ok((vec![Node::new(*pos, p8, Statement::For(Node::new(p1, p3, Variable::new(x2, t)), x4, x6, statements))], s8, p8))
                                                            }
                                                            (Token::Unknown(ref t9), ref s9, _) if t9 == "" => {
                                                                assert_eq!(s9, "");
                                                                return Ok((vec![Node::new(*pos, p8, Statement::For(Node::new(p1, p3, Variable::new(x2, t)), x4, x6, statements))], s8, p8))
                                                            },
                                                            (t9, _, p9) => return Err(Error { expected: vec![Token::Unknown("".to_string())], got: t9 , pos: p9 }),
                                                        }
                                                    },
                                                    Some(Ok(ref x)) if !x.trim().starts_with("return") => match parse_statement(lines, x, &Position { line: current_line, col: 1 }) {
                                                        Ok((mut statement, ..)) => statements.append(&mut statement),
                                                        Err(err) => return Err(err),
                                                    },
                                                    Some(Err(err)) => panic!("Error while reading Definitions: {}", err),
                                                    Some(Ok(ref x)) => {
                                                        let (t, ..) = next_token(x, &Position{ line: current_line, col: 1 });
                                                        return Err(Error { expected: vec![Token::ErrIde, Token::ErrNum, Token::If, Token::Open, Token::Hash, Token::For, Token::Endfor], got: t , pos:  Position{ line: current_line, col: 1 } })
                                                    },
                                                    None => return Err(Error { expected: vec![Token::ErrIde, Token::ErrNum, Token::If, Token::Open, Token::Hash, Token::For], got: Token::Unknown("".to_string()) , pos:  Position{ line: current_line, col: 1 } }),
                                                }
                                                                    }
                                                                }
                                                                (t7, _, p7) => Err(Error {
                                                                    expected: vec![Token::Do],
                                                                    got: t7,
                                                                    pos: p7,
                                                                }),
                                                            }
                                                        }
                                                        (t6, _, p6) => Err(Error {
                                                            expected: vec![Token::ErrNum],
                                                            got: t6,
                                                            pos: p6,
                                                        }),
                                                    }
                                                }
                                                (t5, _, p5) => Err(Error {
                                                    expected: vec![Token::Dotdot],
                                                    got: t5,
                                                    pos: p5,
                                                }),
                                            }
                                        }
                                        (t4, _, p4) => Err(Error {
                                            expected: vec![Token::ErrNum],
                                            got: t4,
                                            pos: p4,
                                        }),
                                    }
                                }
                                (t3, _, p3) => Err(Error {
                                    expected: vec![Token::In],
                                    got: t3,
                                    pos: p3,
                                }),
                            }
                        }
                        (t2, _, p2) => Err(Error {
                            expected: vec![Token::ErrIde],
                            got: t2,
                            pos: p2,
                        }),
                    }
                }
                (t0, _, p0) => Err(Error {
                    expected: vec![Token::Type(Type::FieldElement)],
                    got: t0,
                    pos: p0,
                }),
            }
        }
        (Token::Return, s1, p1) => match parse_expression_list(s1, p1) {
            Ok((e2, s2, p2)) => match next_token(&s2, &p2) {
                (Token::InlineComment(_), ref s3, _) => {
                    assert_eq!(s3, "");
                    Ok((vec![Node::new(*pos, p2, Statement::Return(e2))], s2, p2))
                }
                (Token::Unknown(ref t3), ref s3, _) if t3 == "" => {
                    assert_eq!(s3, "");
                    Ok((vec![Node::new(*pos, p2, Statement::Return(e2))], s2, p2))
                }
                (t3, _, p3) => Err(Error {
                    expected: vec![Token::Unknown("".to_string())],
                    got: t3,
                    pos: p3,
                }),
            },
            Err(err) => Err(err),
        },
        (Token::Def, _, p1) => Err(Error {
            expected: vec![Token::Return],
            got: Token::Def,
            pos: p1,
        }), // This just covers an error case: Def Token is never part of a valid statement and indicates that a return statement is missing.
        (t1, _, p1) => Err(Error {
            expected: vec![
                Token::ErrIde,
                Token::ErrNum,
                Token::If,
                Token::Open,
                Token::Return,
            ],
            got: t1,
            pos: p1,
        }),
    }
}

fn parse_definition1<T: Field>(
    x: AssigneeNode<T>,
    input: String,
    pos: Position,
) -> Result<(Vec<StatementNode<T>>, String, Position), Error<T>> {
    match parse_expr(&input, &pos) {
        Ok((e1, s1, p1)) => match next_token(&s1, &p1) {
            (Token::InlineComment(_), ref s2, _) => {
                assert_eq!(s2, "");
                match e1.value {
                    e @ Expression::FunctionCall(..) => Ok((
                        vec![Node::new(
                            x.start,
                            p1,
                            Statement::MultipleDefinition(vec![x], Node::new(pos, p1, e)),
                        )],
                        s1,
                        p1,
                    )),
                    e => Ok((
                        vec![Node::new(
                            x.start,
                            p1,
                            Statement::Definition(x, Node::new(pos, p1, e)),
                        )],
                        s1,
                        p1,
                    )),
                }
            }
            (Token::Unknown(ref t2), ref s2, _) if t2 == "" => {
                assert_eq!(s2, "");
                match e1.value {
                    e @ Expression::FunctionCall(..) => Ok((
                        vec![Node::new(
                            x.start,
                            p1,
                            Statement::MultipleDefinition(vec![x], Node::new(pos, p1, e)),
                        )],
                        s1,
                        p1,
                    )),
                    e => Ok((
                        vec![Node::new(
                            x.start,
                            p1,
                            Statement::Definition(x, Node::new(pos, p1, e)),
                        )],
                        s1,
                        p1,
                    )),
                }
            }
            (t2, _, p2) => Err(Error {
                expected: vec![Token::Unknown("".to_string())],
                got: t2,
                pos: p2,
            }),
        },
        Err(err) => Err(err),
    }
}

fn parse_declaration_definition<T: Field>(
    t: Type,
    input: String,
    pos: Position,
) -> Result<(Vec<StatementNode<T>>, String, Position), Error<T>> {
    match next_token::<T>(&input, &pos) {
        (Token::Ide(x), s0, p0) => match next_token(&s0, &p0) {
            (Token::Eq, s1, p1) => match parse_expr(&s1, &p1) {
                Ok((e2, s2, p2)) => match next_token(&s2, &p2) {
                    (Token::InlineComment(_), ref s3, _) => {
                        assert_eq!(s3, "");
                        match e2.value {
                            e @ Expression::FunctionCall(..) => Ok((
                                vec![
                                    Node::new(
                                        pos,
                                        p0,
                                        Statement::Declaration(Node::new(
                                            pos,
                                            p0,
                                            Variable::new(x.clone(), t),
                                        )),
                                    ),
                                    Node::new(
                                        pos,
                                        p2,
                                        Statement::MultipleDefinition(
                                            vec![Node::new(pos, p1, Assignee::Identifier(x))],
                                            Node::new(p1, p2, e),
                                        ),
                                    ),
                                ],
                                s2,
                                p2,
                            )),
                            e => Ok((
                                vec![
                                    Node::new(
                                        pos,
                                        p0,
                                        Statement::Declaration(Node::new(
                                            pos,
                                            p0,
                                            Variable::new(x.clone(), t),
                                        )),
                                    ),
                                    Node::new(
                                        pos,
                                        p2,
                                        Statement::Definition(
                                            Node::new(pos, p1, Assignee::Identifier(x)),
                                            Node::new(p1, p2, e),
                                        ),
                                    ),
                                ],
                                s2,
                                p2,
                            )),
                        }
                    }
                    (Token::Unknown(ref t3), ref s3, _) if t3 == "" => {
                        assert_eq!(s3, "");
                        match e2.value {
                            e @ Expression::FunctionCall(..) => Ok((
                                vec![
                                    Node::new(
                                        pos,
                                        p0,
                                        Statement::Declaration(Node::new(
                                            pos,
                                            p0,
                                            Variable::new(x.clone(), t),
                                        )),
                                    ),
                                    Node::new(
                                        pos,
                                        p2,
                                        Statement::MultipleDefinition(
                                            vec![Node::new(pos, p1, Assignee::Identifier(x))],
                                            Node::new(p1, p2, e),
                                        ),
                                    ),
                                ],
                                s2,
                                p2,
                            )),
                            e => Ok((
                                vec![
                                    Node::new(
                                        pos,
                                        p0,
                                        Statement::Declaration(Node::new(
                                            pos,
                                            p0,
                                            Variable::new(x.clone(), t),
                                        )),
                                    ),
                                    Node::new(
                                        pos,
                                        p2,
                                        Statement::Definition(
                                            Node::new(pos, p1, Assignee::Identifier(x)),
                                            Node::new(p1, p2, e),
                                        ),
                                    ),
                                ],
                                s2,
                                p2,
                            )),
                        }
                    }
                    (t3, _, p3) => Err(Error {
                        expected: vec![
                            Token::Add,
                            Token::Sub,
                            Token::Pow,
                            Token::Mult,
                            Token::Div,
                            Token::Unknown("".to_string()),
                        ],
                        got: t3,
                        pos: p3,
                    }),
                },
                Err(err) => Err(err),
            },
            (Token::Comma, s1, p1) => match parse_identifier_list1(x, Some(t.clone()), s1, p1) {
                // if we find a comma, parse the rest of the destructure
                Ok((e2, d2, s2, p2)) => match next_token(&s2, &p2) {
                    // then we should have an equal sign
                    (Token::Eq, s3, p3) => match parse_expr(&s3, &p3) {
                        Ok((e4, s4, p4)) => {
                            let mut statements: Vec<_> = d2
                                .iter()
                                .map(|v| {
                                    Node::new(v.start, v.end, Statement::Declaration(v.clone()))
                                })
                                .collect();
                            statements.push(Node::new(
                                pos,
                                p4,
                                Statement::MultipleDefinition(e2, e4),
                            ));
                            Ok((statements, s4, p4)) // output a multipledefinition with the destructure and the expression
                        }
                        Err(err) => Err(err),
                    },
                    (t3, _, p3) => Err(Error {
                        expected: vec![Token::Eq],
                        got: t3,
                        pos: p3,
                    }),
                },
                Err(err) => Err(err),
            },
            (t1, _, p1) => Err(Error {
                expected: vec![Token::Eq, Token::Unknown("".to_string())],
                got: t1,
                pos: p1,
            }),
        },
        (t0, _, p0) => Err(Error {
            expected: vec![Token::Ide(String::from("identifier"))],
            got: t0,
            pos: p0,
        }),
    }
}

// parse statement that starts with an identifier
fn parse_statement1<T: Field>(
    ide: String,
    input: String,
    pos: Position,
) -> Result<(Vec<StatementNode<T>>, String, Position), Error<T>> {
    let ide_start_position = Position {
        col: pos.col - ide.len(),
        ..pos
    };
    match next_token::<T>(&input, &pos) {
        (Token::Eq, s1, p1) => parse_definition1(
            Node::new(ide_start_position, pos, Assignee::Identifier(ide)),
            s1,
            p1,
        ),
        (Token::Comma, s1, p1) => match parse_identifier_list1(ide, None, s1, p1) {
            // if we find a comma, parse the rest of the destructure
            Ok((e2, d2, s2, p2)) => match next_token(&s2, &p2) {
                // then we should have an equal sign
                (Token::Eq, s3, p3) => match parse_expr(&s3, &p3) {
                    Ok((e4, s4, p4)) => {
                        let mut statements: Vec<_> = d2
                            .iter()
                            .map(|v| Node::new(v.start, v.end, Statement::Declaration(v.clone())))
                            .collect();
                        statements.push(Node::new(pos, p4, Statement::MultipleDefinition(e2, e4)));
                        Ok((statements, s4, p4)) // output a multipledefinition with the destructure and the expression
                    }
                    Err(err) => Err(err),
                },
                (t3, _, p3) => Err(Error {
                    expected: vec![Token::Eq],
                    got: t3,
                    pos: p3,
                }),
            },
            Err(err) => Err(err),
        },
        (Token::Open, s1, p1) => match parse_function_call(ide, s1, p1) {
            Ok((e3, s3, p3)) => match parse_expr1(e3, s3, p3) {
                Ok((e4, s4, p4)) => match next_token(&s4, &p4) {
                    (Token::Eqeq, s5, p5) => match parse_expr(&s5, &p5) {
                        Ok((e6, s6, p6)) => match next_token(&s6, &p6) {
                            (Token::InlineComment(_), ref s7, _) => {
                                assert_eq!(s7, "");
                                Ok((
                                    vec![Node::new(pos, p6, Statement::Condition(e4, e6))],
                                    s6,
                                    p6,
                                ))
                            }
                            (Token::Unknown(ref t7), ref s7, _) if t7 == "" => {
                                assert_eq!(s7, "");
                                Ok((
                                    vec![Node::new(pos, p6, Statement::Condition(e4, e6))],
                                    s6,
                                    p6,
                                ))
                            }
                            (t7, _, p7) => Err(Error {
                                expected: vec![
                                    Token::Add,
                                    Token::Sub,
                                    Token::Pow,
                                    Token::Mult,
                                    Token::Div,
                                    Token::Unknown("".to_string()),
                                ],
                                got: t7,
                                pos: p7,
                            }),
                        },
                        Err(err) => Err(err),
                    },
                    (t4, _, p4) => Err(Error {
                        expected: vec![Token::Eqeq],
                        got: t4,
                        pos: p4,
                    }),
                },
                Err(err) => Err(err),
            },
            Err(err) => Err(err),
        },
        (Token::LeftBracket, s1, p1) => match parse_array_select(ide, s1, p1) {
            Ok((e3, s3, p3)) => match parse_expr1(e3, s3, p3) {
                Ok((e4, s4, p4)) => match next_token(&s4, &p4) {
                    (Token::Eqeq, s5, p5) => match parse_expr(&s5, &p5) {
                        Ok((e6, s6, p6)) => match next_token(&s6, &p6) {
                            (Token::InlineComment(_), ref s7, _) => {
                                assert_eq!(s7, "");
                                Ok((
                                    vec![Node::new(pos, p6, Statement::Condition(e4, e6))],
                                    s6,
                                    p6,
                                ))
                            }
                            (Token::Unknown(ref t7), ref s7, _) if t7 == "" => {
                                assert_eq!(s7, "");
                                Ok((
                                    vec![Node::new(pos, p6, Statement::Condition(e4, e6))],
                                    s6,
                                    p6,
                                ))
                            }
                            (t7, _, p7) => Err(Error {
                                expected: vec![
                                    Token::Add,
                                    Token::Sub,
                                    Token::Pow,
                                    Token::Mult,
                                    Token::Div,
                                    Token::Unknown("".to_string()),
                                ],
                                got: t7,
                                pos: p7,
                            }),
                        },
                        Err(err) => Err(err),
                    },
                    (Token::Eq, s5, p5) => parse_definition1(AssigneeNode::from(e4), s5, p5),
                    (t4, _, p4) => Err(Error {
                        expected: vec![Token::Eqeq],
                        got: t4,
                        pos: p4,
                    }),
                },
                Err(err) => Err(err),
            },
            Err(err) => Err(err),
        },
        _ => match parse_term1(
            Node::new(ide_start_position, pos, Expression::Identifier(ide)),
            input,
            pos,
        ) {
            Ok((e2, s2, p2)) => match parse_expr1(e2, s2, p2) {
                Ok((e3, s3, p3)) => match next_token(&s3, &p3) {
                    (Token::Eqeq, s4, p4) => match parse_expr(&s4, &p4) {
                        Ok((e5, s5, p5)) => match next_token(&s5, &p5) {
                            (Token::InlineComment(_), ref s6, _) => {
                                assert_eq!(s6, "");
                                Ok((
                                    vec![Node::new(pos, p5, Statement::Condition(e3, e5))],
                                    s5,
                                    p5,
                                ))
                            }
                            (Token::Unknown(ref t6), ref s6, _) if t6 == "" => {
                                assert_eq!(s6, "");
                                Ok((
                                    vec![Node::new(pos, p5, Statement::Condition(e3, e5))],
                                    s5,
                                    p5,
                                ))
                            }
                            (t6, _, p6) => Err(Error {
                                expected: vec![
                                    Token::Add,
                                    Token::Sub,
                                    Token::Pow,
                                    Token::Mult,
                                    Token::Div,
                                    Token::Unknown("".to_string()),
                                ],
                                got: t6,
                                pos: p6,
                            }),
                        },
                        Err(err) => Err(err),
                    },
                    (t4, _, p4) => Err(Error {
                        expected: vec![Token::Eqeq],
                        got: t4,
                        pos: p4,
                    }),
                },
                Err(err) => Err(err),
            },
            Err(err) => Err(err),
        },
    }
}

// parse an expression list starting with an identifier
pub fn parse_identifier_list1<T: Field>(
    head: String,
    _type: Option<Type>,
    input: String,
    pos: Position,
) -> Result<(Vec<AssigneeNode<T>>, Vec<VariableNode>, String, Position), Error<T>> {
    let mut res = Vec::new();
    let mut decl = Vec::new();

    let start_pos = Position {
        col: pos.col - head.len(),
        ..pos
    };

    res.push(Node::new(
        start_pos,
        pos,
        Assignee::Identifier(head.clone()),
    ));
    match _type {
        Some(t) => {
            decl.push(Node::new(start_pos, pos, Variable::new(head, t)));
        }
        _ => {}
    };
    parse_comma_separated_identifier_list_rec(input, pos, &mut res, &mut decl)
}

fn parse_comma_separated_identifier_list_rec<T: Field>(
    input: String,
    pos: Position,
    mut acc: &mut Vec<AssigneeNode<T>>,
    mut decl: &mut Vec<VariableNode>,
) -> Result<(Vec<AssigneeNode<T>>, Vec<VariableNode>, String, Position), Error<T>> {
    match next_token(&input, &pos) {
        (Token::Type(t), s1, p1) => match next_token::<T>(&s1, &p1) {
            (Token::Ide(id), s2, p2) => {
                acc.push(Node::new(p1, p2, Assignee::Identifier(id.clone())));
                decl.push(Node::new(pos, p2, Variable::new(id, t)));
                match next_token::<T>(&s2, &p2) {
                    (Token::Comma, s3, p3) => {
                        parse_comma_separated_identifier_list_rec(s3, p3, &mut acc, &mut decl)
                    }
                    (..) => Ok((acc.to_vec(), decl.to_vec(), s2, p2)),
                }
            }
            (t2, _, p2) => Err(Error {
                expected: vec![Token::Ide(String::from("ide"))],
                got: t2,
                pos: p2,
            }),
        },
        (Token::Ide(id), s1, p1) => {
            acc.push(Node::new(pos, p1, Assignee::Identifier(id)));
            match next_token::<T>(&s1, &p1) {
                (Token::Comma, s2, p2) => {
                    parse_comma_separated_identifier_list_rec(s2, p2, &mut acc, &mut decl)
                }
                (..) => Ok((acc.to_vec(), decl.to_vec(), s1, p1)),
            }
        }
        (t1, _, p1) => Err(Error {
            expected: vec![Token::Ide(String::from("ide"))],
            got: t1,
            pos: p1,
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    mod parse_statement1 {
        use super::*;
        #[test]
        fn left_call_in_assertion() {
            let pos = Position { line: 45, col: 121 };
            let string = String::from("() == 1");
            let cond = Statement::Condition(
                Expression::FunctionCall(String::from("foo"), vec![]).into(),
                Expression::Number(FieldPrime::from(1)).into(),
            )
            .into();
            assert_eq!(
                Ok((vec![cond], String::from(""), pos.col(string.len() as isize))),
                parse_statement1(String::from("foo"), string, pos)
            );
        }

        #[test]
        fn left_call_in_assertion2() {
            let pos = Position { line: 45, col: 121 };
            let string = String::from("() - g() - 1 == 1");
            let cond = Statement::Condition(
                Expression::Sub(
                    box Expression::Sub(
                        box Expression::FunctionCall(String::from("foo"), vec![]).into(),
                        box Expression::FunctionCall(String::from("g"), vec![]).into(),
                    )
                    .into(),
                    box Expression::Number(FieldPrime::from(1)).into(),
                )
                .into(),
                Expression::Number(FieldPrime::from(1)).into(),
            )
            .into();
            assert_eq!(
                Ok((vec![cond], String::from(""), pos.col(string.len() as isize))),
                parse_statement1(String::from("foo"), string, pos)
            );
        }

        #[test]
        fn left_select_in_assertion2() {
            let pos = Position { line: 45, col: 121 };
            let string = String::from("[3] - g() - 1 == 1");
            let cond = Statement::Condition(
                Expression::Sub(
                    box Expression::Sub(
                        box Expression::Select(
                            box Expression::Identifier(String::from("foo")).into(),
                            box Expression::Number(FieldPrime::from(3)).into(),
                        )
                        .into(),
                        box Expression::FunctionCall(String::from("g"), vec![]).into(),
                    )
                    .into(),
                    box Expression::Number(FieldPrime::from(1)).into(),
                )
                .into(),
                Expression::Number(FieldPrime::from(1)).into(),
            )
            .into();
            assert_eq!(
                Ok((vec![cond], String::from(""), pos.col(string.len() as isize))),
                parse_statement1(String::from("foo"), string, pos)
            );
        }
    }
}
