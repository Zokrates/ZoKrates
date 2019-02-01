use zokrates_field::field::Field;

use parser::tokenize::{next_token, Position, Token};
use parser::Error;

use absy::{Expression, ExpressionNode, Node};

fn parse_then_else<T: Field>(
    cond: ExpressionNode<T>,
    input: &String,
    pos: &Position,
) -> Result<(ExpressionNode<T>, String, Position), Error<T>> {
    match next_token(input, pos) {
        (Token::Then, s5, p5) => match parse_expr(&s5, &p5) {
            Ok((e6, s6, p6)) => match next_token(&s6, &p6) {
                (Token::Else, s7, p7) => match parse_expr(&s7, &p7) {
                    Ok((e8, s8, p8)) => match next_token(&s8, &p8) {
                        (Token::Fi, s9, p9) => parse_expr1(
                            Node::new(cond.start, p9, Expression::IfElse(box cond, box e6, box e8)),
                            s9,
                            p9,
                        ),
                        (t10, _, p10) => Err(Error {
                            expected: vec![Token::Fi],
                            got: t10,
                            pos: p10,
                        }),
                    },
                    Err(err) => Err(err),
                },
                (t7, _, p7) => Err(Error {
                    expected: vec![Token::Else],
                    got: t7,
                    pos: p7,
                }),
            },
            Err(err) => Err(err),
        },
        (t5, _, p5) => Err(Error {
            expected: vec![Token::Then],
            got: t5,
            pos: p5,
        }),
    }
}

fn parse_prim_cond<T: Field>(
    input: &String,
    pos: &Position,
) -> Result<(ExpressionNode<T>, String, Position), Error<T>> {
    match parse_expr(input, pos) {
        Ok((e2, s2, p2)) => match next_token(&s2, &p2) {
            (Token::Lt, s3, p3) => match parse_expr(&s3, &p3) {
                Ok((e4, s4, p4)) => {
                    Ok((Node::new(*pos, p4, Expression::Lt(box e2, box e4)), s4, p4))
                }
                Err(err) => Err(err),
            },
            (Token::Le, s3, p3) => match parse_expr(&s3, &p3) {
                Ok((e4, s4, p4)) => {
                    Ok((Node::new(*pos, p4, Expression::Le(box e2, box e4)), s4, p4))
                }
                Err(err) => Err(err),
            },
            (Token::Eqeq, s3, p3) => match parse_expr(&s3, &p3) {
                Ok((e4, s4, p4)) => {
                    Ok((Node::new(*pos, p4, Expression::Eq(box e2, box e4)), s4, p4))
                }
                Err(err) => Err(err),
            },
            (Token::Ge, s3, p3) => match parse_expr(&s3, &p3) {
                Ok((e4, s4, p4)) => {
                    Ok((Node::new(*pos, p4, Expression::Ge(box e2, box e4)), s4, p4))
                }
                Err(err) => Err(err),
            },
            (Token::Gt, s3, p3) => match parse_expr(&s3, &p3) {
                Ok((e4, s4, p4)) => {
                    Ok((Node::new(*pos, p4, Expression::Gt(box e2, box e4)), s4, p4))
                }
                Err(err) => Err(err),
            },
            (t3, _, p3) => Err(Error {
                expected: vec![Token::Lt, Token::Le, Token::Eqeq, Token::Ge, Token::Gt],
                got: t3,
                pos: p3,
            }),
        },
        Err(err) => Err(err),
    }
}

fn parse_bfactor<T: Field>(
    input: &String,
    pos: &Position,
) -> Result<(ExpressionNode<T>, String, Position), Error<T>> {
    match next_token::<T>(input, pos) {
        (Token::Not, s1, p1) => match next_token(&s1, &p1) {
            (Token::Open, _, _) => match parse_bfactor(&s1, &p1) {
                Ok((e3, s3, p3)) => Ok((Node::new(*pos, p3, Expression::Not(box e3)), s3, p3)),
                Err(err) => Err(err),
            },
            (t2, _, p2) => Err(Error {
                expected: vec![Token::Open],
                got: t2,
                pos: p2,
            }),
        },
        (Token::Open, s1, p1) => match parse_bexpr(&s1, &p1) {
            Ok((e2, s2, p2)) => match next_token::<T>(&s2, &p2) {
                (Token::Close, s3, p3) => Ok((e2, s3, p3)),
                (t3, _, p3) => Err(Error {
                    expected: vec![Token::Close],
                    got: t3,
                    pos: p3,
                }),
            },
            Err(err) => Err(err),
        },
        _ => parse_prim_cond(&input, &pos),
    }
}

pub fn parse_bterm1<T: Field>(
    expr: ExpressionNode<T>,
    input: String,
    pos: Position,
) -> Result<(ExpressionNode<T>, String, Position), Error<T>> {
    match next_token::<T>(&input, &pos) {
        (Token::And, s1, p1) => match parse_bterm(&s1, &p1) {
            Ok((e, s2, p2)) => Ok((Node::new(pos, p2, Expression::And(box expr, box e)), s2, p2)),
            Err(err) => Err(err),
        },
        _ => Ok((expr, input, pos)),
    }
}

fn parse_bterm<T: Field>(
    input: &String,
    pos: &Position,
) -> Result<(ExpressionNode<T>, String, Position), Error<T>> {
    match parse_bfactor(input, pos) {
        Ok((e, s1, p1)) => parse_bterm1(e, s1, p1),
        Err(err) => Err(err),
    }
}

fn parse_bexpr1<T: Field>(
    expr: ExpressionNode<T>,
    input: String,
    pos: Position,
) -> Result<(ExpressionNode<T>, String, Position), Error<T>> {
    match next_token::<T>(&input, &pos) {
        (Token::Or, s1, p1) => match parse_bterm(&s1, &p1) {
            Ok((e2, s2, p2)) => {
                parse_bexpr1(Node::new(pos, p2, Expression::Or(box expr, box e2)), s2, p2)
            }
            Err(err) => Err(err),
        },
        _ => Ok((expr, input, pos)),
    }
}

fn parse_bexpr<T: Field>(
    input: &String,
    pos: &Position,
) -> Result<(ExpressionNode<T>, String, Position), Error<T>> {
    match next_token::<T>(input, pos) {
        (Token::Not, s1, p1) => match next_token(&s1, &p1) {
            (Token::Open, s2, p2) => match parse_bexpr(&s2, &p2) {
                Ok((e3, s3, p3)) => match next_token(&s3, &p3) {
                    (Token::Close, s4, p4) => {
                        match parse_bterm1(Node::new(*pos, p4, Expression::Not(box e3)), s4, p4) {
                            Ok((e5, s5, p5)) => parse_bexpr1(e5, s5, p5),
                            Err(err) => Err(err),
                        }
                    }
                    (t4, _, p4) => Err(Error {
                        expected: vec![Token::Close],
                        got: t4,
                        pos: p4,
                    }),
                },
                Err(err) => Err(err),
            },
            (t2, _, p2) => Err(Error {
                expected: vec![Token::Open],
                got: t2,
                pos: p2,
            }),
        },
        (Token::Open, s1, p1) => match parse_bexpr(&s1, &p1) {
            Ok((e2, s2, p2)) => match next_token(&s2, &p2) {
                (Token::Close, s3, p3) => match parse_bterm1(e2, s3, p3) {
                    Ok((e4, s4, p4)) => parse_bexpr1(e4, s4, p4),
                    Err(err) => Err(err),
                },
                (t3, _, p3) => Err(Error {
                    expected: vec![Token::Close],
                    got: t3,
                    pos: p3,
                }),
            },
            Err(_) => match parse_prim_cond(input, pos) {
                Ok((e2, s2, p2)) => match parse_bterm1(e2, s2, p2) {
                    Ok((e3, s3, p3)) => parse_bexpr1(e3, s3, p3),
                    Err(err) => Err(err),
                },
                Err(err) => Err(err),
            },
        },
        (Token::Ide(_), _, _) | (Token::Num(_), _, _) => match parse_prim_cond(input, pos) {
            Ok((e2, s2, p2)) => match parse_bterm1(e2, s2, p2) {
                Ok((e3, s3, p3)) => parse_bexpr1(e3, s3, p3),
                Err(err) => Err(err),
            },
            Err(err) => Err(err),
        },
        (t1, _, p1) => Err(Error {
            expected: vec![Token::Open, Token::ErrIde, Token::ErrNum],
            got: t1,
            pos: p1,
        }),
    }
}

fn parse_if_then_else<T: Field>(
    input: &String,
    pos: &Position,
) -> Result<(ExpressionNode<T>, String, Position), Error<T>> {
    match next_token(input, pos) {
        (Token::If, s1, p1) => match parse_bexpr(&s1, &p1) {
            Ok((e2, s2, p2)) => parse_then_else(e2, &s2, &p2),
            Err(err) => Err(err),
        },
        (t1, _, p1) => Err(Error {
            expected: vec![Token::If],
            got: t1,
            pos: p1,
        }),
    }
}

fn parse_factor1<T: Field>(
    expr: ExpressionNode<T>,
    input: String,
    pos: Position,
) -> Result<(ExpressionNode<T>, String, Position), Error<T>> {
    match parse_term1(expr.clone(), input.clone(), pos.clone()) {
        Ok((e1, s1, p1)) => match parse_expr1(e1, s1, p1) {
            Ok((e2, s2, p2)) => match next_token::<T>(&s2, &p2) {
                (Token::Pow, s3, p3) => match next_token(&s3, &p3) {
                    (Token::Num(x), s4, p4) => Ok((
                        Node::new(
                            pos,
                            p4,
                            Expression::Pow(box e2, box Node::new(p3, p4, Expression::Number(x))),
                        ),
                        s4,
                        p4,
                    )),
                    (t4, _, p4) => Err(Error {
                        expected: vec![Token::ErrNum],
                        got: t4,
                        pos: p4,
                    }),
                },
                _ => Ok((expr, input, pos)),
            },
            Err(err) => Err(err),
        },
        Err(err) => Err(err),
    }
}

// parse an identifier or select or function call
fn parse_identified1<T: Field>(
    x: String,
    input: String,
    position: Position,
) -> Result<(ExpressionNode<T>, String, Position), Error<T>> {
    let ide_initial_pos = Position {
        col: position.col - x.len(),
        ..position
    };
    match next_token::<T>(&input, &position) {
        (Token::Open, s1, p1) => parse_function_call(x, s1, p1),
        (Token::LeftBracket, s1, p1) => parse_array_select(x, s1, p1),
        _ => Ok((
            Node::new(ide_initial_pos, position, Expression::Identifier(x)),
            input,
            position,
        )),
    }
}

fn parse_factor<T: Field>(
    input: &String,
    pos: &Position,
) -> Result<(ExpressionNode<T>, String, Position), Error<T>> {
    match next_token(input, pos) {
        (Token::If, ..) => parse_if_then_else(input, pos),
        (Token::Open, s1, p1) => match parse_expr(&s1, &p1) {
            Ok((e2, s2, p2)) => match next_token(&s2, &p2) {
                (Token::Close, s3, p3) => parse_factor1(e2, s3, p3),
                (t3, _, p3) => Err(Error {
                    expected: vec![Token::Close],
                    got: t3,
                    pos: p3,
                }),
            },
            Err(err) => Err(err),
        },
        (Token::Ide(x), s1, p1) => match parse_identified1(x, s1, p1) {
            Ok((e2, s2, p2)) => parse_factor1(e2, s2, p2),
            e => e,
        },
        (Token::Num(x), s1, p1) => {
            parse_factor1(Node::new(*pos, p1, Expression::Number(x)), s1, p1)
        }
        (t1, _, p1) => Err(Error {
            expected: vec![Token::If, Token::Open, Token::ErrIde, Token::ErrNum],
            got: t1,
            pos: p1,
        }),
    }
}

pub fn parse_term1<T: Field>(
    expr: ExpressionNode<T>,
    input: String,
    pos: Position,
) -> Result<(ExpressionNode<T>, String, Position), Error<T>> {
    match next_token::<T>(&input, &pos) {
        (Token::Mult, s1, p1) => match parse_term(&s1, &p1) {
            Ok((e, s2, p2)) => Ok((
                Node::new(expr.start, p2, Expression::Mult(box expr, box e)),
                s2,
                p2,
            )),
            Err(err) => Err(err),
        },
        (Token::Div, s1, p1) => match parse_term(&s1, &p1) {
            Ok((e, s2, p2)) => Ok((
                Node::new(expr.start, p2, Expression::Div(box expr, box e)),
                s2,
                p2,
            )),
            Err(err) => Err(err),
        },
        _ => Ok((expr, input, pos)),
    }
}

fn parse_term<T: Field>(
    input: &String,
    pos: &Position,
) -> Result<(ExpressionNode<T>, String, Position), Error<T>> {
    match parse_factor(input, pos) {
        Ok((e, s1, p1)) => parse_term1(e, s1, p1),
        Err(err) => Err(err),
    }
}

pub fn parse_expr1<T: Field>(
    expr: ExpressionNode<T>,
    input: String,
    pos: Position,
) -> Result<(ExpressionNode<T>, String, Position), Error<T>> {
    match next_token::<T>(&input, &pos) {
        (Token::Add, s1, p1) => match parse_term(&s1, &p1) {
            Ok((e2, s2, p2)) => parse_expr1(
                Node::new(expr.start, p2, Expression::Add(box expr, box e2)),
                s2,
                p2,
            ),
            Err(err) => Err(err),
        },
        (Token::Sub, s1, p1) => match parse_term(&s1, &p1) {
            Ok((e2, s2, p2)) => parse_expr1(
                Node::new(expr.start, p2, Expression::Sub(box expr, box e2)),
                s2,
                p2,
            ),
            Err(err) => Err(err),
        },
        (Token::Pow, s1, p1) => match parse_term(&s1, &p1) {
            Ok((e, s2, p2)) => match parse_term1(
                Node::new(expr.start, p2, Expression::Pow(box expr, box e)),
                s2,
                p2,
            ) {
                Ok((e3, s3, p3)) => parse_expr1(e3, s3, p3),
                Err(err) => Err(err),
            },
            Err(err) => Err(err),
        },
        _ => Ok((expr, input, pos)),
    }
}

pub fn parse_function_call<T: Field>(
    ide: String,
    input: String,
    pos: Position,
) -> Result<(ExpressionNode<T>, String, Position), Error<T>> {
    // backtrack to the beginning of the function identifier, plus one because we're after the `(`
    let start_pos = Position {
        col: pos.col - ide.len() - 1,
        ..pos
    };

    // function call can have 0 .. n args
    let mut args = Vec::new();
    let mut s: String = input;
    let mut p: Position = pos;

    loop {
        match next_token::<T>(&s, &p) {
            // no arguments
            (Token::Close, s1, p1) => {
                return parse_term1(
                    Node::new(start_pos, p1, Expression::FunctionCall(ide, args)),
                    s1,
                    p1,
                );
            }
            // at least one argument
            (_, _, _) => match parse_expr(&s, &p) {
                Ok((e1, s1, p1)) => {
                    args.push(e1);
                    match next_token::<T>(&s1, &p1) {
                        (Token::Comma, s2, p2) => {
                            s = s2;
                            p = p2;
                        }
                        (Token::Close, s2, p2) => {
                            return parse_term1(
                                Node::new(start_pos, p2, Expression::FunctionCall(ide, args)),
                                s2,
                                p2,
                            );
                        }
                        (t2, _, p2) => {
                            return Err(Error {
                                expected: vec![Token::Comma, Token::Close],
                                got: t2,
                                pos: p2,
                            });
                        }
                    }
                }
                Err(err) => return Err(err),
            },
        }
    }
}

pub fn parse_inline_array<T: Field>(
    input: String,
    pos: Position,
) -> Result<(ExpressionNode<T>, String, Position), Error<T>> {
    // function call can have 0 .. n args
    let mut expressions = Vec::new();
    let mut s: String = input;
    let mut p: Position = pos;

    loop {
        match next_token::<T>(&s, &p) {
            // no arguments
            (Token::RightBracket, s1, p1) => {
                match parse_term1(
                    Node::new(pos, p1, Expression::InlineArray(expressions)),
                    s1,
                    p1,
                ) {
                    Ok((e2, s2, p2)) => return parse_expr1(e2, s2, p2),
                    Err(err) => return Err(err),
                }
            }
            // at least one argument
            (_, _, _) => match parse_expr(&s, &p) {
                Ok((e1, s1, p1)) => {
                    expressions.push(e1);
                    match next_token::<T>(&s1, &p1) {
                        (Token::Comma, s2, p2) => {
                            s = s2;
                            p = p2;
                        }
                        (Token::RightBracket, s2, p2) => {
                            match parse_term1(
                                Node::new(pos, p2, Expression::InlineArray(expressions)),
                                s2,
                                p2,
                            ) {
                                Ok((e3, s3, p3)) => return parse_expr1(e3, s3, p3),
                                Err(err) => return Err(err),
                            }
                        }
                        (t2, _, p2) => {
                            return Err(Error {
                                expected: vec![Token::Comma, Token::RightBracket],
                                got: t2,
                                pos: p2,
                            });
                        }
                    }
                }
                Err(err) => return Err(err),
            },
        }
    }
}

pub fn parse_array_select<T: Field>(
    ide: String,
    input: String,
    pos: Position,
) -> Result<(ExpressionNode<T>, String, Position), Error<T>> {
    let start_pos = Position {
        col: pos.col - ide.len() - 1,
        ..pos
    };

    // array select can have exactly one arg
    match next_token::<T>(&input, &pos) {
        (_, _, _) => match parse_expr(&input, &pos) {
            Ok((e1, s1, p1)) => match next_token::<T>(&s1, &p1) {
                (Token::RightBracket, s2, p2) => parse_term1(
                    Node::new(
                        pos,
                        p2,
                        Expression::Select(
                            box Node::new(start_pos, p1, Expression::Identifier(ide)),
                            box e1,
                        ),
                    ),
                    s2,
                    p2,
                ),
                (t2, _, p2) => Err(Error {
                    expected: vec![Token::RightBracket],
                    got: t2,
                    pos: p2,
                }),
            },
            Err(err) => Err(err),
        },
    }
}

pub fn parse_expr<T: Field>(
    input: &String,
    pos: &Position,
) -> Result<(ExpressionNode<T>, String, Position), Error<T>> {
    match next_token::<T>(input, pos) {
        (Token::If, ..) => parse_if_then_else(input, pos),
        (Token::Open, s1, p1) => match parse_expr(&s1, &p1) {
            Ok((e2, s2, p2)) => match next_token(&s2, &p2) {
                (Token::Close, s3, p3) => match parse_term1(e2, s3, p3) {
                    Ok((e4, s4, p4)) => parse_expr1(e4, s4, p4),
                    Err(err) => Err(err),
                },
                (t3, _, p3) => Err(Error {
                    expected: vec![Token::Close],
                    got: t3,
                    pos: p3,
                }),
            },
            Err(err) => Err(err),
        },
        (Token::Ide(x), s1, p1) => match parse_identified1(x, s1, p1) {
            Ok((e2, s2, p2)) => match parse_term1(e2, s2, p2) {
                Ok((e3, s3, p3)) => parse_expr1(e3, s3, p3),
                e => e,
            },
            e => e,
        },
        (Token::Num(x), s1, p1) => {
            match parse_term1(Node::new(*pos, p1, Expression::Number(x)), s1, p1) {
                Ok((e2, s2, p2)) => parse_expr1(e2, s2, p2),
                Err(err) => Err(err),
            }
        }
        (Token::LeftBracket, s1, p1) => parse_inline_array(s1, p1),
        (t1, _, p1) => Err(Error {
            expected: vec![Token::If, Token::Open, Token::ErrIde, Token::ErrNum],
            got: t1,
            pos: p1,
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    mod terms {
        use super::*;

        #[test]
        fn parse_number_sum() {
            let pos = Position { line: 45, col: 121 };
            let string = String::from("1 + 2 + 3");
            let expr = Expression::Add(
                box Expression::Add(
                    box Expression::Number(FieldPrime::from(1)).into(),
                    box Expression::Number(FieldPrime::from(2)).into(),
                )
                .into(),
                box Expression::Number(FieldPrime::from(3)).into(),
            )
            .into();
            assert_eq!(
                Ok((expr, String::from(""), pos.col(string.len() as isize))),
                parse_expr(&string, &pos)
            );
        }

        #[test]
        fn parse_number_sub() {
            let pos = Position { line: 45, col: 121 };
            let string = String::from("1 - 2 - 3");
            let expr = Expression::Sub(
                box Expression::Sub(
                    box Expression::Number(FieldPrime::from(1)).into(),
                    box Expression::Number(FieldPrime::from(2)).into(),
                )
                .into(),
                box Expression::Number(FieldPrime::from(3)).into(),
            )
            .into();
            assert_eq!(
                Ok((expr, String::from(""), pos.col(string.len() as isize))),
                parse_expr(&string, &pos)
            );
        }

        #[test]
        fn parse_function_call_single_sub() {
            let pos = Position { line: 45, col: 121 };
            let string = String::from("1 - f(a)");
            let expr = Expression::Sub(
                box Expression::Number(FieldPrime::from(1)).into(),
                box Expression::FunctionCall(
                    String::from("f"),
                    vec![Expression::Identifier(String::from("a")).into()],
                )
                .into(),
            )
            .into();
            assert_eq!(
                Ok((expr, String::from(""), pos.col(string.len() as isize))),
                parse_expr(&string, &pos)
            );
        }

        #[test]
        fn parse_function_call_sub() {
            let pos = Position { line: 45, col: 121 };
            let string = String::from("1 - f() - 3");
            let expr = Expression::Sub(
                box Expression::Sub(
                    box Expression::Number(FieldPrime::from(1)).into(),
                    box Expression::FunctionCall(String::from("f"), vec![]).into(),
                )
                .into(),
                box Expression::Number(FieldPrime::from(3)).into(),
            )
            .into();
            assert_eq!(
                Ok((expr, String::from(""), pos.col(string.len() as isize))),
                parse_expr(&string, &pos)
            );
        }

        #[test]
        fn parse_function_call_add() {
            let pos = Position { line: 45, col: 121 };
            let string = String::from("1 + f() + 3");
            let expr = Expression::Add(
                box Expression::Add(
                    box Expression::Number(FieldPrime::from(1)).into(),
                    box Expression::FunctionCall(String::from("f"), vec![]).into(),
                )
                .into(),
                box Expression::Number(FieldPrime::from(3)).into(),
            )
            .into();
            assert_eq!(
                Ok((expr, String::from(""), pos.col(string.len() as isize))),
                parse_expr(&string, &pos)
            );
        }

        #[test]
        fn parse_select_sub() {
            let pos = Position { line: 45, col: 121 };
            let string = String::from("1 - f[2] - 3");
            let expr = Expression::Sub(
                box Expression::Sub(
                    box Expression::Number(FieldPrime::from(1)).into(),
                    box Expression::Select(
                        box Expression::Identifier(String::from("f")).into(),
                        box Expression::Number(FieldPrime::from(2)).into(),
                    )
                    .into(),
                )
                .into(),
                box Expression::Number(FieldPrime::from(3)).into(),
            )
            .into();
            assert_eq!(
                Ok((expr, String::from(""), pos.col(string.len() as isize))),
                parse_expr(&string, &pos)
            );
        }

        #[test]
        fn parse_select_add() {
            let pos = Position { line: 45, col: 121 };
            let string = String::from("1 + f[2] + 3");
            let expr = Expression::Add(
                box Expression::Add(
                    box Expression::Number(FieldPrime::from(1)).into(),
                    box Expression::Select(
                        box Expression::Identifier(String::from("f")).into(),
                        box Expression::Number(FieldPrime::from(2)).into(),
                    )
                    .into(),
                )
                .into(),
                box Expression::Number(FieldPrime::from(3)).into(),
            )
            .into();
            assert_eq!(
                Ok((expr, String::from(""), pos.col(string.len() as isize))),
                parse_expr(&string, &pos)
            );
        }

        #[test]
        fn parse_identifier_sub() {
            let pos = Position { line: 45, col: 121 };
            let string = String::from("1 - f - 3");
            let expr = Expression::Sub(
                box Expression::Sub(
                    box Expression::Number(FieldPrime::from(1)).into(),
                    box Expression::Identifier(String::from("f")).into(),
                )
                .into(),
                box Expression::Number(FieldPrime::from(3)).into(),
            )
            .into();
            assert_eq!(
                Ok((expr, String::from(""), pos.col(string.len() as isize))),
                parse_expr(&string, &pos)
            );
        }

        #[test]
        fn parse_identifier_add() {
            let pos = Position { line: 45, col: 121 };
            let string = String::from("1 + f + 3");
            let expr = Expression::Add(
                box Expression::Add(
                    box Expression::Number(FieldPrime::from(1)).into(),
                    box Expression::Identifier(String::from("f")).into(),
                )
                .into(),
                box Expression::Number(FieldPrime::from(3)).into(),
            )
            .into();
            assert_eq!(
                Ok((expr, String::from(""), pos.col(string.len() as isize))),
                parse_expr(&string, &pos)
            );
        }
    }

    #[test]
    fn parse_if_then_else_ok() {
        let pos = Position { line: 45, col: 121 };
        let string = String::from("if a < b then c else d fi");
        let expr = Expression::IfElse::<FieldPrime>(
            box Expression::Lt(
                box Expression::Identifier(String::from("a")).into(),
                box Expression::Identifier(String::from("b")).into(),
            )
            .into(),
            box Expression::Identifier(String::from("c")).into(),
            box Expression::Identifier(String::from("d")).into(),
        )
        .into();
        assert_eq!(
            Ok((expr, String::from(""), pos.col(string.len() as isize))),
            parse_if_then_else(&string, &pos)
        );
    }

    #[test]
    fn parse_boolean_and() {
        let pos = Position { line: 45, col: 121 };
        let string = String::from("if a < b && 2*a > b && b > a then c else d fi");

        let expr = Expression::IfElse::<FieldPrime>(
            box Expression::And(
                box Expression::Lt(
                    box Expression::Identifier(String::from("a")).into(),
                    box Expression::Identifier(String::from("b")).into(),
                )
                .into(),
                box Expression::And(
                    box Expression::Gt(
                        box Expression::Mult(
                            box Expression::Number(FieldPrime::from(2)).into(),
                            box Expression::Identifier(String::from("a")).into(),
                        )
                        .into(),
                        box Expression::Identifier(String::from("b")).into(),
                    )
                    .into(),
                    box Expression::Gt(
                        box Expression::Identifier(String::from("b")).into(),
                        box Expression::Identifier(String::from("a")).into(),
                    )
                    .into(),
                )
                .into(),
            )
            .into(),
            box Expression::Identifier(String::from("c")).into(),
            box Expression::Identifier(String::from("d")).into(),
        )
        .into();

        assert_eq!(
            Ok((expr, String::from(""), pos.col(string.len() as isize))),
            parse_if_then_else(&string, &pos)
        );
    }

    mod array_select {
        use super::*;

        #[test]
        fn array_select() {
            let pos = Position { line: 45, col: 121 };
            let string = String::from("foo[42 + 33]");
            let expr = Expression::Select::<FieldPrime>(
                box Expression::Identifier(String::from("foo")).into(),
                box Expression::Add(
                    box Expression::Number(FieldPrime::from(42)).into(),
                    box Expression::Number(FieldPrime::from(33)).into(),
                )
                .into(),
            )
            .into();
            assert_eq!(
                Ok((expr, String::from(""), pos.col(string.len() as isize))),
                parse_expr(&string, &pos)
            );
        }

        #[test]
        fn array_select_empty() {
            let pos = Position { line: 45, col: 121 };
            let string = String::from("foo[]");

            let res = parse_expr::<FieldPrime>(&string, &pos);

            assert!(res.is_err());
            let res = res.unwrap_err();
            assert_eq!(res.got, Token::RightBracket);
            assert_eq!(res.pos, pos.col(string.len() as isize));
        }
    }

    #[test]
    fn parse_boolean_or() {
        let pos = Position { line: 45, col: 121 };
        let string = String::from("if a < b || 2*a > b then c else d fi");

        let expr = Expression::IfElse::<FieldPrime>(
            box Expression::Or(
                box Expression::Lt(
                    box Expression::Identifier(String::from("a")).into(),
                    box Expression::Identifier(String::from("b")).into(),
                )
                .into(),
                box Expression::Gt(
                    box Expression::Mult(
                        box Expression::Number(FieldPrime::from(2)).into(),
                        box Expression::Identifier(String::from("a")).into(),
                    )
                    .into(),
                    box Expression::Identifier(String::from("b")).into(),
                )
                .into(),
            )
            .into(),
            box Expression::Identifier(String::from("c")).into(),
            box Expression::Identifier(String::from("d")).into(),
        )
        .into();
        assert_eq!(
            Ok((expr, String::from(""), pos.col(string.len() as isize))),
            parse_if_then_else(&string, &pos)
        );
    }

    #[test]
    fn parse_boolean_operator_associativity() {
        use absy::Expression::*;
        let pos = Position { line: 45, col: 121 };
        let string = String::from("2 == 3 || 4 == 5 && 6 == 7");
        let expr = Or::<FieldPrime>(
            box Eq(
                box Number(FieldPrime::from(2)).into(),
                box Number(FieldPrime::from(3)).into(),
            )
            .into(),
            box And(
                box Eq(
                    box Number(FieldPrime::from(4)).into(),
                    box Number(FieldPrime::from(5)).into(),
                )
                .into(),
                box Eq(
                    box Number(FieldPrime::from(6)).into(),
                    box Number(FieldPrime::from(7)).into(),
                )
                .into(),
            )
            .into(),
        )
        .into();
        assert_eq!(
            Ok((expr, String::from(""), pos.col(string.len() as isize))),
            parse_bexpr(&string, &pos)
        );
    }

    #[test]
    fn parse_boolean_expr() {
        use absy::Expression::*;
        let pos = Position { line: 45, col: 121 };
        let string = String::from("(a + 2 == 3) && (a * 2 + 3 == 2 || a < 3) || 1 < 2");
        let expr = Or::<FieldPrime>(
            box And(
                box Eq(
                    box Add(
                        box Identifier(String::from("a")).into(),
                        box Number(FieldPrime::from(2)).into(),
                    )
                    .into(),
                    box Number(FieldPrime::from(3)).into(),
                )
                .into(),
                box Or(
                    box Eq(
                        box Add(
                            box Mult(
                                box Identifier(String::from("a")).into(),
                                box Number(FieldPrime::from(2)).into(),
                            )
                            .into(),
                            box Number(FieldPrime::from(3)).into(),
                        )
                        .into(),
                        box Number(FieldPrime::from(2)).into(),
                    )
                    .into(),
                    box Lt(
                        box Identifier(String::from("a")).into(),
                        box Number(FieldPrime::from(3)).into(),
                    )
                    .into(),
                )
                .into(),
            )
            .into(),
            box Lt(
                box Number(FieldPrime::from(1)).into(),
                box Number(FieldPrime::from(2)).into(),
            )
            .into(),
        )
        .into();
        assert_eq!(
            Ok((expr, String::from(""), pos.col(string.len() as isize))),
            parse_bexpr(&string, &pos)
        );
    }

    mod parse_factor {
        use super::*;
        #[test]
        fn if_then_else() {
            let pos = Position { line: 45, col: 121 };
            let string = String::from("if a < b then c else d fi");
            let expr = Expression::IfElse::<FieldPrime>(
                box Expression::Lt(
                    box Expression::Identifier(String::from("a")).into(),
                    box Expression::Identifier(String::from("b")).into(),
                )
                .into(),
                box Expression::Identifier(String::from("c")).into(),
                box Expression::Identifier(String::from("d")).into(),
            )
            .into();
            assert_eq!(
                Ok((expr, String::from(""), pos.col(string.len() as isize))),
                parse_factor(&string, &pos)
            );
        }
        #[test]
        fn brackets() {
            let pos = Position { line: 45, col: 121 };
            let string = String::from("(5 + a * 6)");
            let expr = Expression::Add(
                box Expression::Number(FieldPrime::from(5)).into(),
                box Expression::Mult(
                    box Expression::Identifier(String::from("a")).into(),
                    box Expression::Number(FieldPrime::from(6)).into(),
                )
                .into(),
            )
            .into();
            assert_eq!(
                Ok((expr, String::from(""), pos.col(string.len() as isize))),
                parse_factor(&string, &pos)
            );
        }
        #[test]
        fn ide() {
            let pos = Position { line: 45, col: 121 };
            let string = String::from("a");
            let expr = Expression::Identifier::<FieldPrime>(String::from("a")).into();
            assert_eq!(
                Ok((expr, String::from(""), pos.col(string.len() as isize))),
                parse_factor(&string, &pos)
            );
        }
        #[test]
        fn num() {
            let pos = Position { line: 45, col: 121 };
            let string = String::from("234");
            let expr = Expression::Number(FieldPrime::from(234)).into();
            assert_eq!(
                Ok((expr, String::from(""), pos.col(string.len() as isize))),
                parse_factor(&string, &pos)
            );
        }
    }
}
