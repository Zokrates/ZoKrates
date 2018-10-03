use field::Field;

use parser::Error;
use parser::tokenize::{Token, Position, next_token};

use absy::{Expression};

use parser::tokenize::parse_num;

fn parse_then_else<T: Field>(
    cond: Expression<T>,
    input: &String,
    pos: &Position,
) -> Result<(Expression<T>, String, Position), Error<T>> {
    match next_token(input, pos) {
        (Token::Then, s5, p5) => match parse_expr(&s5, &p5) {
            Ok((e6, s6, p6)) => match next_token(&s6, &p6) {
                (Token::Else, s7, p7) => match parse_expr(&s7, &p7) {
                    Ok((e8, s8, p8)) => match next_token(&s8, &p8) {
                        (Token::Fi, s9, p9) => {
                            parse_expr1(Expression::IfElse(box cond, box e6, box e8), s9, p9)
                        }
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
) -> Result<(Expression<T>, String, Position), Error<T>> {
    match parse_expr(input, pos) {
        Ok((e2, s2, p2)) => match next_token(&s2, &p2) {
            (Token::Lt, s3, p3) => match parse_expr(&s3, &p3) {
                Ok((e4, s4, p4)) => Ok((Expression::Lt(box e2, box e4), s4, p4)),
                Err(err) => Err(err),
            },
            (Token::Le, s3, p3) => match parse_expr(&s3, &p3) {
                Ok((e4, s4, p4)) => Ok((Expression::Le(box e2, box e4), s4, p4)),
                Err(err) => Err(err),
            },
            (Token::Eqeq, s3, p3) => match parse_expr(&s3, &p3) {
                Ok((e4, s4, p4)) => Ok((Expression::Eq(box e2, box e4), s4, p4)),
                Err(err) => Err(err),
            },
            (Token::Ge, s3, p3) => match parse_expr(&s3, &p3) {
                Ok((e4, s4, p4)) => Ok((Expression::Ge(box e2, box e4), s4, p4)),
                Err(err) => Err(err),
            },
            (Token::Gt, s3, p3) => match parse_expr(&s3, &p3) {
                Ok((e4, s4, p4)) => Ok((Expression::Gt(box e2, box e4), s4, p4)),
                Err(err) => Err(err),
            },
            (t3, _, p3) => Err(Error {
                expected: vec![Token::Lt, Token::Le, Token::Eqeq, Token::Ge, Token::Gt],
                got: t3,
                pos: p3,
            }),
        },
        Err(err) => Err(err)
    }
}

fn parse_condition<T: Field>(
    cond: Expression<T>,
    input: &String,
    pos: &Position,
) -> Result<(Expression<T>, String, Position), Error<T>> {
    match next_token(input, pos) {
        (Token::AndAnd, s1, p1) => match parse_prim_cond(&s1, &p1) {
            Ok((e2, s2, p2)) => parse_condition(Expression::AndAnd(box cond, box e2), &s2, &p2),
            Err(err) => Err(err),
        },
        (Token::Then, _, _) => parse_then_else(cond, input, pos),
        (t1, _, p1) => Err(Error {
            expected: vec![Token::AndAnd, Token::Then],
            got: t1,
            pos: p1,
        }),
    }
}

fn parse_if_then_else<T: Field>(
    input: &String,
    pos: &Position,
) -> Result<(Expression<T>, String, Position), Error<T>> {
    match next_token(input, pos) {
        (Token::If, s1, p1) => match parse_prim_cond(&s1, &p1) {
            Ok((e2, s2, p2)) => parse_condition(e2, &s2, &p2),
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
    expr: Expression<T>,
    input: String,
    pos: Position,
) -> Result<(Expression<T>, String, Position), Error<T>> {
    match parse_term1(expr.clone(), input.clone(), pos.clone()) {
        Ok((e1, s1, p1)) => match parse_expr1(e1, s1, p1) {
            Ok((e2, s2, p2)) => match next_token::<T>(&s2, &p2) {
                (Token::Pow, s3, p3) => match next_token(&s3, &p3) {
                    (Token::Num(x), s4, p4) => {
                        Ok((Expression::Pow(box e2, box Expression::Number(x)), s4, p4))
                    }
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

fn parse_factor<T: Field>(
    input: &String,
    pos: &Position,
) -> Result<(Expression<T>, String, Position), Error<T>> {
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
        (Token::Ide(x), s1, p1) => match next_token::<T>(&s1, &p1) {
            (Token::Open, s2, p2) => parse_function_call(x, s2, p2),
            _ => parse_factor1(Expression::Identifier(x), s1, p1),
        },
        (Token::Num(x), s1, p1) => parse_factor1(Expression::Number(x), s1, p1),
        (t1, _, p1) => Err(Error {
            expected: vec![Token::If, Token::Open, Token::ErrIde, Token::ErrNum],
            got: t1,
            pos: p1,
        }),
    }
}

pub fn parse_term1<T: Field>(
    expr: Expression<T>,
    input: String,
    pos: Position,
) -> Result<(Expression<T>, String, Position), Error<T>> {
    match next_token::<T>(&input, &pos) {
        (Token::Mult, s1, p1) => match parse_term(&s1, &p1) {
            Ok((e, s2, p2)) => Ok((Expression::Mult(box expr, box e), s2, p2)),
            Err(err) => Err(err),
        },
        (Token::Div, s1, p1) => match parse_term(&s1, &p1) {
            Ok((e, s2, p2)) => Ok((Expression::Div(box expr, box e), s2, p2)),
            Err(err) => Err(err),
        },
        _ => Ok((expr, input, pos)),
    }
}

fn parse_term<T: Field>(
    input: &String,
    pos: &Position,
) -> Result<(Expression<T>, String, Position), Error<T>> {
    match parse_factor(input, pos) {
        Ok((e, s1, p1)) => parse_term1(e, s1, p1),
        Err(err) => Err(err),
    }
}

pub fn parse_expr1<T: Field>(
    expr: Expression<T>,
    input: String,
    pos: Position,
) -> Result<(Expression<T>, String, Position), Error<T>> {
    match next_token::<T>(&input, &pos) {
        (Token::Add, s1, p1) => match parse_term(&s1, &p1) {
            Ok((e2, s2, p2)) => parse_expr1(Expression::Add(box expr, box e2), s2, p2),
            Err(err) => Err(err),
        },
        (Token::Sub, s1, p1) => match parse_term(&s1, &p1) {
            Ok((e2, s2, p2)) => parse_expr1(Expression::Sub(box expr, box e2), s2, p2),
            Err(err) => Err(err),
        },
        (Token::Pow, s1, p1) => match parse_num(&s1, &p1) {
            (Token::Num(x), s2, p2) => {
                match parse_term1(Expression::Pow(box expr, box Expression::Number(x)), s2, p2) {
                    Ok((e3, s3, p3)) => parse_expr1(e3, s3, p3),
                    Err(err) => Err(err),
                }
            }
            (t2, _, p2) => Err(Error {
                expected: vec![Token::ErrNum],
                got: t2,
                pos: p2,
            }),
        },
        _ => Ok((expr, input, pos)),
    }
}

pub fn parse_function_call<T: Field>(
    ide: String,
    input: String,
    pos: Position,
) -> Result<(Expression<T>, String, Position), Error<T>> {
    // function call can have 0 .. n args
    let mut args = Vec::new();
    let mut s: String = input;
    let mut p: Position = pos;

    loop {
        match next_token::<T>(&s, &p) {
            // no arguments
            (Token::Close, s1, p1) => {
                match parse_term1(Expression::FunctionCall(ide, args), s1, p1) {
                    Ok((e2, s2, p2)) => return parse_expr1(e2, s2, p2),
                    Err(err) => return Err(err),
                }
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
                            match parse_term1(Expression::FunctionCall(ide, args), s2, p2) {
                                Ok((e3, s3, p3)) => return parse_expr1(e3, s3, p3),
                                Err(err) => return Err(err),
                            }
                        }
                        (t2, _, p2) => {
                            return Err(Error {
                                expected: vec![Token::Comma, Token::Close],
                                got: t2,
                                pos: p2,
                            })
                        }
                    }
                }
                Err(err) => return Err(err),
            },
        }
    }
}

pub fn parse_expr<T: Field>(
    input: &String,
    pos: &Position,
) -> Result<(Expression<T>, String, Position), Error<T>> {
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
        (Token::Ide(x), s1, p1) => match next_token::<T>(&s1, &p1) {
            (Token::Open, s2, p2) => parse_function_call(x, s2, p2),
            _ => match parse_term1(Expression::Identifier(x), s1, p1) {
                Ok((e2, s2, p2)) => parse_expr1(e2, s2, p2),
                Err(err) => Err(err),
            },
        },
        (Token::Num(x), s1, p1) => match parse_term1(Expression::Number(x), s1, p1) {
            Ok((e2, s2, p2)) => parse_expr1(e2, s2, p2),
            Err(err) => Err(err),
        },
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
    use field::FieldPrime;

    #[test]
    fn parse_if_then_else_ok() {
        let pos = Position { line: 45, col: 121 };
        let string = String::from("if a < b then c else d fi");
        let expr = Expression::IfElse::<FieldPrime>(
            box Expression::Lt(
                box Expression::Identifier(String::from("a")),
                box Expression::Identifier(String::from("b")),
            ),
            box Expression::Identifier(String::from("c")),
            box Expression::Identifier(String::from("d")),
        );
        assert_eq!(
            Ok((expr, String::from(""), pos.col(string.len() as isize))),
            parse_if_then_else(&string, &pos)
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
                    box Expression::Identifier(String::from("a")),
                    box Expression::Identifier(String::from("b")),
                ),
                box Expression::Identifier(String::from("c")),
                box Expression::Identifier(String::from("d")),
            );
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
                box Expression::Number(FieldPrime::from(5)),
                box Expression::Mult(
                    box Expression::Identifier(String::from("a")),
                    box Expression::Number(FieldPrime::from(6)),
                ),
            );
            assert_eq!(
                Ok((expr, String::from(""), pos.col(string.len() as isize))),
                parse_factor(&string, &pos)
            );
        }
        #[test]
        fn ide() {
            let pos = Position { line: 45, col: 121 };
            let string = String::from("a");
            let expr = Expression::Identifier::<FieldPrime>(String::from("a"));
            assert_eq!(
                Ok((expr, String::from(""), pos.col(string.len() as isize))),
                parse_factor(&string, &pos)
            );
        }
        #[test]
        fn num() {
            let pos = Position { line: 45, col: 121 };
            let string = String::from("234");
            let expr = Expression::Number(FieldPrime::from(234));
            assert_eq!(
                Ok((expr, String::from(""), pos.col(string.len() as isize))),
                parse_factor(&string, &pos)
            );
        }
    }
}
