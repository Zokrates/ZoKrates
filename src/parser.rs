//
// @file parser.rs
// @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
// @date 2017

// Grammar:
// <prog> ::= `def' <ide> `(' <arguments> `):\\n' <stat-list>
//
// <arguments> ::= <ide> <more-args> | $\varepsilon$
//
// <more-args> ::= `,' <ide> <more-args>  | $\varepsilon$
//
// <stat-list> ::= <statement> <stat-list> | <return>
//
// <statement> ::= <ide> <statement'>
//         | `if' <expr> <comparator> <expr> `then' <expr> `else' <expr> `fi' <expr'> `==' <expr> `\\n'
//         | `(' <expr> `)' <term'> <expr'> `==' <expr> `\\n'
//         | <num> <term'> <expr'> `==' <expr> `\\n'
//         | `#' <ide> `=' <expr> `\\n'
//
// <statement'> ::= `=' <expr> `\\n'
//         | <term'> <expr'> `==' <expr> `\\n'
//
// <expr> ::= `if' <expr> <comparator> <expr> `then' <expr> `else' <expr> `fi' <expr'>
//         | `(' <expr> `)' <term'> <expr'>
//         | <ide> <term'> <expr'>
//         | <num> <term'> <expr'>
//
// <expr'> ::= `+' <term> <expr'>
//         | `-' <term> <expr'>
//         | `**' <num> <term'> <expr'>
//         | $\varepsilon$
//
// <term> ::= <factor> <term'>
//
// <term'> ::= `*' <term>
//         | `/' <term>
//         | $\varepsilon$
//
// <factor> ::= `if' <expr> <comparator> <expr> `then' <expr> `else' <expr> `fi' <expr'> `**' <num>
//         | `(' <expr> `)' <factor'>
//         | <ide> <factor'>
//         | <num> <factor'>
//
// <factor'> ::= <term'> <expr'> `**' <num>
//         | $\varepsilon$
//
// <comparator> ::= `<' | `<=' | `==' | `>=' | `>'
//
// <num> ::= `d' <num> | `d'
//
// <ide> ::= `l' <trail> | `l'
//
// <trail> ::= `d' <trail> | `l' <trail> | `d' | `l'
//

use std::fmt;
use std::io::{BufReader, Lines};
use std::io::prelude::*;
use std::fs::File;
use field::Field;
use absy::*;

#[derive(Clone,PartialEq)]
struct Position {
    line: usize,
    col: usize,
}
impl Position {
    fn col(&self, delta: isize) -> Position {
        assert!(self.col <= isize::max_value() as usize);
        assert!(self.col as isize >= delta);
        Position { line: self.line, col: (self.col as isize + delta) as usize }
    }
}
impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}
impl fmt::Debug for Position {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

#[derive(PartialEq)]
pub struct Error<T: Field> {
    expected: Vec<Token<T>>,
    got: Token<T>,
    pos: Position,
}
impl<T: Field> fmt::Display for Error<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Error at {}: Expected one of {:?}, got {:?}", self.pos.col(-(self.got.to_string().len() as isize)), self.expected, self.got)
    }
}
impl<T: Field> fmt::Debug for Error<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

#[derive(PartialEq)]
enum Token<T: Field> {
    Open, Close, Comma, Colon, Hash,
    Eq, Return,
    If, Then, Else, Fi,
    For, In, Dotdot, Do, Endfor,
    Lt, Le, Eqeq, Ge, Gt,
    Add, Sub, Mult, Div, Pow,
    Ide(String),
    Num(T),
    Unknown(String),
    // following used for error messages
    ErrIde, ErrNum
}
impl<T: Field> fmt::Display for Token<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Token::Open => write!(f, "("),
            Token::Close => write!(f, ")"),
            Token::Comma => write!(f, ","),
            Token::Colon => write!(f, ":"),
            Token::Hash => write!(f, "#"),
            Token::Eq => write!(f, "="),
            Token::Return => write!(f, "return"),
            Token::If => write!(f, "if"),
            Token::Then => write!(f, "then"),
            Token::Else => write!(f, "else"),
            Token::Fi => write!(f, "fi"),
            Token::For => write!(f, "for"),
            Token::In => write!(f, "in"),
            Token::Dotdot => write!(f, ".."),
            Token::Do => write!(f, "do"),
            Token::Endfor => write!(f, "endfor"),
            Token::Lt => write!(f, "<"),
            Token::Le => write!(f, "<="),
            Token::Eqeq => write!(f, "=="),
            Token::Ge => write!(f, ">="),
            Token::Gt => write!(f, ">"),
            Token::Add => write!(f, "+"),
            Token::Sub => write!(f, "-"),
            Token::Mult => write!(f, "*"),
            Token::Div => write!(f, "/"),
            Token::Pow => write!(f, "**"),
            Token::Ide(ref x) => write!(f, "{}", x),
            Token::Num(ref x) => write!(f, "{}", x),
            Token::Unknown(ref x) => write!(f, "{}", x),
            Token::ErrIde => write!(f, "identifier"),
            Token::ErrNum => write!(f, "number"),
        }
    }
}
impl<T: Field> fmt::Debug for Token<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ref t @ Token::ErrIde |
            ref t @ Token::ErrNum => write!(f, "{}", t),
            ref t => write!(f, "`{}`", t)
        }
    }
}

fn parse_num<T: Field>(input: &String, pos: &Position) -> (Token<T>, String, Position) {
    let mut end = 0;
    loop {
        match input.chars().nth(end) {
            Some(x) => match x {
                '0'...'9' => end += 1,
                _ => break,
            },
            None => break,
        }
    }
    assert!(end > 0);
    (Token::Num(T::from(&input[0..end])), input[end..].to_string(), Position { line: pos.line, col: pos.col + end })
}

fn parse_ide<T: Field>(input: &String, pos: &Position) -> (Token<T>, String, Position) {
    assert!(match input.chars().next().unwrap() { 'a'...'z' | 'A'...'Z' => true, _ => false });
    let mut end = 1;
    loop {
        match input.chars().nth(end) {
            Some(x) => match x {
                'a'...'z' | 'A'...'Z' | '0'...'9' => end += 1,
                _ => break,
            },
            None => break,
        }
    }
    (Token::Ide(input[0..end].to_string()), input[end..].to_string(), Position { line: pos.line, col: pos.col + end })
}

fn skip_whitespaces(input: &String) -> usize {
    let mut i = 0;
    loop {
        match input.chars().nth(i) {
            Some(' ') | Some('\t') => i += 1,
            _ => return i,
        }
    }
}

fn next_token<T: Field>(input: &String, pos: &Position) -> (Token<T>, String, Position) {
    let offset = skip_whitespaces(input);
    match input.chars().nth(offset) {
        Some('(') => (Token::Open, input[offset + 1..].to_string(), Position { line: pos.line, col: pos.col + offset + 1 }),
        Some(')') => (Token::Close, input[offset + 1..].to_string(), Position { line: pos.line, col: pos.col + offset + 1 }),
        Some(',') => (Token::Comma, input[offset + 1..].to_string(), Position { line: pos.line, col: pos.col + offset + 1 }),
        Some(':') => (Token::Colon, input[offset + 1..].to_string(), Position { line: pos.line, col: pos.col + offset + 1 }),
        Some('#') => (Token::Hash, input[offset + 1..].to_string(), Position { line: pos.line, col: pos.col + offset + 1 }),
        Some('=') => match input.chars().nth(offset + 1) {
            Some('=') => (Token::Eqeq, input[offset + 2..].to_string(), Position { line: pos.line, col: pos.col + offset + 2 }),
            _ => (Token::Eq, input[offset + 1..].to_string(), Position { line: pos.line, col: pos.col + offset + 1 }),
        },
        Some('<') => match input.chars().nth(offset + 1) {
            Some('=') => (Token::Le, input[offset + 2..].to_string(), Position { line: pos.line, col: pos.col + offset + 2 }),
            _ => (Token::Lt, input[offset + 1..].to_string(), Position { line: pos.line, col: pos.col + offset + 1 }),
        },
        Some('>') => match input.chars().nth(offset + 1) {
            Some('=') => (Token::Ge, input[offset + 2..].to_string(), Position { line: pos.line, col: pos.col + offset + 2 }),
            _ => (Token::Gt, input[offset + 1..].to_string(), Position { line: pos.line, col: pos.col + offset + 1 }),
        },
        Some('+') => (Token::Add, input[offset + 1..].to_string(), Position { line: pos.line, col: pos.col + offset + 1 }),
        Some('-') => (Token::Sub, input[offset + 1..].to_string(), Position { line: pos.line, col: pos.col + offset + 1 }),
        Some('*') => match input.chars().nth(offset + 1) {
            Some('*') => (Token::Pow, input[offset + 2..].to_string(), Position { line: pos.line, col: pos.col + offset + 2 }),
            _ => (Token::Mult, input[offset + 1..].to_string(), Position { line: pos.line, col: pos.col + offset + 1 }),
        },
        Some('/') => (Token::Div, input[offset + 1..].to_string(), Position { line: pos.line, col: pos.col + offset + 1 }),
        Some(_) if input[offset..].starts_with("return ") => (Token::Return, input[offset + 7..].to_string(), Position { line: pos.line, col: pos.col + offset + 7 }),
        Some(_) if input[offset..].starts_with("if ") => (Token::If, input[offset + 3..].to_string(), Position { line: pos.line, col: pos.col + offset + 3 }),
        Some(_) if input[offset..].starts_with("then ") => (Token::Then, input[offset + 5..].to_string(), Position { line: pos.line, col: pos.col + offset + 5 }),
        Some(_) if input[offset..].starts_with("else ") => (Token::Else, input[offset + 5..].to_string(), Position { line: pos.line, col: pos.col + offset + 5 }),
        Some(_) if input[offset..].starts_with("fi ") || input[offset..].to_string() == "fi" => (Token::Fi, input[offset + 2..].to_string(), Position { line: pos.line, col: pos.col + offset + 2 }),
        Some(_) if input[offset..].starts_with("for ") => (Token::For, input[offset + 4..].to_string(), Position { line: pos.line, col: pos.col + offset + 4 }),
        Some(_) if input[offset..].starts_with("in ") => (Token::In, input[offset + 3..].to_string(), Position { line: pos.line, col: pos.col + offset + 3 }),
        Some(_) if input[offset..].starts_with("..") => (Token::Dotdot, input[offset + 2..].to_string(), Position { line: pos.line, col: pos.col + offset + 2 }),
        Some(_) if input[offset..].starts_with("do ") || input[offset..].to_string() == "do" => (Token::Do, input[offset + 2..].to_string(), Position { line: pos.line, col: pos.col + offset + 2 }),
        Some(_) if input[offset..].starts_with("endfor ") || input[offset..].to_string() == "endfor" => (Token::For, input[offset + 6..].to_string(), Position { line: pos.line, col: pos.col + offset + 6 }),
        Some(x) => match x {
            '0'...'9' => parse_num(&input[offset..].to_string(), &Position { line: pos.line, col: pos.col + offset }),
            'a'...'z' | 'A'...'Z' => parse_ide(&input[offset..].to_string(), &Position { line: pos.line, col: pos.col + offset }),
            _ => (Token::Unknown(x.to_string()), input[offset + 1..].to_string(), Position { line: pos.line, col: pos.col + offset + 1 }),
        },
        None => (Token::Unknown("".to_string()), input[offset..].to_string(), Position { line: pos.line, col: pos.col + offset }),
    }
}

fn parse_then_else<T: Field>(cond: Condition<T>, input: &String, pos: &Position) -> Result<(Expression<T>, String, Position), Error<T>> {
    match next_token(input, pos) {
        (Token::Then, s5, p5) => match parse_expr(&s5, &p5) {
            Ok((e6, s6, p6)) => match next_token(&s6, &p6) {
                (Token::Else, s7, p7) => match parse_expr(&s7, &p7) {
                    Ok((e8, s8, p8)) => match next_token(&s8, &p8) {
                        (Token::Fi, s9, p9) => parse_expr1(Expression::IfElse(box cond, box e6, box e8), s9, p9),
                        (t10, _, p10) => Err(Error { expected: vec![Token::Fi], got: t10 , pos: p10 }),
                    },
                    Err(err) => Err(err),
                },
                (t7, _, p7) => Err(Error { expected: vec![Token::Else], got: t7 , pos: p7 }),
            },
            Err(err) => Err(err),
        },
        (t5, _, p5) => Err(Error { expected: vec![Token::Then], got: t5 , pos: p5 }),
    }
}

fn parse_if_then_else<T: Field>(input: &String, pos: &Position) -> Result<(Expression<T>, String, Position), Error<T>> {
    match next_token(input, pos) {
        (Token::If, s1, p1) => match parse_expr(&s1, &p1) {
            Ok((e2, s2, p2)) => match next_token(&s2, &p2) {
                (Token::Lt, s3, p3) => match parse_expr(&s3, &p3) {
                    Ok((e4, s4, p4)) => parse_then_else(Condition::Lt(e2, e4), &s4, &p4),
                    Err(err) => Err(err),
                },
                (Token::Le, s3, p3) => match parse_expr(&s3, &p3) {
                    Ok((e4, s4, p4)) => parse_then_else(Condition::Le(e2, e4), &s4, &p4),
                    Err(err) => Err(err),
                },
                (Token::Eqeq, s3, p3) => match parse_expr(&s3, &p3) {
                    Ok((e4, s4, p4)) => parse_then_else(Condition::Eq(e2, e4), &s4, &p4),
                    Err(err) => Err(err),
                },
                (Token::Ge, s3, p3) => match parse_expr(&s3, &p3) {
                    Ok((e4, s4, p4)) => parse_then_else(Condition::Ge(e2, e4), &s4, &p4),
                    Err(err) => Err(err),
                },
                (Token::Gt, s3, p3) => match parse_expr(&s3, &p3) {
                    Ok((e4, s4, p4)) => parse_then_else(Condition::Gt(e2, e4), &s4, &p4),
                    Err(err) => Err(err),
                },
                (t3, _, p3) => Err(Error { expected: vec![Token::Lt, Token::Le, Token::Eqeq, Token::Ge, Token::Gt], got: t3 , pos: p3 }),
            },
            Err(err) => Err(err),
        },
        (t1, _, p1) => Err(Error { expected: vec![Token::If], got: t1 , pos: p1 }),
    }
}

fn parse_factor1<T: Field>(expr: Expression<T>, input: String, pos: Position) -> Result<(Expression<T>, String, Position), Error<T>> {
    match parse_term1(expr.clone(), input.clone(), pos.clone()) {
        Ok((e1, s1, p1)) => match parse_expr1(e1, s1, p1) {
            Ok((e2, s2, p2)) => match next_token::<T>(&s2, &p2) {
                (Token::Pow, s3, p3) => match next_token(&s3, &p3) {
                    (Token::Num(x), s4, p4) => Ok((Expression::Pow(box e2, box Expression::Number(x)), s4, p4)),
                    (t4, _, p4) => Err(Error { expected: vec![Token::ErrNum], got: t4 , pos: p4 }),
                },
                _ => Ok((expr, input, pos)),
            },
            Err(err) => Err(err),
        },
        Err(err) => Err(err),
    }
}

fn parse_factor<T: Field>(input: &String, pos: &Position) -> Result<(Expression<T>, String, Position), Error<T>> {
    match next_token(input, pos) {
        (Token::If, ..) => parse_if_then_else(input, pos),
        (Token::Open, s1, p1) => match parse_expr(&s1, &p1) {
            Ok((e2, s2, p2)) => match next_token(&s2, &p2) {
                (Token::Close, s3, p3) => parse_factor1(e2, s3, p3),
                (t3, _, p3) => Err(Error { expected: vec![Token::Close], got: t3 , pos: p3 }),
            },
            Err(err) => Err(err),
        },
        (Token::Ide(x), s1, p1) => parse_factor1(Expression::Identifier(x), s1, p1),
        (Token::Num(x), s1, p1) => parse_factor1(Expression::Number(x), s1, p1),
        (t1, _, p1) => Err(Error { expected: vec![Token::If, Token::Open, Token::ErrIde, Token::ErrNum], got: t1 , pos: p1 }),
    }
}

fn parse_term1<T: Field>(expr: Expression<T>, input: String, pos: Position) -> Result<(Expression<T>, String, Position), Error<T>> {
    match next_token::<T>(&input, &pos) {
        (Token::Mult, s1, p1) => {
            match parse_term(&s1, &p1) {
                Ok((e, s2, p2)) => Ok((Expression::Mult(box expr, box e), s2, p2)),
                Err(err) => Err(err),
            }
        },
        (Token::Div, s1, p1) => {
            match parse_term(&s1, &p1) {
                Ok((e, s2, p2)) => Ok((Expression::Div(box expr, box e), s2, p2)),
                Err(err) => Err(err),
            }
        },
        _ => Ok((expr, input, pos)),
    }
}

fn parse_term<T: Field>(input: &String, pos: &Position) -> Result<(Expression<T>, String, Position), Error<T>> {
    match parse_factor(input, pos) {
        Ok((e, s1, p1)) => parse_term1(e, s1, p1),
        Err(err) => Err(err),
    }
}

fn parse_expr1<T: Field>(expr: Expression<T>, input: String, pos: Position) -> Result<(Expression<T>, String, Position), Error<T>> {
    match next_token::<T>(&input, &pos) {
        (Token::Add, s1, p1) => {
            match parse_term(&s1, &p1) {
                Ok((e2, s2, p2)) => parse_expr1(Expression::Add(box expr, box e2), s2, p2),
                Err(err) => Err(err),
            }
        },
        (Token::Sub, s1, p1) => {
            match parse_term(&s1, &p1) {
                Ok((e2, s2, p2)) => parse_expr1(Expression::Sub(box expr, box e2), s2, p2),
                Err(err) => Err(err),
            }
        },
        (Token::Pow, s1, p1) => {
            match parse_num(&s1, &p1) {
                (Token::Num(x), s2, p2) => match parse_term1(Expression::Pow(box expr, box Expression::Number(x)), s2, p2) {
                    Ok((e3, s3, p3)) => parse_expr1(e3, s3, p3),
                    Err(err) => Err(err),
                },
                (t2, _, p2) => Err(Error { expected: vec![Token::ErrNum], got: t2 , pos: p2 }),
            }
        },
        _ => Ok((expr, input, pos)),
    }
}

fn parse_expr<T: Field>(input: &String, pos: &Position) -> Result<(Expression<T>, String, Position), Error<T>> {
    match next_token::<T>(input, pos) {
        (Token::If, ..) => parse_if_then_else(input, pos),
        (Token::Open, s1, p1) => match parse_expr(&s1, &p1) {
            Ok((e2, s2, p2)) => match next_token(&s2, &p2) {
                (Token::Close, s3, p3) => match parse_term1(e2, s3, p3) {
                    Ok((e4, s4, p4)) => parse_expr1(e4, s4, p4),
                    Err(err) => Err(err),
                },
                (t3, _, p3) => Err(Error { expected: vec![Token::Close], got: t3 , pos: p3 }),
            },
            Err(err) => Err(err),
        },
        (Token::Ide(x), s1, p1) => {
            match parse_term1(Expression::Identifier(x), s1, p1) {
                Ok((e2, s2, p2)) => parse_expr1(e2, s2, p2),
                Err(err) => Err(err),
            }
        }
        (Token::Num(x), s1, p1) => {
            match parse_term1(Expression::Number(x), s1, p1) {
                Ok((e2, s2, p2)) => parse_expr1(e2, s2, p2),
                Err(err) => Err(err),
            }
        },
        (t1, _, p1) => Err(Error { expected: vec![Token::If, Token::Open, Token::ErrIde, Token::ErrNum], got: t1 , pos: p1 }),
    }
}

fn parse_statement1<T: Field>(ide: String, input: String, pos: Position) -> Result<(Statement<T>, String, Position), Error<T>> {
    match next_token::<T>(&input, &pos) {
        (Token::Eq, s1, p1) => match parse_expr(&s1, &p1) {
            Ok((e2, s2, p2)) => match next_token(&s2, &p2) {
                (Token::Unknown(ref t3), ref s3, _) if t3 == "" => {
                    assert_eq!(s3, "");
                    Ok((Statement::Definition(ide, e2), s2, p2))
                },
                (t3, _, p3) => Err(Error { expected: vec![Token::Add, Token::Sub, Token::Pow, Token::Mult, Token::Div, Token::Unknown("".to_string())], got: t3 , pos: p3 }),
            },
            Err(err) => Err(err),
        },
        _ => match parse_term1(Expression::Identifier(ide), input, pos) {
            Ok((e2, s2, p2)) => match parse_expr1(e2, s2, p2) {
                Ok((e3, s3, p3)) => match next_token(&s3, &p3) {
                    (Token::Eqeq, s4, p4) => match parse_expr(&s4, &p4) {
                        Ok((e5, s5, p5)) => match next_token(&s5, &p5) {
                            (Token::Unknown(ref t6), ref s6, _) if t6 == "" => {
                                assert_eq!(s6, "");
                                Ok((Statement::Condition(e3, e5), s5, p5))
                            },
                            (t6, _, p6) => Err(Error { expected: vec![Token::Add, Token::Sub, Token::Pow, Token::Mult, Token::Div, Token::Unknown("".to_string())], got: t6 , pos: p6 }),
                        },
                        Err(err) => Err(err),
                    },
                    (t4, _, p4) => Err(Error { expected: vec![Token::Eqeq], got: t4 , pos: p4 }),
                },
                Err(err) => Err(err),
            },
            Err(err) => Err(err),
        },
    }
}

fn parse_statement<T: Field>(lines: &mut Lines<BufReader<File>>, input: &String, pos: &Position) -> Result<(Statement<T>, String, Position), Error<T>> {
    match next_token::<T>(input, pos) {
        (Token::Ide(x1), s1, p1) => parse_statement1(x1, s1, p1),
        (Token::If, ..) |
        (Token::Open, ..) |
        (Token::Num(_), ..) => match parse_expr(input, pos) {
            Ok((e2, s2, p2)) => match next_token(&s2, &p2) {
                (Token::Eqeq, s3, p3) => match parse_expr(&s3, &p3) {
                    Ok((e4, s4, p4)) => match next_token(&s4, &p4) {
                        (Token::Unknown(ref t5), ref s5, _) if t5 == "" => {
                            assert_eq!(s5, "");
                            Ok((Statement::Condition(e2, e4), s4, p4))
                        },
                        (t5, _, p5) => Err(Error { expected: vec![Token::Unknown("".to_string())], got: t5 , pos: p5 }),
                    },
                    Err(err) => Err(err),
                },
                (t3, _, p3) => Err(Error { expected: vec![Token::Eqeq], got: t3 , pos: p3 }),
            },
            Err(err) => Err(err),
        },
        (Token::For, s1, p1) => match parse_ide(&s1, &p1) {
            (Token::Ide(x2), s2, p2) => match next_token(&s2, &p2) {
                (Token::In, s3, p3) => match next_token(&s3, &p3) {
                    (Token::Num(x4), s4, p4) => match next_token(&s4, &p4) {
                        (Token::Dotdot, s5, p5) => match next_token(&s5, &p5) {
                            (Token::Num(x6), s6, p6) => match next_token(&s6, &p6) {
                                (Token::Do, s7, p7) => {
                                    match next_token(&s7, &p7) {
                                        (Token::Unknown(ref t8), ref s8, _) if t8 == "" => {
                                            assert_eq!(s8, "");
                                        },
                                        (t8, _, p8) => return Err(Error { expected: vec![Token::Unknown("".to_string())], got: t8 , pos: p8 }),
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
                                                    (Token::Unknown(ref t9), ref s9, _) if t9 == "" => {
                                                        assert_eq!(s9, "");
                                                        return Ok((Statement::For(x2, x4, x6, statements), s8, p8))
                                                    },
                                                    (t9, _, p9) => return Err(Error { expected: vec![Token::Unknown("1432567iuhgvfc".to_string())], got: t9 , pos: p9 }),
                                                }
                                            },
                                            Some(Ok(ref x)) if !x.trim().starts_with("return") => match parse_statement(lines, x, &Position { line: current_line, col: 1 }) {
                                                Ok((statement, ..)) => statements.push(statement),
                                                Err(err) => return Err(err),
                                            },
                                            Some(Err(err)) => panic!("Error while reading Definitions: {}", err),
                                            Some(Ok(ref x)) => {
                                                let (t, ..) = next_token(x, &Position{ line: current_line, col: 1 });
                                                return Err(Error { expected: vec![Token::ErrIde, Token::ErrNum, Token::If, Token::Open, Token::Hash, Token::For, Token::Endfor], got: t , pos:  Position{ line: current_line, col: 1 } })
                                            },
                                            None => return Err(Error { expected: vec![Token::ErrIde, Token::ErrNum, Token::If, Token::Open, Token::Hash, Token::For], got: Token::Unknown("".to_string()) , pos:  Position{ line: current_line, col: 1 } }),
                                        }
                                    };
                                },
                                (t7, _, p7) => Err(Error { expected: vec![Token::Do], got: t7 , pos: p7 }),
                            },
                            (t6, _, p6) => Err(Error { expected: vec![Token::ErrNum], got: t6 , pos: p6 }),
                        },
                        (t5, _, p5) => Err(Error { expected: vec![Token::Dotdot], got: t5 , pos: p5 }),
                    },
                    (t4, _, p4) => Err(Error { expected: vec![Token::ErrNum], got: t4 , pos: p4 }),
                },
                (t3, _, p3) => Err(Error { expected: vec![Token::In], got: t3 , pos: p3 }),
            },
            (t2, _, p2) => Err(Error { expected: vec![Token::ErrIde], got: t2 , pos: p2 }),
        },
        (Token::Hash, s1, p1) => match parse_ide(&s1, &p1) {
            (Token::Ide(x2), s2, p2) => match next_token(&s2, &p2) {
                (Token::Eq, s3, p3) => match parse_expr(&s3, &p3) {
                    Ok((e4, s4, p4)) => Ok((Statement::Compiler(x2, e4), s4, p4)),
                    Err(err) => Err(err),
                },
                (t3, _, p3) => Err(Error { expected: vec![Token::Eq], got: t3 , pos: p3 }),
            },
            (t2, _, p2) => Err(Error { expected: vec![Token::ErrIde], got: t2 , pos: p2 }),
        },
        (Token::Return, s1, p1) => {
            match parse_expr(&s1, &p1) {
                Ok((expr, s2, p2)) => match next_token(&s2, &p2) {
                    (Token::Unknown(ref t3), ref s3, _) if t3 == "" => {
                        assert_eq!(s3, "");
                        Ok((Statement::Return(expr), s2, p2))
                    },
                    (t4, _, p4) => Err(Error { expected: vec![Token::Add, Token::Sub, Token::Pow, Token::Mult, Token::Div, Token::Unknown("".to_string())], got: t4 , pos: p4 }),
                },
                Err(err) => Err(err),
            }
        },
        (t1, _, p1) => Err(Error { expected: vec![Token::ErrIde, Token::ErrNum, Token::If, Token::Open, Token::Hash, Token::Return], got: t1 , pos: p1 }),
    }
}

pub fn parse_program<T: Field>(file: File) -> Result<Prog<T>, Error<T>> {
    let mut current_line = 1;
    let reader = BufReader::new(file);
    let mut lines = reader.lines();

    let id;
    let mut args = Vec::new();
    loop { // search and make Prog
        match lines.next() {
            Some(Ok(ref x)) if x.trim().starts_with("//") || x == "" => {},
            Some(Ok(ref x)) => match next_token(x, &Position { line: current_line, col: 1 }) {
                (Token::Ide(ref x1), ref s1, ref p1) if x1 == "def" => match next_token(s1, p1) {
                    (Token::Ide(x2), s2, p2) => {
                        id = x2;
                        match next_token(&s2, &p2) {
                            (Token::Open, s3, p3) => {
                                let mut s = s3;
                                let mut p = p3;
                                loop {
                                    match next_token(&s, &p) {
                                        (Token::Ide(x), s4, p4) => {
                                            args.push(Parameter { id: x });
                                            match next_token(&s4, &p4) {
                                                (Token::Comma, s5, p5) => {
                                                    s = s5;
                                                    p = p5;
                                                },
                                                (Token::Close, s4, p4) => {
                                                    match next_token(&s4, &p4) {
                                                        (Token::Colon, s5, p5) => {
                                                            match next_token(&s5, &p5) {
                                                                (Token::Unknown(ref x6), ..) if x6 == "" => break,
                                                                (t6, _, p6) => return Err(Error { expected: vec![Token::Unknown("".to_string())], got: t6 , pos: p6 }),
                                                            }
                                                        },
                                                        (t5, _, p5) => return Err(Error { expected: vec![Token::Colon], got: t5 , pos: p5 }),
                                                    }
                                                },
                                                (t5, _, p5) => return Err(Error { expected: vec![Token::Comma, Token::Close], got: t5 , pos: p5 }),
                                            }
                                        },
                                        (t4, _, p4) => return Err(Error { expected: vec![Token::Ide(String::from("ide"))], got: t4 , pos: p4 }),
                                    }
                                }
                                break;
                            },
                            (t3, _, p3) => return Err(Error { expected: vec![Token::Open], got: t3 , pos: p3 }),
                        }
                    },
                    (t2, _, p2) => return Err(Error { expected: vec![Token::Ide(String::from("name"))], got: t2 , pos: p2 }),
                },
                (t1, _, p1) => return Err(Error { expected: vec![Token::Ide(String::from("def"))], got: t1 , pos: p1 }),
            },
            Some(Err(err)) => panic!("Error while reading line {}: {:?}", current_line, err),
            None => return Err(Error { expected: vec![Token::Ide(String::from("def"))], got: Token::Unknown(String::from("")) , pos: Position { line: current_line, col: 1 } }),
        }
        current_line += 1;
    };
    current_line += 1;

    let mut defs = Vec::new();
    let mut got_return = false;
    loop {
        match lines.next() {
            Some(Ok(ref x)) if x.trim().starts_with("//") || x.trim() == "" => {}, // skip
            Some(Ok(ref x)) => match parse_statement(&mut lines, x, &Position { line: current_line, col: 1 }) {
                Ok((statement @ Statement::Return(_), ..)) => {
                    if !got_return {
                        got_return = true;
                        defs.push(statement)
                    } else {
                        return Err(Error { expected: vec![], got: Token::Return , pos: Position { line: current_line, col: 1 + skip_whitespaces(x) + Token::Return::<T>.to_string().len() } })
                    }
                },
                Ok((statement, ..)) => defs.push(statement),
                Err(err) => return Err(err),
            },
            None => break,
            Some(Err(err)) => panic!("Error while reading Definitions: {}", err),
        }
        current_line += 1;
    }

    match defs.last() {
        Some(&Statement::Return(_)) => {},
        Some(x) => panic!("Last definition not Return: {}", x),
        None => panic!("Error while checking last definition"),
    }
    Ok(Prog { id: id, arguments: args, statements: defs })
}

#[cfg(test)]
mod tests {
    use super::*;
    use field::FieldPrime;

    // Position.col()
    #[test]
    fn position_col() {
        let pos = Position { line: 100, col: 258 };
        assert_eq!(pos.col(26), Position { line: 100, col: 284 });
        assert_eq!(pos.col(-23), Position { line: 100, col: 235 });
    }

    #[cfg(test)]
    mod parse_num {
        use super::*;

        #[test]
        fn single() {
            let pos = Position { line: 45, col: 121 };
            assert_eq!(
                (Token::Num(FieldPrime::from(12234)), String::from(""), pos.col(5)),
                parse_num(&"12234".to_string(), &pos)
            );
        }

        #[test]
        fn add() {
            let pos = Position { line: 45, col: 121 };
            assert_eq!(
                (Token::Num(FieldPrime::from(354)), String::from("+879"), pos.col(3)),
                parse_num(&"354+879".to_string(), &pos)
            );
        }

        #[test]
        fn space_after() {
            let pos = Position { line: 45, col: 121 };
            assert_eq!(
                (Token::Num(FieldPrime::from(354)), String::from(" "), pos.col(3)),
                parse_num(&"354 ".to_string(), &pos)
            );
        }

        #[test]
        #[should_panic]
        fn space_before() {
            let pos = Position { line: 45, col: 121 };
            parse_num::<FieldPrime>(&" 354".to_string(), &pos);
        }

        #[test]
        #[should_panic]
        fn x_before() {
            let pos = Position { line: 45, col: 121 };
            parse_num::<FieldPrime>(&"x324312".to_string(), &pos);
        }
    }

    // parse_ide
    // skip_whitespaces
    // next_token
    // parse_if_then_else
    #[test]
    fn parse_if_then_else_ok() {
        let pos = Position { line: 45, col: 121 };
        let string = String::from("if a < b then c else d fi");
        let expr = Expression::IfElse::<FieldPrime>(
            box Condition::Lt(Expression::Identifier(String::from("a")), Expression::Identifier(String::from("b"))),
            box Expression::Identifier(String::from("c")),
            box Expression::Identifier(String::from("d"))
        );
        assert_eq!(
            Ok((expr, String::from(""), pos.col(string.len() as isize))),
            parse_if_then_else(&string, &pos)
        );
    }

    // parse_factor1

    #[cfg(test)]
    mod parse_factor {
        use super::*;
        #[test]
        fn if_then_else() {
            let pos = Position { line: 45, col: 121 };
            let string = String::from("if a < b then c else d fi");
            let expr = Expression::IfElse::<FieldPrime>(
                box Condition::Lt(Expression::Identifier(String::from("a")), Expression::Identifier(String::from("b"))),
                box Expression::Identifier(String::from("c")),
                box Expression::Identifier(String::from("d"))
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
                box Expression::Mult(box Expression::Identifier(String::from("a")), box Expression::Number(FieldPrime::from(6)))
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

    // parse_term1
    // parse_term
    // parse_expr1
    // parse_expr
    // parse_statement
    // parse_program
    // #[should_panic(expected = "assertion failed")]
}
