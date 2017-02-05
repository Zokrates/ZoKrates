extern crate regex;

use std::fmt;
use std::io::BufReader;
use std::io::prelude::*;
use std::fs::File;
use self::regex::Regex;
use absy::*;

#[derive(Clone)]
struct Position {
    line: usize,
    col: usize
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

enum Token {
    Open, Close, Eq, Return,
    If, Then, Else, Fi,
    Lt, Le, Eqeq, Ge, Gt,
    Add, Sub, Mult, Div, Pow,
    Ide(String),
    Num(i32),
}
impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Token::Open => write!(f, "("),
            Token::Close => write!(f, ")"),
            Token::Eq => write!(f, "="),
            Token::Return => write!(f, "return"),
            Token::If => write!(f, "if"),
            Token::Then => write!(f, "then"),
            Token::Else => write!(f, "else"),
            Token::Fi => write!(f, "fi"),
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
        }
    }
}
impl fmt::Debug for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

fn skip_whitespaces(input: &String) -> usize {
    let mut i = 0;
    loop {
        match input.chars().nth(i) {
            Some(' ') | Some('\t') => i += 1,
            Some(_) | None => return i,
            _ => panic!("what now?"), // TODO NONE?
        }
    }
}

fn get_next_whitespace(input: &String) -> usize {
    let mut i = 0;
    loop {
        match input.chars().nth(i) {
            Some(' ') | Some('\t') | Some('\n') | None => return i,
            Some(_) => i += 1,
        }
    }
}

fn parse_num(input: &String, pos: Position) -> (Token, String, Position) {
    let end = get_next_whitespace(input);
    (Token::Num(input[0..end].parse().unwrap()), input[end..].to_string(), Position { line: pos.line, col: pos.col + end })
}

fn parse_ide(input: &String, pos: Position) -> (Token, String, Position) {
    let end = get_next_whitespace(input);
    (Token::Ide(input[0..end].to_string()), input[end..].to_string(), Position { line: pos.line, col: pos.col + end })
}

fn next_token(input: &String, pos: Position) -> Option<(Token, String, Position)> {
    let offset = skip_whitespaces(input);
    Some(match input.chars().nth(offset) {
        Some('(') => (Token::Open, input[offset + 1..].to_string(), Position { line: pos.line, col: pos.col + offset + 1 }),
        Some(')') => (Token::Close, input[offset + 1..].to_string(), Position { line: pos.line, col: pos.col + offset + 1 }),
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
        Some(_) if input[offset..].starts_with("if ") => panic!("Got if"),
        Some(_) if input[offset..].starts_with("then ") => panic!("Got then"),
        Some(_) if input[offset..].starts_with("else ") => panic!("Got else"),
        Some(_) if input[offset..].starts_with("fi ") => panic!("Got fi"),
        Some(x) => match x {
            '0'...'9' => parse_num(&input[offset..].to_string(), Position { line: pos.line, col: pos.col + offset }),
            'a'...'z' | 'A'...'Z' => parse_ide(&input[offset..].to_string(), Position { line: pos.line, col: pos.col + offset }),
            _ => panic!("unexpected"),
        },
        None => return None,
        e @ _ => panic!("not implemented for: {:?}", e),
    })
}

// TODO is TEST IMPL
fn parse_factor1(expr: Expression, input: String, pos: Position) -> Result<(Expression, String, Position), String> {
    match parse_term1(expr.clone(), input.clone(), pos.clone()) {
        Ok((e1 @ _, s1 @ _, p1 @ _)) => match parse_expr1(e1, s1, p1) {
            Ok((e2 @ _, s2 @ _, p2 @ _)) => match next_token(&s2, p2) {
                Some((Token::Pow, s3 @ _, p3 @ _)) => match next_token(&s3, p3.clone()) {
                    Some((Token::Num(x), s4 @ _, p4 @ _)) => Ok((Expression::Pow(box e2, box Expression::NumberLiteral(x)), s4, p4)),
                    e @ _ => Err(format!("Exprected number at {}, got: {:?}", p3, e)),
                },
                _ => Ok((expr, input, pos)),
            },
            Err(why) => Err(why),
        },
        Err(why) => Err(why),
    }
}

fn parse_factor(input: String, pos: Position) -> Result<(Expression, String, Position), String> {
    match next_token(&input, pos.clone()) {
        Some((Token::If, s1 @ _, p1 @ _)) => {
            unimplemented!()
        },
        Some((Token::Open, s1 @ _, p1 @ _)) => {
            unimplemented!()
        },
        Some((Token::Ide(x), s1 @ _, p1 @ _)) => parse_factor1(Expression::VariableReference(x), s1, p1),
        Some((Token::Num(x), s1 @ _, p1 @ _)) => parse_factor1(Expression::NumberLiteral(x), s1, p1),
        e @ _ => Err(format!("expected one of `if`, `(`, variable or a number, found {:?}\n\tat {}", e, pos)),
    }
}

fn parse_term(input: String, pos: Position) -> Result<(Expression, String, Position), String> {
    println!("parse_term ({}, {})", &input, &pos);
    match parse_factor(input, pos) {
        Ok((e @ _, s1 @ _, p1 @ _)) => parse_term1(e, s1, p1),
        e @ Err(_) => e,
    }
}

fn parse_term1(expr: Expression, input: String, pos: Position) -> Result<(Expression, String, Position), String> {
    println!("parse_term1 ({}, {}, {})", expr, &input, &pos);
    match next_token(&input, pos.clone()) {
        Some((Token::Mult, s1 @ _, p1 @ _)) => {
            match parse_term(s1, p1) {
                Ok((e @ _, s2 @ _, p2 @ _)) => Ok((Expression::Mult(box expr, box e), s2, p2)),
                Err(why) => Err(why),
            }
        },
        Some((Token::Div, s1 @ _, p1 @ _)) => {
            match parse_term(s1, p1) {
                Ok((e @ _, s2 @ _, p2 @ _)) => Ok((Expression::Div(box expr, box e), s2, p2)),
                Err(why) => Err(why),
            }
        },
        _ => Ok((expr, input, pos)),
    }
}

fn parse_expr1(expr: Expression, input: String, pos: Position) -> Result<(Expression, String, Position), String> {
    println!("parse_expr1 ({}, {}, {})", expr, &input, &pos);
    match next_token(&input, pos.clone()) {
        Some((Token::Add, s1 @ _, p1 @ _)) => {
            // match parse_term(s1, p1) {
            match parse_expr(s1, p1) {
                Ok((e @ _, s2 @ _, p2 @ _)) => Ok((Expression::Add(box expr, box e), s2, p2)),
                Err(why) => Err(why),
            }
        },
        Some((Token::Sub, s1 @ _, p1 @ _)) => {
            // match parse_term(s1, p1) {
            match parse_expr(s1, p1) {
                Ok((e @ _, s2 @ _, p2 @ _)) => Ok((Expression::Sub(box expr, box e), s2, p2)),
                Err(why) => Err(why),
            }
        },
        Some((Token::Pow, s1 @ _, p1 @ _)) => {
            unimplemented!()
        },
        // _ => Ok((expr, input, pos)),
        e @ _ => {
            println!("parse_expr1 foud EPSILON, cause: {:?}", e);
            Ok((expr, input, pos))
        },
    }
}

fn parse_expr(input: String, pos: Position) -> Result<(Expression, String, Position), String> {
    println!("parse_expr ({}, {})", &input, &pos);
    match next_token(&input, pos) {
        Some((Token::If, s1 @ _, p1 @ _)) => {
            unimplemented!()
        },
        Some((Token::Open, s1 @ _, p1 @ _)) => {
            unimplemented!()
        },
        Some((Token::Ide(x), s1 @ _, p1 @ _)) => {
            match parse_term1(Expression::VariableReference(x), s1, p1) {
                Ok((e @ _, s2 @ _, p2 @ _)) => parse_expr1(e, s2, p2),
                Err(why) => Err(why),
            }
        }
        Some((Token::Num(x), s1 @ _, p1 @ _)) => {
            match parse_term1(Expression::NumberLiteral(x), s1, p1) {
                Ok((e @ _, s2 @ _, p2 @ _)) => parse_expr1(e, s2, p2),
                Err(why) => Err(why),
            }
        },
        _ => panic!("unexpected"),
    }
}

fn parse_statement(input: &String, pos: Position) -> Result<(Statement, String, Position), String> {
    match next_token(input, pos) {
        Some((Token::Ide(x), s1 @ _, p1 @ _)) => {
            // let Ok(ide, s1, p1) = parse_ide(input, pos);
            match next_token(&s1, p1) {
                Some((Token::Eq, s2, p2)) => match parse_expr(s2, p2) {
                    Ok((expr, s3, p3)) => Ok((Statement::Definition(x, expr), s3, p3)),
                    Err(e) => Err(e),
                },
                Some((t, _, p2)) => Err(format!("Expected '=' at {}, got: '{}'", p2, t)),
                None => panic!("unexpected"),
            }
        },
        Some((Token::Return, s1 @ _, p1 @ _)) => {
            match parse_expr(s1, p1) {
                Ok((expr, s, p)) => {
                    assert_eq!(s, "");
                    Ok((Statement::Return(expr), s, p))
                },
                Err(e) => Err(e),
            }
        },
        e @ _ => Err(format!("Error parsing statement, got: {:?}", e)),
    }
}

pub fn parse_program(file: File) -> Result<Prog, String> {
    let mut current_line = 0;
    let reader = BufReader::new(file);
    let mut lines = reader.lines();

    // TODO def parse old
    let id;
    let args;
    let def_regex = Regex::new(r"^def\s(?P<id>\D[a-zA-Z0-9]+)\(\s*([a-z]+)(,\s*[a-z]+)*\s*\):$").unwrap();
    let args_regex = Regex::new(r"\(\s*(?P<args>[a-z]+(,\s*[a-z]+)*)\s*\)").unwrap();
    loop { // search and make Prog
        match lines.next() {
            Some(Ok(ref x)) if x.starts_with("def") => {
                id = match def_regex.captures(x) {
                    Some(x) => x["id"].to_string(),
                    None => panic!("Wrong definition of function"),
                };
                args = match args_regex.captures(x) {
                    Some(x) => x["args"].replace(" ", "").replace("\t", "").split(",")
                                        .map(|p| Parameter { id: p.to_string() })
                                        .collect::<Vec<_>>(),
                    None => panic!("Wrong argument definition in function: {}", id),
                };
                break;
            },
            Some(Ok(ref x)) if x.trim().starts_with("//") || x == "" => {},
            None => panic!("End of file reached without function def"),
            Some(x) => panic!("Found '{:?}' outside of function", x),
        }
        current_line += 1;
    };

    let mut defs = Vec::new();
    loop {
        match lines.next() {
            Some(Ok(ref x)) => match parse_statement(x, Position { line: current_line, col: 0 }) {
                Ok((statement, ..)) => {
                    println!("statement {}", &statement);
                    defs.push(statement)
                },
                Err(e) => panic!("Error: {}", e),
            },
            None => break,
            Some(Err(e)) => panic!("Error while reading Definitions: {}", e),
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
