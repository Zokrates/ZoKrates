use super::position::Position;
use super::token::Token;
use types::Type;
use zokrates_field::field::Field;

pub fn parse_num<T: Field>(input: &String, pos: &Position) -> (Token<T>, String, Position) {
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
    (
        Token::Num(T::try_from_str(&input[0..end]).unwrap()),
        input[end..].to_string(),
        Position {
            line: pos.line,
            col: pos.col + end,
        },
    )
}

pub fn parse_ide<T: Field>(input: &String, pos: &Position) -> (Token<T>, String, Position) {
    assert!(match input.chars().next().unwrap() {
        'a'...'z' | 'A'...'Z' => true,
        _ => false,
    });
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

    let token = match &input[0..end] {
        "import" => Token::Import,
        "as" => Token::As,
        "if" => Token::If,
        "then" => Token::Then,
        "else" => Token::Else,
        "fi" => Token::Fi,
        "for" => Token::For,
        "in" => Token::In,
        "do" => Token::Do,
        "endfor" => Token::Endfor,
        "private" => Token::Private,
        "def" => Token::Def,
        "return" => Token::Return,
        "field" => match input.chars().nth(end) {
            Some('[') => {
                let size_start = end + 1;
                let mut size_len = 0;
                loop {
                    match input.chars().nth(size_start + size_len) {
                        Some(x) => match x {
                            '0'...'9' => size_len += 1,
                            _ => break,
                        },
                        None => break,
                    }
                }
                assert!(size_len > 0);
                let size_end = size_start + size_len;
                match input.chars().nth(size_end) {
                    Some(']') => {
                        end = size_end + 1;
                        Token::Type(Type::FieldElementArray(
                            input[size_start..(size_start + size_len)]
                                .parse::<usize>()
                                .unwrap(),
                        ))
                    }
                    _ => panic!(),
                }
            }
            _ => Token::Type(Type::FieldElement),
        },
        "bool" => Token::Type(Type::Boolean),
        _ => Token::Ide(input[0..end].to_string()),
    };

    (
        token,
        input[end..].to_string(),
        Position {
            line: pos.line,
            col: pos.col + end,
        },
    )
}

pub fn skip_whitespaces(input: &String) -> usize {
    let mut i = 0;
    loop {
        match input.chars().nth(i) {
            Some(' ') | Some('\t') => i += 1,
            _ => return i,
        }
    }
}

pub fn parse_quoted_path<T: Field>(input: &String, pos: &Position) -> (Token<T>, String, Position) {
    let mut end = 0;
    loop {
        match input.chars().nth(end) {
            Some(x) => {
                end += 1;
                match x {
                    '\"' => break,
                    _ => continue,
                }
            }
            None => panic!("Invalid import path, should end with '\"'"),
        }
    }
    (
        Token::Path(input[0..end - 1].to_string()),
        input[end..].to_string(),
        Position {
            line: pos.line,
            col: pos.col + end,
        },
    )
}

pub fn next_token<T: Field>(input: &String, pos: &Position) -> (Token<T>, String, Position) {
    let offset = skip_whitespaces(input);
    match input.chars().nth(offset) {
        Some('(') => (
            Token::Open,
            input[offset + 1..].to_string(),
            Position {
                line: pos.line,
                col: pos.col + offset + 1,
            },
        ),
        Some(')') => (
            Token::Close,
            input[offset + 1..].to_string(),
            Position {
                line: pos.line,
                col: pos.col + offset + 1,
            },
        ),
        Some(',') => (
            Token::Comma,
            input[offset + 1..].to_string(),
            Position {
                line: pos.line,
                col: pos.col + offset + 1,
            },
        ),
        Some(':') => (
            Token::Colon,
            input[offset + 1..].to_string(),
            Position {
                line: pos.line,
                col: pos.col + offset + 1,
            },
        ),
        Some('#') => (
            Token::Hash,
            input[offset + 1..].to_string(),
            Position {
                line: pos.line,
                col: pos.col + offset + 1,
            },
        ),
        Some('=') => match input.chars().nth(offset + 1) {
            Some('=') => (
                Token::Eqeq,
                input[offset + 2..].to_string(),
                Position {
                    line: pos.line,
                    col: pos.col + offset + 2,
                },
            ),
            _ => (
                Token::Eq,
                input[offset + 1..].to_string(),
                Position {
                    line: pos.line,
                    col: pos.col + offset + 1,
                },
            ),
        },
        Some('<') => match input.chars().nth(offset + 1) {
            Some('=') => (
                Token::Le,
                input[offset + 2..].to_string(),
                Position {
                    line: pos.line,
                    col: pos.col + offset + 2,
                },
            ),
            _ => (
                Token::Lt,
                input[offset + 1..].to_string(),
                Position {
                    line: pos.line,
                    col: pos.col + offset + 1,
                },
            ),
        },
        Some('>') => match input.chars().nth(offset + 1) {
            Some('=') => (
                Token::Ge,
                input[offset + 2..].to_string(),
                Position {
                    line: pos.line,
                    col: pos.col + offset + 2,
                },
            ),
            _ => (
                Token::Gt,
                input[offset + 1..].to_string(),
                Position {
                    line: pos.line,
                    col: pos.col + offset + 1,
                },
            ),
        },
        Some('&') => match input.chars().nth(offset + 1) {
            Some('&') => (
                Token::And,
                input[offset + 2..].to_string(),
                Position {
                    line: pos.line,
                    col: pos.col + offset + 2,
                },
            ),
            _ => (
                Token::Unknown(String::from("&")),
                input[offset + 1..].to_string(),
                Position {
                    line: pos.line,
                    col: pos.col + offset + 1,
                },
            ),
        },
        Some('|') => match input.chars().nth(offset + 1) {
            Some('|') => (
                Token::Or,
                input[offset + 2..].to_string(),
                Position {
                    line: pos.line,
                    col: pos.col + offset + 2,
                },
            ),
            _ => (
                Token::Unknown(String::from("|")),
                input[offset + 1..].to_string(),
                Position {
                    line: pos.line,
                    col: pos.col + offset + 1,
                },
            ),
        },
        Some('!') => (
            Token::Not,
            input[offset + 1..].to_string(),
            Position {
                line: pos.line,
                col: pos.col + offset + 1,
            },
        ),
        Some('+') => (
            Token::Add,
            input[offset + 1..].to_string(),
            Position {
                line: pos.line,
                col: pos.col + offset + 1,
            },
        ),
        Some('-') => match input.chars().nth(offset + 1) {
            Some('>') => (
                Token::Arrow,
                input[offset + 2..].to_string(),
                Position {
                    line: pos.line,
                    col: pos.col + offset + 2,
                },
            ),
            _ => (
                Token::Sub,
                input[offset + 1..].to_string(),
                Position {
                    line: pos.line,
                    col: pos.col + offset + 1,
                },
            ),
        },
        Some('"') => (
            Token::DoubleQuote,
            input[offset + 1..].to_string(),
            Position {
                line: pos.line,
                col: pos.col + offset + 1,
            },
        ),
        Some('*') => match input.chars().nth(offset + 1) {
            Some('*') => (
                Token::Pow,
                input[offset + 2..].to_string(),
                Position {
                    line: pos.line,
                    col: pos.col + offset + 2,
                },
            ),
            _ => (
                Token::Mult,
                input[offset + 1..].to_string(),
                Position {
                    line: pos.line,
                    col: pos.col + offset + 1,
                },
            ),
        },
        Some('[') => (
            Token::LeftBracket,
            input[offset + 1..].to_string(),
            Position {
                line: pos.line,
                col: pos.col + offset + 1,
            },
        ),
        Some(']') => (
            Token::RightBracket,
            input[offset + 1..].to_string(),
            Position {
                line: pos.line,
                col: pos.col + offset + 1,
            },
        ),
        Some('/') => match input.chars().nth(offset + 1) {
            Some('/') => (
                Token::InlineComment(input[offset + 2..].to_string()),
                "".to_string(),
                Position {
                    line: pos.line,
                    col: pos.col + offset + input[offset + 2..].len(),
                },
            ),
            _ => (
                Token::Div,
                input[offset + 1..].to_string(),
                Position {
                    line: pos.line,
                    col: pos.col + offset + 1,
                },
            ),
        },
        Some(_) if input[offset..].starts_with("..") => (
            Token::Dotdot,
            input[offset + 2..].to_string(),
            Position {
                line: pos.line,
                col: pos.col + offset + 2,
            },
        ),
        Some(x) => match x {
            '0'...'9' => parse_num(
                &input[offset..].to_string(),
                &Position {
                    line: pos.line,
                    col: pos.col + offset,
                },
            ),
            'a'...'z' | 'A'...'Z' => parse_ide(
                &input[offset..].to_string(),
                &Position {
                    line: pos.line,
                    col: pos.col + offset,
                },
            ),
            _ => (
                Token::Unknown(x.to_string()),
                input[offset + 1..].to_string(),
                Position {
                    line: pos.line,
                    col: pos.col + offset + 1,
                },
            ),
        },
        None => (
            Token::Unknown("".to_string()),
            input[offset..].to_string(),
            Position {
                line: pos.line,
                col: pos.col + offset,
            },
        ),
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn inline_comment() {
        let pos = Position {
            line: 100,
            col: 258,
        };
        let (token, _, _) = next_token::<FieldPrime>(&" //inline comment".to_string(), &pos);
        assert_eq!(Token::InlineComment("inline comment".to_string()), token);
    }

    mod types {
        use super::*;

        #[test]
        fn field() {
            let pos = Position { line: 45, col: 121 };
            assert_eq!(
                (
                    Token::Type::<FieldPrime>(Type::FieldElement),
                    String::from(""),
                    pos.col(5)
                ),
                parse_ide(&"field".to_string(), &pos)
            );
        }

        #[test]
        fn field_array() {
            let pos = Position { line: 45, col: 121 };
            assert_eq!(
                (
                    Token::Type::<FieldPrime>(Type::FieldElementArray(123)),
                    String::from(" "),
                    pos.col(10)
                ),
                parse_ide(&"field[123] ".to_string(), &pos)
            );
        }

        #[test]
        fn field_array_2() {
            let pos = Position { line: 45, col: 121 };
            assert_eq!(
                (
                    Token::Type::<FieldPrime>(Type::FieldElementArray(1)),
                    String::from(" "),
                    pos.col(8)
                ),
                parse_ide(&"field[1] ".to_string(), &pos)
            );
        }

        #[should_panic]
        #[test]
        fn field_array_no_size() {
            let pos = Position { line: 45, col: 121 };
            parse_ide::<FieldPrime>(&"field[] ".to_string(), &pos);
        }

        #[should_panic]
        #[test]
        fn field_array_unclosed() {
            let pos = Position { line: 45, col: 121 };
            parse_ide::<FieldPrime>(&"field[123 ".to_string(), &pos);
        }

        #[should_panic]
        #[test]
        fn field_array_empty_unclosed() {
            let pos = Position { line: 45, col: 121 };
            parse_ide::<FieldPrime>(&"field[ ".to_string(), &pos);
        }

        #[test]
        fn field_array_empty_unopened() {
            let pos = Position { line: 45, col: 121 };
            assert_eq!(
                (
                    Token::Type::<FieldPrime>(Type::FieldElement),
                    String::from("] "),
                    pos.col(5)
                ),
                parse_ide::<FieldPrime>(&"field] ".to_string(), &pos)
            );
        }
    }

    mod parse_num {
        use super::*;

        #[test]
        fn single() {
            let pos = Position { line: 45, col: 121 };
            assert_eq!(
                (
                    Token::Num(FieldPrime::from(12234)),
                    String::from(""),
                    pos.col(5)
                ),
                parse_num(&"12234".to_string(), &pos)
            );
        }

        #[test]
        fn add() {
            let pos = Position { line: 45, col: 121 };
            assert_eq!(
                (
                    Token::Num(FieldPrime::from(354)),
                    String::from("+879"),
                    pos.col(3)
                ),
                parse_num(&"354+879".to_string(), &pos)
            );
        }

        #[test]
        fn space_after() {
            let pos = Position { line: 45, col: 121 };
            assert_eq!(
                (
                    Token::Num(FieldPrime::from(354)),
                    String::from(" "),
                    pos.col(3)
                ),
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
}
