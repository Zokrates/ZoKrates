use zokrates_field::field::Field;

use parser::tokenize::{next_token, Position, Token};
use parser::Error;

use parser::tokenize::parse_quoted_path;

use absy::Node;
use imports::{Import, ImportNode};

pub fn parse_import<T: Field>(
    input: &String,
    pos: &Position,
) -> Result<(ImportNode, Position), Error<T>> {
    match next_token(input, pos) {
        (Token::DoubleQuote, s1, p1) => match parse_quoted_path(&s1, &p1) {
            (Token::Path(code_path), s2, p2) => match next_token::<T>(&s2, &p2) {
                (Token::As, s3, p3) => match next_token(&s3, &p3) {
                    (Token::Ide(id), _, p4) => {
                        return Ok((
                            Node::new(*pos, p4, Import::new_with_alias(code_path, &id)),
                            p4,
                        ));
                    }
                    (t4, _, p4) => {
                        return Err(Error {
                            expected: vec![Token::Ide("ide".to_string())],
                            got: t4,
                            pos: p4,
                        });
                    }
                },
                (Token::Unknown(_), _, p3) => {
                    return Ok((Node::new(*pos, p3, Import::new(code_path)), p3));
                }
                (t3, _, p3) => {
                    return Err(Error {
                        expected: vec![
                            Token::Ide("id".to_string()),
                            Token::Unknown("".to_string()),
                        ],
                        got: t3,
                        pos: p3,
                    });
                }
            },
            (t2, _, p2) => Err(Error {
                expected: vec![Token::Path("./path/to/program.code".to_string())],
                got: t2,
                pos: p2,
            }),
        },
        (t1, _, p1) => Err(Error {
            expected: vec![Token::DoubleQuote],
            got: t1,
            pos: p1,
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn quoted_path() {
        let pos = Position { line: 45, col: 121 };
        let string = String::from("./foo.code\" as foo");
        let path: Token<FieldPrime> = Token::Path("./foo.code".to_string());
        assert_eq!(
            (path, " as foo".to_string(), pos.col(11 as isize)),
            parse_quoted_path(&string, &pos)
        );
    }

    #[test]
    fn import() {
        let pos = Position { line: 45, col: 121 };
        let string = String::from("import \"./foo.code\"");
        let import: Token<FieldPrime> = Token::Import;
        assert_eq!(
            (import, " \"./foo.code\"".to_string(), pos.col(6 as isize)),
            next_token(&string, &pos)
        )
    }

    #[test]
    fn parse_import_test() {
        let pos = Position { line: 45, col: 121 };
        let string = String::from("\"./foo.code\"");
        let import = Import::new("./foo.code".to_string()).into();
        let position = Position {
            line: 45,
            col: pos.col + 1 + "./foo.code".len() + 1,
        };
        assert_eq!(
            Ok((import, position)),
            parse_import::<FieldPrime>(&string, &pos)
        )
    }

    #[test]
    fn parse_import_with_alias_test() {
        let pos = Position { line: 45, col: 121 };
        let string = String::from("\"./foo.code\" as myalias");
        let alias = "myalias".to_string();
        let import = Import::new_with_alias("./foo.code".to_string(), &alias).into();
        let position = Position {
            line: 45,
            col: pos.col + string.len(),
        };
        assert_eq!(
            Ok((import, position)),
            parse_import::<FieldPrime>(&string, &pos)
        )
    }
}
