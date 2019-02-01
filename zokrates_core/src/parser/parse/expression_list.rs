use zokrates_field::field::Field;

use parser::tokenize::{next_token, Position, Token};
use parser::Error;

use super::expression::parse_expr;

use absy::{ExpressionList, ExpressionListNode, Node};

// parse an expression list
pub fn parse_expression_list<T: Field>(
    input: String,
    pos: Position,
) -> Result<(ExpressionListNode<T>, String, Position), Error<T>> {
    let mut res = ExpressionList::new();
    parse_comma_separated_expression_list_rec(input, pos, &mut res)
}

fn parse_comma_separated_expression_list_rec<T: Field>(
    input: String,
    pos: Position,
    mut acc: &mut ExpressionList<T>,
) -> Result<(ExpressionListNode<T>, String, Position), Error<T>> {
    match parse_expr(&input, &pos) {
        Ok((e1, s1, p1)) => {
            acc.expressions.push(e1);
            match next_token::<T>(&s1, &p1) {
                (Token::Comma, s2, p2) => {
                    parse_comma_separated_expression_list_rec(s2, p2, &mut acc)
                }
                (..) => Ok((Node::new(pos, p1, acc.clone()), s1, p1)),
            }
        }
        Err(err) => Err(err),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use absy::Expression;
    use zokrates_field::field::FieldPrime;

    fn parse_comma_separated_list<T: Field>(
        input: String,
        pos: Position,
    ) -> Result<(ExpressionListNode<T>, String, Position), Error<T>> {
        let mut res = ExpressionList::new().into();
        parse_comma_separated_expression_list_rec(input, pos, &mut res)
    }

    #[test]
    fn comma_separated_list() {
        let pos = Position { line: 45, col: 121 };
        let string = String::from("b, c");
        let expr = ExpressionList::<FieldPrime> {
            expressions: vec![
                Expression::Identifier(String::from("b")).into(),
                Expression::Identifier(String::from("c")).into(),
            ],
        }
        .into();
        assert_eq!(
            Ok((expr, String::from(""), pos.col(string.len() as isize))),
            parse_expression_list(string, pos)
        )
    }

    #[test]
    fn comma_separated_list_single() {
        let pos = Position { line: 45, col: 121 };
        let string = String::from("a");
        let exprs = ExpressionList {
            expressions: vec![Expression::Identifier(String::from("a")).into()],
        }
        .into();
        assert_eq!(
            Ok((exprs, String::from(""), pos.col(string.len() as isize))),
            parse_comma_separated_list::<FieldPrime>(string, pos)
        )
    }

    #[test]
    fn comma_separated_list_three() {
        let pos = Position { line: 45, col: 121 };
        let string = String::from("a, b, c");
        let exprs = ExpressionList {
            expressions: vec![
                Expression::Identifier(String::from("a")).into(),
                Expression::Identifier(String::from("b")).into(),
                Expression::Identifier(String::from("c")).into(),
            ],
        }
        .into();
        assert_eq!(
            Ok((exprs, String::from(""), pos.col(string.len() as isize))),
            parse_comma_separated_list::<FieldPrime>(string, pos)
        )
    }
}
