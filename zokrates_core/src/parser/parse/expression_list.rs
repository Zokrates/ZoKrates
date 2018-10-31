use field::Field;

use parser::Error;
use parser::tokenize::{Token, Position, next_token};

use super::expression::parse_expr;

use absy::ExpressionList;

// parse an expression list
pub fn parse_expression_list<T: Field>(
    input: String,
    pos: Position,
) -> Result<(ExpressionList<T>, String, Position), Error<T>> {
    let mut res = ExpressionList::new();
    parse_comma_separated_expression_list_rec(input, pos, &mut res)
}

fn parse_comma_separated_expression_list_rec<T: Field>(
    input: String, 
    pos: Position,
    mut acc: &mut ExpressionList<T>
) -> Result<(ExpressionList<T>, String, Position), Error<T>> {
    match parse_expr(&input, &pos) {
        Ok((e1, s1, p1)) => {
            acc.expressions.push(e1);
            match next_token::<T>(&s1, &p1) {
                (Token::Comma, s2, p2) => parse_comma_separated_expression_list_rec(s2, p2, &mut acc),
                (..) => Ok((acc.clone(), s1, p1)),
            }                
        },
        Err(err) => Err(err)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use field::FieldPrime;
    use absy::Expression;

    fn parse_comma_separated_list<T: Field>(
        input: String, 
        pos: Position
    ) -> Result<(ExpressionList<T>, String, Position), Error<T>> { 
        let mut res = ExpressionList::new();
        parse_comma_separated_expression_list_rec(input, pos, &mut res) 
    }

    #[test]
    fn comma_separated_list() {
        let pos = Position { line: 45, col: 121 };
        let string = String::from("b, c");
        let expr = ExpressionList::<FieldPrime> {
            expressions: vec![Expression::Identifier(String::from("b")),Expression::Identifier(String::from("c"))]
        };
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
            expressions: vec![Expression::Identifier(String::from("a"))]
        };
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
                Expression::Identifier(String::from("a")),
                Expression::Identifier(String::from("b")),
                Expression::Identifier(String::from("c"))
            ]
        };
        assert_eq!(
            Ok((exprs, String::from(""), pos.col(string.len() as isize))),
            parse_comma_separated_list::<FieldPrime>(string, pos)
        )
    }
}