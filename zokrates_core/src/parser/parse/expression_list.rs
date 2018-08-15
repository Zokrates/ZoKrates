use absy::variable::Variable;
use parser::parse::expression::parse_expr;
use field::Field;
use parser::position::Position;
use absy::ExpressionList;
use parser::token::Token;
use parser::error::Error;
use parser::tokenizer::next_token;

// parse an expression list starting with an identifier
pub fn parse_identifier_list1<T: Field>(
    head: String,
    input: String,
    pos: Position,
) -> Result<(Vec<Variable>, String, Position), Error<T>> {
    let mut res = Vec::new();
    res.push(Variable::from(head));
    parse_comma_separated_identifier_list_rec(input, pos, &mut res)
}

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

fn parse_comma_separated_identifier_list_rec<T: Field>(
    input: String, 
    pos: Position,
    mut acc: &mut Vec<Variable>
) -> Result<(Vec<Variable>, String, Position), Error<T>> {
    match next_token(&input, &pos) {
        (Token::Ide(id), s1, p1) => {
            acc.push(Variable::from(id));
            match next_token::<T>(&s1, &p1) {
                (Token::Comma, s2, p2) => parse_comma_separated_identifier_list_rec(s2, p2, &mut acc),
                (..) => Ok((acc.to_vec(), s1, p1)),
            }
        },
        (t1, _, p1) => Err(Error {
            expected: vec![Token::Ide(String::from("ide"))],
            got: t1,
            pos: p1,
        })
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