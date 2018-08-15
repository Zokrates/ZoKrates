use field::Field;
use parser::position::Position;
use parser::token::Token;
use std::fmt;

#[derive(PartialEq)]
pub struct Error<T: Field> {
    pub expected: Vec<Token<T>>,
    pub got: Token<T>,
    pub pos: Position,
}

impl<T: Field> fmt::Display for Error<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Error at {}: Expected one of {:?}, got {:?}",
            self.pos.col(-(self.got.to_string().len() as isize)),
            self.expected,
            self.got
        )
    }
}

impl<T: Field> fmt::Debug for Error<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}