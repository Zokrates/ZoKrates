use parser::tokenize::Position;
use parser::tokenize::Token;
use std::fmt;
use zokrates_field::field::Field;

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
            "{}\n\tExpected one of {:?}, got {:?}",
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
