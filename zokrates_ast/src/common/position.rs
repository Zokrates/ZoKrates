use std::fmt;

use serde::{Deserialize, Serialize};

#[derive(Clone, PartialEq, Eq, Copy, Hash, Default, PartialOrd, Ord, Deserialize, Serialize)]
pub struct Position {
    pub line: usize,
    pub col: usize,
}

#[derive(Clone, PartialEq, Eq, Copy, Hash, Default, PartialOrd, Ord, Deserialize, Serialize)]
pub struct Span {
    pub from: Position,
    pub to: Position,
}

pub trait WithSpan: Sized {
    fn span(self, _: Option<Span>) -> Self;

    fn with_span(self, span: Span) -> Self {
        self.span(Some(span))
    }

    fn get_span(&self) -> Option<Span>;
}

impl Span {
    pub fn mock() -> Self {
        Span {
            from: Position::mock(),
            to: Position::mock(),
        }
    }
}

impl Position {
    pub fn col(&self, delta: isize) -> Position {
        assert!(self.col <= isize::max_value() as usize);
        assert!(self.col as isize >= delta);
        Position {
            line: self.line,
            col: (self.col as isize + delta) as usize,
        }
    }

    pub fn mock() -> Self {
        Position { line: 42, col: 42 }
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

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({},{})", self.from, self.to)
    }
}
impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

#[test]
fn position_col() {
    let pos = Position {
        line: 100,
        col: 258,
    };
    assert_eq!(
        pos.col(26),
        Position {
            line: 100,
            col: 284,
        }
    );
    assert_eq!(
        pos.col(-23),
        Position {
            line: 100,
            col: 235,
        }
    );
}
