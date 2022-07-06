use std::fmt;

#[derive(Clone, PartialEq, Eq, Copy, Hash, Default, PartialOrd, Ord)]
pub struct Position {
    pub line: usize,
    pub col: usize,
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
