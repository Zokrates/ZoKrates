use parser::Position;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Node<T: fmt::Display> {
    pub start: Position,
    pub end: Position,
    pub value: T,
}

impl<T: fmt::Display> Node<T> {
    pub fn pos(&self) -> (Position, Position) {
        (self.start, self.end)
    }
}

impl<T: fmt::Display> fmt::Display for Node<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} ({}:{})", self.value, self.start, self.end)
    }
}

impl<T: fmt::Display> Node<T> {
    pub fn new(start: Position, end: Position, value: T) -> Node<T> {
        Node { start, end, value }
    }
}
