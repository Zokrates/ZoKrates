use parser::Position;
use std::fmt;

#[derive(Debug, Clone, Serialize, Deserialize)]
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
        write!(f, "{}", self.value)
    }
}

impl<T: fmt::Display> Node<T> {
    pub fn new(start: Position, end: Position, value: T) -> Node<T> {
        Node { start, end, value }
    }
}

pub trait NodeValue: fmt::Display + Sized + PartialEq {
    fn at(self, line: usize, col: usize, delta: isize) -> Node<Self> {
        let start = Position { col, line };
        Node::new(start, start.col(delta), self)
    }
}

#[cfg(test)]
impl<V: NodeValue> From<V> for Node<V> {
    fn from(v: V) -> Node<V> {
        let mock_position = Position { col: 42, line: 42 };
        Node::new(mock_position, mock_position, v)
    }
}

use absy::*;
use imports::*;
use zokrates_field::field::Field;

impl<T: Field> NodeValue for Expression<T> {}
impl<T: Field> NodeValue for ExpressionList<T> {}
impl<T: Field> NodeValue for Assignee<T> {}
impl<T: Field> NodeValue for Statement<T> {}
impl<T: Field> NodeValue for Function<T> {}
impl<T: Field> NodeValue for Prog<T> {}
impl NodeValue for Variable {}
impl NodeValue for Parameter {}
impl NodeValue for Import {}

impl<T: NodeValue> std::cmp::PartialEq for Node<T> {
    fn eq(&self, other: &Node<T>) -> bool {
        self.value.eq(&other.value)
    }
}
