use crate::parser::Position;
use std::fmt;
use zokrates_pest_ast::Span;

#[derive(Clone, Serialize, Deserialize)]
pub struct Node<T> {
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

impl<T: fmt::Debug> fmt::Debug for Node<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.value)
    }
}

impl<T: fmt::Display> Node<T> {
    pub fn new(start: Position, end: Position, value: T) -> Node<T> {
        Node { start, end, value }
    }
}

pub trait NodeValue: fmt::Display + fmt::Debug + Sized + PartialEq {
    fn at(self, line: usize, col: usize, delta: isize) -> Node<Self> {
        let start = Position { col, line };
        Node::new(start, start.col(delta), self)
    }

    fn start_end(self, start: Position, end: Position) -> Node<Self> {
        Node::new(start, end, self)
    }

    #[cfg(test)]
    fn mock(self) -> Node<Self> {
        Node::new(Position::mock(), Position::mock(), self)
    }

    fn span(self, span: Span) -> Node<Self> {
        let from = span.start_pos().line_col();
        let to = span.end_pos().line_col();

        let from = Position {
            line: from.0,
            col: from.1,
        };
        let to = Position {
            line: to.0,
            col: to.1,
        };

        Node::new(from, to, self)
    }
}

impl<V: NodeValue> From<V> for Node<V> {
    fn from(v: V) -> Node<V> {
        let mock_position = Position { col: 42, line: 42 };
        Node::new(mock_position, mock_position, v)
    }
}

use crate::absy::*;
use crate::imports::*;
use zokrates_field::field::Field;

impl<'ast, T: fmt::Display + fmt::Debug + PartialEq> NodeValue for Expression<'ast, T> {}
impl<'ast, T: fmt::Display + fmt::Debug + PartialEq> NodeValue for ExpressionList<'ast, T> {}
impl<'ast, T: fmt::Display + fmt::Debug + PartialEq> NodeValue for Assignee<'ast, T> {}
impl<'ast, T: fmt::Display + fmt::Debug + PartialEq> NodeValue for Statement<'ast, T> {}
impl<'ast, T: fmt::Display + fmt::Debug + PartialEq> NodeValue for SymbolDeclaration<'ast, T> {}
impl NodeValue for UnresolvedType {}
impl<'ast> NodeValue for StructType<'ast> {}
impl<'ast> NodeValue for StructField<'ast> {}
impl<'ast, T: fmt::Display + fmt::Debug + PartialEq> NodeValue for Function<'ast, T> {}
impl<'ast, T: fmt::Display + fmt::Debug + PartialEq> NodeValue for Module<'ast, T> {}
impl<'ast> NodeValue for SymbolImport<'ast> {}
impl<'ast> NodeValue for Variable<'ast> {}
impl<'ast> NodeValue for Parameter<'ast> {}
impl<'ast> NodeValue for Import<'ast> {}
impl<'ast, T: fmt::Display + fmt::Debug + PartialEq> NodeValue for Spread<'ast, T> {}
impl<T: fmt::Display + fmt::Debug + PartialEq> NodeValue for Range<T> {}

impl<T: PartialEq> PartialEq for Node<T> {
    fn eq(&self, other: &Node<T>) -> bool {
        self.value.eq(&other.value)
    }
}
