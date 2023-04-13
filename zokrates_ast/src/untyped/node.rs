use crate::common::LocalSourceSpan as Span;
use std::fmt;
use zokrates_pest_ast::Span as PestSpan;

#[derive(Clone)]
pub struct Node<T> {
    pub span: Span,
    pub value: T,
}

impl<T> Node<T> {
    pub fn mock(e: T) -> Self {
        Self {
            span: Span::mock(),
            value: e,
        }
    }
}

impl<T: fmt::Display> Node<T> {
    pub fn span(&self) -> Span {
        self.span
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
    pub fn new(from: Position, to: Position, value: T) -> Node<T> {
        Node {
            span: Span { from, to },
            value,
        }
    }
}

pub trait NodeValue: fmt::Display + fmt::Debug + Sized + PartialEq {
    fn at(self, line: usize, col: usize, delta: isize) -> Node<Self> {
        let start = Position { line, col };
        Node::new(start, start.col(delta), self)
    }

    fn start_end(self, start: Position, end: Position) -> Node<Self> {
        Node::new(start, end, self)
    }

    fn mock(self) -> Node<Self> {
        Node::new(Position::mock(), Position::mock(), self)
    }

    fn span(self, span: PestSpan) -> Node<Self> {
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
        Node::new(Position::mock(), Position::mock(), v)
    }
}

use super::*;

impl<'ast> NodeValue for Expression<'ast> {}
impl<'ast> NodeValue for Assignee<'ast> {}
impl<'ast> NodeValue for Statement<'ast> {}
impl<'ast> NodeValue for AssemblyStatement<'ast> {}
impl<'ast> NodeValue for SymbolDeclaration<'ast> {}
impl<'ast> NodeValue for UnresolvedType<'ast> {}
impl<'ast> NodeValue for StructDefinition<'ast> {}
impl<'ast> NodeValue for StructDefinitionField<'ast> {}
impl<'ast> NodeValue for ConstantDefinition<'ast> {}
impl<'ast> NodeValue for TypeDefinition<'ast> {}
impl<'ast> NodeValue for Function<'ast> {}
impl<'ast> NodeValue for Module<'ast> {}
impl<'ast> NodeValue for CanonicalImport<'ast> {}
impl<'ast> NodeValue for SymbolImport<'ast> {}
impl<'ast> NodeValue for Variable<'ast> {}
impl<'ast> NodeValue for Parameter<'ast> {}
impl<'ast> NodeValue for Spread<'ast> {}
impl<'ast> NodeValue for Range<'ast> {}
impl<'ast> NodeValue for Identifier<'ast> {}

impl<T: PartialEq> PartialEq for Node<T> {
    fn eq(&self, other: &Node<T>) -> bool {
        self.value.eq(&other.value)
    }
}
