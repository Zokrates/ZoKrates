use derivative::Derivative;
use serde::{Deserialize, Serialize};

use crate::Solver;

use super::{FormatString, SourceMetadata};
use super::{Span, WithSpan};
use std::fmt;

#[derive(Derivative)]
#[derivative(PartialOrd, PartialEq, Eq, Hash, Ord)]
#[derive(Clone, Debug)]
pub struct DefinitionStatement<A, E> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub assignee: A,
    pub rhs: E,
}

impl<A, E> DefinitionStatement<A, E> {
    pub fn new(assignee: A, rhs: E) -> Self {
        DefinitionStatement {
            span: None,
            assignee,
            rhs,
        }
    }
}

impl<A, E> WithSpan for DefinitionStatement<A, E> {
    fn span(self, span: Option<Span>) -> Self {
        Self { span, ..self }
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

impl<A: fmt::Display, E: fmt::Display> fmt::Display for DefinitionStatement<A, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {};", self.assignee, self.rhs,)
    }
}

#[derive(Derivative)]
#[derivative(PartialOrd, PartialEq, Eq, Hash, Ord)]
#[derive(Clone, Debug)]
pub struct AssertionStatement<B, E> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub expression: B,
    pub error: E,
}

impl<B, E> AssertionStatement<B, E> {
    pub fn new(expression: B, error: E) -> Self {
        AssertionStatement {
            span: None,
            expression,
            error,
        }
    }
}

impl<B, E> WithSpan for AssertionStatement<B, E> {
    fn span(self, span: Option<Span>) -> Self {
        Self { span, ..self }
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

#[derive(Derivative)]
#[derivative(PartialOrd, PartialEq, Eq, Hash, Ord)]
#[derive(Clone, Debug)]
pub struct ReturnStatement<E> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub inner: E,
}

impl<E> ReturnStatement<E> {
    pub fn new(e: E) -> Self {
        ReturnStatement {
            span: None,
            inner: e,
        }
    }
}

impl<E> WithSpan for ReturnStatement<E> {
    fn span(self, span: Option<Span>) -> Self {
        Self { span, ..self }
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

impl<E: fmt::Display> fmt::Display for ReturnStatement<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "return {};", self.inner)
    }
}

#[derive(Derivative)]
#[derivative(PartialOrd, PartialEq, Eq, Hash, Ord)]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LogStatement<E> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub format_string: FormatString,
    pub expressions: Vec<E>,
}

impl<E> LogStatement<E> {
    pub fn new(format_string: FormatString, expressions: Vec<E>) -> Self {
        LogStatement {
            span: None,
            format_string,
            expressions,
        }
    }
}

impl<E> WithSpan for LogStatement<E> {
    fn span(self, span: Option<Span>) -> Self {
        Self { span, ..self }
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

impl<E: fmt::Display> fmt::Display for LogStatement<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "log({}, {});",
            self.format_string,
            self.expressions
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

#[derive(Derivative, Clone, Debug, Serialize, Deserialize)]
#[derivative(Hash, PartialEq, Eq)]
pub struct DirectiveStatement<I, O, S> {
    #[derivative(Hash = "ignore", PartialEq = "ignore")]
    pub span: Option<Span>,
    pub inputs: Vec<I>,
    pub outputs: Vec<O>,
    pub solver: S,
}

impl<'ast, T, I, O> DirectiveStatement<I, O, Solver<'ast, T>> {
    pub fn new(outputs: Vec<O>, solver: Solver<'ast, T>, inputs: Vec<I>) -> Self {
        let (in_len, out_len) = solver.get_signature();
        assert_eq!(in_len, inputs.len());
        assert_eq!(out_len, outputs.len());
        Self {
            span: None,
            inputs,
            outputs,
            solver,
        }
    }
}

impl<I, O, S> WithSpan for DirectiveStatement<I, O, S> {
    fn span(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

impl<I: fmt::Display, O: fmt::Display, S: fmt::Display> fmt::Display
    for DirectiveStatement<I, O, S>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "# {} = {}({})",
            self.outputs
                .iter()
                .map(|o| format!("{}", o))
                .collect::<Vec<_>>()
                .join(", "),
            self.solver,
            self.inputs
                .iter()
                .map(|i| format!("{}", i))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

#[derive(Derivative)]
#[derivative(PartialEq, Eq, Hash, PartialOrd, Ord)]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AssemblyAssignment<A, E> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub assignee: A,
    pub expression: E,
}

impl<A, E> AssemblyAssignment<A, E> {
    pub fn new(assignee: A, expression: E) -> Self {
        Self {
            span: None,
            assignee,
            expression,
        }
    }
}

impl<A, E> WithSpan for AssemblyAssignment<A, E> {
    fn span(self, span: Option<Span>) -> Self {
        Self { span, ..self }
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

#[derive(Derivative)]
#[derivative(PartialEq, Eq, Hash, PartialOrd, Ord)]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AssemblyConstraint<E> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub left: E,
    pub right: E,
    pub metadata: SourceMetadata,
}

impl<E> AssemblyConstraint<E> {
    pub fn new(left: E, right: E, metadata: SourceMetadata) -> Self {
        Self {
            span: None,
            left,
            right,
            metadata,
        }
    }
}

impl<E> WithSpan for AssemblyConstraint<E> {
    fn span(self, span: Option<Span>) -> Self {
        Self { span, ..self }
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

impl<E: fmt::Display> fmt::Display for AssemblyConstraint<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} === {};", self.left, self.right)
    }
}
