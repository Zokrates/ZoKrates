use derivative::Derivative;
use serde::{Deserialize, Serialize};
use std::fmt;

use super::{Span, WithSpan};

#[derive(Derivative)]
#[derivative(PartialOrd, PartialEq, Hash, Eq, Ord)]
#[derive(Clone, Serialize, Deserialize, Debug)]
pub struct Variable<I, T> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub id: I,
    pub ty: T,
}

impl<I, T> WithSpan for Variable<I, T> {
    fn span(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

impl<I, T> Variable<I, T> {
    pub fn new<J: Into<I>>(id: J, ty: T) -> Self {
        Self {
            span: None,
            id: id.into(),
            ty,
        }
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for Variable<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self.ty, self.id,)
    }
}
