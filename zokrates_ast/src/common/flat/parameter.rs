use crate::common::{Span, WithSpan};

use super::variable::Variable;
use derivative::Derivative;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;

#[derive(Derivative)]
#[derivative(PartialOrd, PartialEq, Eq, Hash, Ord)]
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct Parameter {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub id: Variable,
    pub private: bool,
}

impl WithSpan for Parameter {
    fn span(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

impl Parameter {
    pub fn new(id: Variable, private: bool) -> Self {
        Parameter {
            id,
            private,
            span: None,
        }
    }

    pub fn public(v: Variable) -> Self {
        Self::new(v, false)
    }

    pub fn private(v: Variable) -> Self {
        Self::new(v, true)
    }
}

impl fmt::Display for Parameter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let visibility = if self.private { "private " } else { "" };
        write!(f, "{}{}", visibility, self.id)
    }
}

impl Parameter {
    pub fn apply_substitution(self, substitution: &HashMap<Variable, Variable>) -> Parameter {
        Parameter {
            id: *substitution.get(&self.id).unwrap(),
            private: self.private,
            ..self
        }
    }
}
