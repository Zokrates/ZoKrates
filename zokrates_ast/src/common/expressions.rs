use derivative::Derivative;
use num_bigint::BigUint;
use serde::{Deserialize, Serialize};

use super::operators::OpEq;
use super::{operators::OperatorStr, Span, WithSpan};
use std::fmt;
use std::marker::PhantomData;

#[derive(Derivative)]
#[derivative(PartialOrd, PartialEq, Eq, Hash, Ord)]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BinaryExpression<Op, L, R, Out> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub left: Box<L>,
    pub right: Box<R>,
    operator: PhantomData<Op>,
    output: PhantomData<Out>,
}

impl<Op, L, R, Out> BinaryExpression<Op, L, R, Out> {
    pub fn new(left: L, right: R) -> Self {
        Self {
            span: None,
            left: Box::new(left),
            right: Box::new(right),
            operator: PhantomData,
            output: PhantomData,
        }
    }
}

impl<Op: OperatorStr, L: fmt::Display, R: fmt::Display, Out: fmt::Display> fmt::Display
    for BinaryExpression<Op, L, R, Out>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({} {} {})", self.left, Op::STR, self.right,)
    }
}

impl<Op, L, R, Out> WithSpan for BinaryExpression<Op, L, R, Out> {
    fn span(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

pub enum BinaryOrExpression<Op, L, R, E, I> {
    Binary(BinaryExpression<Op, L, R, E>),
    Expression(I),
}

pub type EqExpression<E, B> = BinaryExpression<OpEq, E, E, B>;

#[derive(Derivative)]
#[derivative(PartialOrd, PartialEq, Eq, Hash, Ord)]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct UnaryExpression<Op, In, Out> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub inner: Box<In>,
    operator: PhantomData<Op>,
    output: PhantomData<Out>,
}

impl<Op, In, Out> UnaryExpression<Op, In, Out> {
    pub fn new(inner: In) -> Self {
        Self {
            span: None,
            inner: Box::new(inner),
            operator: PhantomData,
            output: PhantomData,
        }
    }
}

impl<Op: OperatorStr, In: fmt::Display, Out: fmt::Display> fmt::Display
    for UnaryExpression<Op, In, Out>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}{})", Op::STR, self.inner,)
    }
}

impl<Op, In, Out> WithSpan for UnaryExpression<Op, In, Out> {
    fn span(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

pub enum UnaryOrExpression<Op, In, E, I> {
    Unary(UnaryExpression<Op, In, E>),
    Expression(I),
}

#[derive(Derivative)]
#[derivative(PartialOrd, PartialEq, Eq, Hash, Ord)]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ValueExpression<V> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub value: V,
}

impl<V> ValueExpression<V> {
    pub fn new(value: V) -> Self {
        Self { span: None, value }
    }
}

impl<V: fmt::Display> fmt::Display for ValueExpression<V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value,)
    }
}

pub type FieldValueExpression<T> = ValueExpression<T>;

pub type BooleanValueExpression = ValueExpression<bool>;

pub type UValueExpression = ValueExpression<u128>;

pub type IntValueExpression = ValueExpression<BigUint>;

pub enum ValueOrExpression<V, I> {
    Value(V),
    Expression(I),
}

#[derive(Derivative)]
#[derivative(PartialOrd, PartialEq, Eq, Hash, Ord)]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct IdentifierExpression<I, E> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub id: I,
    pub ty: PhantomData<E>,
}

impl<I, E> IdentifierExpression<I, E> {
    pub fn new(id: I) -> Self {
        IdentifierExpression {
            span: None,
            id,
            ty: PhantomData,
        }
    }
}

impl<I: fmt::Display, E> fmt::Display for IdentifierExpression<I, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.id,)
    }
}

impl<I, T> WithSpan for IdentifierExpression<I, T> {
    fn span(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

pub enum IdentifierOrExpression<V, E, I> {
    Identifier(IdentifierExpression<V, E>),
    Expression(I),
}

#[derive(Derivative)]
#[derivative(PartialOrd, PartialEq, Eq, Hash, Ord)]
#[derive(Clone, Debug, Serialize, Deserialize)]
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
        write!(f, "{} = {}", self.assignee, self.rhs,)
    }
}

#[derive(Derivative)]
#[derivative(PartialOrd, PartialEq, Eq, Hash, Ord)]
#[derive(Clone, Debug, Serialize, Deserialize)]
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
#[derive(Clone, Debug, Serialize, Deserialize)]
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
