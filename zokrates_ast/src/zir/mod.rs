pub mod folder;
mod from_typed;
mod identifier;
mod parameter;
pub mod result_folder;
pub mod types;
mod uint;
mod variable;

pub use self::parameter::Parameter;
pub use self::types::{Type, UBitwidth};
pub use self::variable::Variable;
use crate::common::expressions::{BooleanValueExpression, UnaryExpression};
use crate::common::{
    expressions::{self, BinaryExpression, ValueExpression},
    operators::*,
};
use crate::common::{FlatEmbed, FormatString, Span, Value, WithSpan};
use crate::typed::ConcreteType;
pub use crate::zir::uint::{ShouldReduce, UExpression, UExpressionInner, UMetadata};

use crate::zir::types::Signature;
use std::fmt;
use std::marker::PhantomData;
use zokrates_field::Field;

pub use self::folder::Folder;
pub use self::identifier::{Identifier, SourceIdentifier};

/// A typed program as a collection of modules, one of them being the main
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct ZirProgram<'ast, T> {
    pub main: ZirFunction<'ast, T>,
}

impl<'ast, T: fmt::Display> fmt::Display for ZirProgram<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.main)
    }
}
/// A typed function
#[derive(Clone, PartialEq, Eq)]
pub struct ZirFunction<'ast, T> {
    /// Arguments of the function
    pub arguments: Vec<Parameter<'ast>>,
    /// Vector of statements that are executed when running the function
    pub statements: Vec<ZirStatement<'ast, T>>,
    /// function signature
    pub signature: Signature,
}

pub type IdentifierOrExpression<'ast, T, E> =
    expressions::IdentifierOrExpression<Identifier<'ast>, E, <E as Expr<'ast, T>>::Inner>;

impl<'ast, T: fmt::Display> fmt::Display for ZirFunction<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(
            f,
            "({}) -> ({}) {{",
            self.arguments
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>()
                .join(", "),
            self.signature
                .outputs
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>()
                .join(", ")
        )?;

        for s in &self.statements {
            s.fmt_indented(f, 1)?;
            writeln!(f)?;
        }

        writeln!(f, "}}")
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for ZirFunction<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "ZirFunction(arguments: {:?}, ...):\n{}",
            self.arguments,
            self.statements
                .iter()
                .map(|x| format!("\t{:?}", x))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

pub type ZirAssignee<'ast> = Variable<'ast>;

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub enum RuntimeError {
    SourceAssertion(String),
    SelectRangeCheck,
    DivisionByZero,
    IncompleteDynamicRange,
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeError::SourceAssertion(message) => write!(f, "{}", message),
            RuntimeError::SelectRangeCheck => write!(f, "Range check on array access"),
            RuntimeError::DivisionByZero => write!(f, "Division by zero"),
            RuntimeError::IncompleteDynamicRange => write!(f, "Dynamic comparison is incomplete"),
        }
    }
}

impl RuntimeError {
    pub fn mock() -> Self {
        RuntimeError::SourceAssertion(String::default())
    }
}

/// A statement in a `ZirFunction`
#[derive(Clone, PartialEq, Hash, Eq, Debug)]
pub enum ZirStatement<'ast, T> {
    Return(Vec<ZirExpression<'ast, T>>),
    Definition(ZirAssignee<'ast>, ZirExpression<'ast, T>),
    IfElse(
        BooleanExpression<'ast, T>,
        Vec<ZirStatement<'ast, T>>,
        Vec<ZirStatement<'ast, T>>,
    ),
    Assertion(BooleanExpression<'ast, T>, RuntimeError),
    MultipleDefinition(Vec<ZirAssignee<'ast>>, ZirExpressionList<'ast, T>),
    Log(
        FormatString,
        Vec<(ConcreteType, Vec<ZirExpression<'ast, T>>)>,
    ),
}

impl<'ast, T: fmt::Display> fmt::Display for ZirStatement<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.fmt_indented(f, 0)
    }
}

impl<'ast, T: fmt::Display> ZirStatement<'ast, T> {
    fn fmt_indented(&self, f: &mut fmt::Formatter, depth: usize) -> fmt::Result {
        write!(f, "{}", "\t".repeat(depth))?;
        match self {
            ZirStatement::Return(ref exprs) => {
                write!(
                    f,
                    "return {};",
                    exprs
                        .iter()
                        .map(|e| e.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            ZirStatement::Definition(ref lhs, ref rhs) => {
                write!(f, "{} = {};", lhs, rhs)
            }
            ZirStatement::IfElse(ref condition, ref consequence, ref alternative) => {
                writeln!(f, "if {} {{", condition)?;
                for s in consequence {
                    s.fmt_indented(f, depth + 1)?;
                    writeln!(f)?;
                }
                writeln!(f, "{}}} else {{", "\t".repeat(depth))?;
                for s in alternative {
                    s.fmt_indented(f, depth + 1)?;
                    writeln!(f)?;
                }
                write!(f, "{}}};", "\t".repeat(depth))
            }
            ZirStatement::Assertion(ref e, ref error) => {
                write!(f, "assert({}", e)?;
                match error {
                    RuntimeError::SourceAssertion(message) => write!(f, ", \"{}\");", message),
                    error => write!(f, "); // {}", error),
                }
            }
            ZirStatement::MultipleDefinition(ref ids, ref rhs) => {
                for (i, id) in ids.iter().enumerate() {
                    write!(f, "{}", id)?;
                    if i < ids.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, " = {};", rhs)
            }
            ZirStatement::Log(ref l, ref expressions) => write!(
                f,
                "log(\"{}\"), {});",
                l,
                expressions
                    .iter()
                    .map(|(_, e)| format!(
                        "[{}]",
                        e.iter()
                            .map(|e| e.to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    ))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

pub trait Typed {
    fn get_type(&self) -> Type;
}

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub struct ConditionalExpression<'ast, T, E> {
    pub span: Option<Span>,
    pub condition: Box<BooleanExpression<'ast, T>>,
    pub consequence: Box<E>,
    pub alternative: Box<E>,
}

impl<'ast, T, E> ConditionalExpression<'ast, T, E> {
    pub fn new(condition: BooleanExpression<'ast, T>, consequence: E, alternative: E) -> Self {
        ConditionalExpression {
            span: None,
            condition: box condition,
            consequence: box consequence,
            alternative: box alternative,
        }
    }
}

impl<'ast, T: fmt::Display, E: fmt::Display> fmt::Display for ConditionalExpression<'ast, T, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} ? {} : {}",
            self.condition, self.consequence, self.alternative
        )
    }
}

impl<'ast, T, E> WithSpan for ConditionalExpression<'ast, T, E> {
    fn span(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub struct SelectExpression<'ast, T, E> {
    pub span: Option<Span>,
    pub array: Vec<E>,
    pub index: Box<UExpression<'ast, T>>,
}

impl<'ast, T, E> SelectExpression<'ast, T, E> {
    pub fn new(array: Vec<E>, index: UExpression<'ast, T>) -> Self {
        SelectExpression {
            span: None,
            array,
            index: box index,
        }
    }
}

impl<'ast, T: fmt::Display, E: fmt::Display> fmt::Display for SelectExpression<'ast, T, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}[{}]",
            self.array
                .iter()
                .map(|a| a.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            self.index
        )
    }
}

impl<'ast, T, E> WithSpan for SelectExpression<'ast, T, E> {
    fn span(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

/// A typed expression
#[derive(Clone, PartialEq, Hash, Eq)]
pub enum ZirExpression<'ast, T> {
    Boolean(BooleanExpression<'ast, T>),
    FieldElement(FieldElementExpression<'ast, T>),
    Uint(UExpression<'ast, T>),
}

impl<'ast, T: Field> From<BooleanExpression<'ast, T>> for ZirExpression<'ast, T> {
    fn from(e: BooleanExpression<'ast, T>) -> ZirExpression<T> {
        ZirExpression::Boolean(e)
    }
}

impl<'ast, T: Field> From<FieldElementExpression<'ast, T>> for ZirExpression<'ast, T> {
    fn from(e: FieldElementExpression<'ast, T>) -> ZirExpression<T> {
        ZirExpression::FieldElement(e)
    }
}

impl<'ast, T: Field> From<UExpression<'ast, T>> for ZirExpression<'ast, T> {
    fn from(e: UExpression<'ast, T>) -> ZirExpression<T> {
        ZirExpression::Uint(e)
    }
}

impl<'ast, T: fmt::Display> fmt::Display for ZirExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ZirExpression::Boolean(ref e) => write!(f, "{}", e),
            ZirExpression::FieldElement(ref e) => write!(f, "{}", e),
            ZirExpression::Uint(ref e) => write!(f, "{}", e),
        }
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for ZirExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ZirExpression::Boolean(ref e) => write!(f, "{:?}", e),
            ZirExpression::FieldElement(ref e) => write!(f, "{:?}", e),
            ZirExpression::Uint(ref e) => write!(f, "{:?}", e),
        }
    }
}

impl<'ast, T: Field> Typed for ZirExpression<'ast, T> {
    fn get_type(&self) -> Type {
        match *self {
            ZirExpression::Boolean(ref e) => e.get_type(),
            ZirExpression::FieldElement(ref e) => e.get_type(),
            ZirExpression::Uint(ref e) => e.get_type(),
        }
    }
}

impl<'ast, T: Field> Typed for FieldElementExpression<'ast, T> {
    fn get_type(&self) -> Type {
        Type::FieldElement
    }
}

impl<'ast, T: Field> Typed for UExpression<'ast, T> {
    fn get_type(&self) -> Type {
        Type::Uint(self.bitwidth)
    }
}

impl<'ast, T: Field> Typed for BooleanExpression<'ast, T> {
    fn get_type(&self) -> Type {
        Type::Boolean
    }
}

pub trait MultiTyped {
    fn get_types(&self) -> &Vec<Type>;
}

#[derive(Clone, PartialEq, Hash, Eq)]
pub enum ZirExpressionList<'ast, T> {
    EmbedCall(FlatEmbed, Vec<u32>, Vec<ZirExpression<'ast, T>>),
}

pub type IdentifierExpression<'ast, E> = expressions::IdentifierExpression<Identifier<'ast>, E>;

/// An expression of type `field`
#[derive(Clone, PartialEq, Hash, Eq, Debug)]
pub enum FieldElementExpression<'ast, T> {
    Number(ValueExpression<T>),
    Identifier(IdentifierExpression<'ast, Self>),
    Select(SelectExpression<'ast, T, Self>),
    Add(BinaryExpression<OpAdd, Self, Self, Self>),
    Sub(BinaryExpression<OpSub, Self, Self, Self>),
    Mult(BinaryExpression<OpMul, Self, Self, Self>),
    Div(BinaryExpression<OpDiv, Self, Self, Self>),
    Pow(BinaryExpression<OpPow, Self, UExpression<'ast, T>, Self>),
    Conditional(ConditionalExpression<'ast, T, FieldElementExpression<'ast, T>>),
}

impl<'ast, T> FieldElementExpression<'ast, T> {
    pub fn number(n: T) -> Self {
        Self::Number(ValueExpression::new(n))
    }
}

/// An expression of type `bool`
#[derive(Clone, PartialEq, Hash, Eq, Debug)]
pub enum BooleanExpression<'ast, T> {
    Value(BooleanValueExpression),
    Identifier(IdentifierExpression<'ast, Self>),
    Select(SelectExpression<'ast, T, Self>),
    FieldLt(
        BinaryExpression<
            OpLt,
            FieldElementExpression<'ast, T>,
            FieldElementExpression<'ast, T>,
            Self,
        >,
    ),
    FieldLe(
        BinaryExpression<
            OpLe,
            FieldElementExpression<'ast, T>,
            FieldElementExpression<'ast, T>,
            Self,
        >,
    ),
    FieldEq(
        BinaryExpression<
            OpEq,
            FieldElementExpression<'ast, T>,
            FieldElementExpression<'ast, T>,
            Self,
        >,
    ),
    UintLt(BinaryExpression<OpLt, UExpression<'ast, T>, UExpression<'ast, T>, Self>),
    UintLe(BinaryExpression<OpLe, UExpression<'ast, T>, UExpression<'ast, T>, Self>),
    UintEq(BinaryExpression<OpEq, UExpression<'ast, T>, UExpression<'ast, T>, Self>),
    BoolEq(BinaryExpression<OpEq, Self, Self, Self>),
    Or(BinaryExpression<OpOr, Self, Self, Self>),
    And(BinaryExpression<OpAnd, Self, Self, Self>),
    Not(UnaryExpression<OpNot, Self, Self>),
    Conditional(ConditionalExpression<'ast, T, BooleanExpression<'ast, T>>),
}

pub struct ConjunctionIterator<T> {
    current: Vec<T>,
}

impl<'ast, T> Iterator for ConjunctionIterator<BooleanExpression<'ast, T>> {
    type Item = BooleanExpression<'ast, T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.current.pop().and_then(|n| match n {
            BooleanExpression::And(e) => {
                self.current.push(*e.left);
                self.current.push(*e.right);
                self.next()
            }
            n => Some(n),
        })
    }
}

impl<'ast, T> BooleanExpression<'ast, T> {
    pub fn into_conjunction_iterator(self) -> ConjunctionIterator<Self> {
        ConjunctionIterator {
            current: vec![self],
        }
    }
}

// Downcasts
impl<'ast, T> From<ZirExpression<'ast, T>> for FieldElementExpression<'ast, T> {
    fn from(e: ZirExpression<'ast, T>) -> FieldElementExpression<'ast, T> {
        match e {
            ZirExpression::FieldElement(e) => e,
            _ => unreachable!("downcast failed"),
        }
    }
}

impl<'ast, T> From<ZirExpression<'ast, T>> for BooleanExpression<'ast, T> {
    fn from(e: ZirExpression<'ast, T>) -> BooleanExpression<'ast, T> {
        match e {
            ZirExpression::Boolean(e) => e,
            _ => unreachable!("downcast failed"),
        }
    }
}

impl<'ast, T> From<ZirExpression<'ast, T>> for UExpression<'ast, T> {
    fn from(e: ZirExpression<'ast, T>) -> UExpression<'ast, T> {
        match e {
            ZirExpression::Uint(e) => e,
            _ => unreachable!("downcast failed"),
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for FieldElementExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FieldElementExpression::Number(ref i) => write!(f, "{}", i),
            FieldElementExpression::Identifier(ref var) => write!(f, "{}", var),
            FieldElementExpression::Select(ref e) => write!(f, "{}", e),
            FieldElementExpression::Add(ref e) => write!(f, "{}", e),
            FieldElementExpression::Sub(ref e) => write!(f, "{}", e),
            FieldElementExpression::Mult(ref e) => write!(f, "{}", e),
            FieldElementExpression::Div(ref e) => write!(f, "{}", e),
            FieldElementExpression::Pow(ref e) => write!(f, "{}", e),
            FieldElementExpression::Conditional(ref c) => {
                write!(f, "{}", c)
            }
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for UExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.inner {
            UExpressionInner::Value(ref v) => write!(f, "{}", v),
            UExpressionInner::Identifier(ref var) => write!(f, "{}", var),
            UExpressionInner::Select(ref e) => write!(f, "{}", e),
            UExpressionInner::Add(ref e) => write!(f, "{}", e),
            UExpressionInner::Sub(ref e) => write!(f, "{}", e),
            UExpressionInner::Mult(ref e) => write!(f, "{}", e),
            UExpressionInner::Div(ref e) => write!(f, "{}", e),
            UExpressionInner::Rem(ref e) => write!(f, "{}", e),
            UExpressionInner::Xor(ref e) => write!(f, "{}", e),
            UExpressionInner::And(ref e) => write!(f, "{}", e),
            UExpressionInner::Or(ref e) => write!(f, "{}", e),
            UExpressionInner::LeftShift(ref e) => write!(f, "{}", e),
            UExpressionInner::RightShift(ref e) => write!(f, "{}", e),
            UExpressionInner::Not(ref e) => write!(f, "{}", e),
            UExpressionInner::Conditional(ref c) => {
                write!(f, "{}", c)
            }
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for BooleanExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            BooleanExpression::Identifier(ref var) => write!(f, "{}", var),
            BooleanExpression::Value(ref b) => write!(f, "{}", b),
            BooleanExpression::Select(ref e) => write!(f, "{}", e),
            BooleanExpression::FieldLt(ref e) => write!(f, "{}", e),
            BooleanExpression::UintLt(ref e) => write!(f, "{}", e),
            BooleanExpression::FieldLe(ref e) => write!(f, "{}", e),
            BooleanExpression::UintLe(ref e) => write!(f, "{}", e),
            BooleanExpression::FieldEq(ref e) => write!(f, "{}", e),
            BooleanExpression::BoolEq(ref e) => write!(f, "{}", e),
            BooleanExpression::UintEq(ref e) => write!(f, "{}", e),
            BooleanExpression::Or(ref e) => write!(f, "{}", e),
            BooleanExpression::And(ref e) => write!(f, "{}", e),
            BooleanExpression::Not(ref exp) => write!(f, "{}", exp),
            BooleanExpression::Conditional(ref c) => {
                write!(f, "{}", c)
            }
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for ZirExpressionList<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ZirExpressionList::EmbedCall(ref embed, ref generics, ref p) => {
                write!(
                    f,
                    "{}{}(",
                    embed.id(),
                    if generics.is_empty() {
                        "".into()
                    } else {
                        format!(
                            "::<{}>",
                            generics
                                .iter()
                                .map(|g| g.to_string())
                                .collect::<Vec<_>>()
                                .join(", ")
                        )
                    }
                )?;
                for (i, param) in p.iter().enumerate() {
                    write!(f, "{}", param)?;
                    if i < p.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
        }
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for ZirExpressionList<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ZirExpressionList::EmbedCall(ref embed, ref generics, ref p) => {
                write!(f, "EmbedCall({:?}, {:?}, (", generics, embed)?;
                f.debug_list().entries(p.iter()).finish()?;
                write!(f, ")")
            }
        }
    }
}

impl<'ast, T: Field> std::ops::Add for FieldElementExpression<'ast, T> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        FieldElementExpression::Add(BinaryExpression::new(self, other))
    }
}

impl<'ast, T: Field> std::ops::Sub for FieldElementExpression<'ast, T> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        FieldElementExpression::Sub(BinaryExpression::new(self, other))
    }
}

impl<'ast, T: Field> std::ops::Mul for FieldElementExpression<'ast, T> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        FieldElementExpression::Mult(BinaryExpression::new(self, other))
    }
}

impl<'ast, T: Field> std::ops::Div for FieldElementExpression<'ast, T> {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        FieldElementExpression::Div(BinaryExpression::new(self, other))
    }
}

impl<'ast, T: Clone> Value for FieldElementExpression<'ast, T> {
    type Value = T;

    fn as_value(&self) -> Option<&Self::Value> {
        unimplemented!()
    }
}

impl<'ast, T> Value for BooleanExpression<'ast, T> {
    type Value = bool;
}

impl<'ast, T> Value for UExpression<'ast, T> {
    type Value = u128;
}

// Common behaviour across expressions
pub trait Expr<'ast, T>: Value + fmt::Display + PartialEq + From<ZirExpression<'ast, T>> {
    type Inner;
    type Ty: Clone + IntoType;

    fn ty(&self) -> &Self::Ty;

    fn into_inner(self) -> Self::Inner;

    fn as_inner(&self) -> &Self::Inner;

    fn as_inner_mut(&mut self) -> &mut Self::Inner;
}

impl<'ast, T: Field> Expr<'ast, T> for FieldElementExpression<'ast, T> {
    type Inner = Self;
    type Ty = Type;

    fn ty(&self) -> &Self::Ty {
        &Type::FieldElement
    }

    fn into_inner(self) -> Self::Inner {
        self
    }

    fn as_inner(&self) -> &Self::Inner {
        self
    }

    fn as_inner_mut(&mut self) -> &mut Self::Inner {
        self
    }
}

impl<'ast, T: Field> Expr<'ast, T> for BooleanExpression<'ast, T> {
    type Inner = Self;
    type Ty = Type;

    fn ty(&self) -> &Self::Ty {
        &Type::Boolean
    }

    fn into_inner(self) -> Self::Inner {
        self
    }

    fn as_inner(&self) -> &Self::Inner {
        self
    }

    fn as_inner_mut(&mut self) -> &mut Self::Inner {
        self
    }
}

impl<'ast, T: Field> Expr<'ast, T> for UExpression<'ast, T> {
    type Inner = UExpressionInner<'ast, T>;
    type Ty = UBitwidth;

    fn ty(&self) -> &Self::Ty {
        &self.bitwidth
    }

    fn into_inner(self) -> Self::Inner {
        self.inner
    }

    fn as_inner(&self) -> &Self::Inner {
        &self.inner
    }

    fn as_inner_mut(&mut self) -> &mut Self::Inner {
        &mut self.inner
    }
}

pub trait Id<'ast, T>: Expr<'ast, T> {
    fn identifier(id: Identifier<'ast>) -> Self::Inner;
}

impl<'ast, T: Field> Id<'ast, T> for FieldElementExpression<'ast, T> {
    fn identifier(id: Identifier<'ast>) -> Self::Inner {
        FieldElementExpression::Identifier(IdentifierExpression::new(id))
    }
}

impl<'ast, T: Field> Id<'ast, T> for BooleanExpression<'ast, T> {
    fn identifier(id: Identifier<'ast>) -> Self::Inner {
        BooleanExpression::Identifier(IdentifierExpression::new(id))
    }
}

impl<'ast, T: Field> Id<'ast, T> for UExpression<'ast, T> {
    fn identifier(id: Identifier<'ast>) -> Self::Inner {
        UExpressionInner::Identifier(IdentifierExpression::new(id))
    }
}

pub trait Conditional<'ast, T> {
    fn conditional(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
    ) -> Self;
}

pub enum ConditionalOrExpression<'ast, T, E: Expr<'ast, T>> {
    Conditional(ConditionalExpression<'ast, T, E>),
    Expression(E::Inner),
}

impl<'ast, T> Conditional<'ast, T> for FieldElementExpression<'ast, T> {
    fn conditional(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
    ) -> Self {
        FieldElementExpression::Conditional(ConditionalExpression::new(
            condition,
            consequence,
            alternative,
        ))
    }
}

impl<'ast, T> Conditional<'ast, T> for BooleanExpression<'ast, T> {
    fn conditional(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
    ) -> Self {
        BooleanExpression::Conditional(ConditionalExpression::new(
            condition,
            consequence,
            alternative,
        ))
    }
}

impl<'ast, T> Conditional<'ast, T> for UExpression<'ast, T> {
    fn conditional(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
    ) -> Self {
        let bitwidth = consequence.bitwidth;

        UExpressionInner::Conditional(ConditionalExpression::new(
            condition,
            consequence,
            alternative,
        ))
        .annotate(bitwidth)
    }
}
pub trait Select<'ast, T>: Sized {
    fn select(array: Vec<Self>, index: UExpression<'ast, T>) -> Self;
}

pub enum SelectOrExpression<'ast, T, E: Expr<'ast, T>> {
    Select(SelectExpression<'ast, T, E>),
    Expression(E::Inner),
}

impl<'ast, T> Select<'ast, T> for FieldElementExpression<'ast, T> {
    fn select(array: Vec<Self>, index: UExpression<'ast, T>) -> Self {
        FieldElementExpression::Select(SelectExpression::new(array, index))
    }
}

impl<'ast, T> Select<'ast, T> for BooleanExpression<'ast, T> {
    fn select(array: Vec<Self>, index: UExpression<'ast, T>) -> Self {
        BooleanExpression::Select(SelectExpression::new(array, index))
    }
}

impl<'ast, T> Select<'ast, T> for UExpression<'ast, T> {
    fn select(array: Vec<Self>, index: UExpression<'ast, T>) -> Self {
        let bitwidth = array[0].bitwidth;

        UExpressionInner::Select(SelectExpression::new(array, index)).annotate(bitwidth)
    }
}
pub trait IntoType {
    fn into_type(self) -> Type;
}

impl IntoType for Type {
    fn into_type(self) -> Type {
        self
    }
}

impl IntoType for UBitwidth {
    fn into_type(self) -> Type {
        Type::Uint(self)
    }
}

impl<'ast, T> WithSpan for FieldElementExpression<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        use FieldElementExpression::*;
        match self {
            Select(e) => Select(e.span(span)),
            Identifier(e) => Identifier(e.span(span)),
            Conditional(e) => Conditional(e.span(span)),
            Add(e) => Add(e.span(span)),
            Number(e) => Number(e.span(span)),
            e => e,
        }
    }

    fn get_span(&self) -> Option<Span> {
        use FieldElementExpression::*;
        match self {
            Select(e) => e.get_span(),
            Identifier(e) => e.get_span(),
            Conditional(e) => e.get_span(),
            Add(e) => e.get_span(),
            Number(e) => e.get_span(),
            e => unimplemented!(),
        }
    }
}

impl<'ast, T> WithSpan for BooleanExpression<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        use BooleanExpression::*;
        match self {
            Select(e) => Select(e.span(span)),
            Identifier(e) => Identifier(e.span(span)),
            Conditional(e) => Conditional(e.span(span)),
            e => e,
        }
    }

    fn get_span(&self) -> Option<Span> {
        use BooleanExpression::*;
        match self {
            Select(e) => e.get_span(),
            Identifier(e) => e.get_span(),
            Conditional(e) => e.get_span(),
            e => unimplemented!(),
        }
    }
}

impl<'ast, T> WithSpan for UExpressionInner<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        use UExpressionInner::*;
        match self {
            Select(e) => Select(e.span(span)),
            Identifier(e) => Identifier(e.span(span)),
            Conditional(e) => Conditional(e.span(span)),
            e => e,
        }
    }

    fn get_span(&self) -> Option<Span> {
        use UExpressionInner::*;
        match self {
            Select(e) => e.get_span(),
            Identifier(e) => e.get_span(),
            Conditional(e) => e.get_span(),
            e => unimplemented!(),
        }
    }
}
