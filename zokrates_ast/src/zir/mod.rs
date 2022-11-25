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
use crate::common::{FlatEmbed, FormatString};
use crate::typed::identifier::IdTrait;
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
pub struct ZirProgram<I, T> {
    pub main: ZirFunction<I, T>,
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for ZirProgram<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.main)
    }
}
/// A typed function
#[derive(Clone, PartialEq, Eq)]
pub struct ZirFunction<I, T> {
    /// Arguments of the function
    pub arguments: Vec<Parameter<I>>,
    /// Vector of statements that are executed when running the function
    pub statements: Vec<ZirStatement<I, T>>,
    /// function signature
    pub signature: Signature,
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for ZirFunction<I, T> {
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

impl<I: fmt::Debug, T: fmt::Debug> fmt::Debug for ZirFunction<I, T> {
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

pub type ZirAssignee<I> = Variable<I>;

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
pub enum ZirStatement<I, T> {
    Return(Vec<ZirExpression<I, T>>),
    Definition(ZirAssignee<I>, ZirExpression<I, T>),
    IfElse(
        BooleanExpression<I, T>,
        Vec<ZirStatement<I, T>>,
        Vec<ZirStatement<I, T>>,
    ),
    Assertion(BooleanExpression<I, T>, RuntimeError),
    MultipleDefinition(Vec<ZirAssignee<I>>, ZirExpressionList<I, T>),
    Log(FormatString, Vec<(ConcreteType, Vec<ZirExpression<I, T>>)>),
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for ZirStatement<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.fmt_indented(f, 0)
    }
}

impl<I: fmt::Display, T: fmt::Display> ZirStatement<I, T> {
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
pub struct IdentifierExpression<I, E> {
    pub id: Identifier<I>,
    ty: PhantomData<E>,
}

impl<I: fmt::Display, E> fmt::Display for IdentifierExpression<I, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.id)
    }
}

impl<I, E> IdentifierExpression<I, E> {
    pub fn new(id: Identifier<I>) -> Self {
        IdentifierExpression {
            id,
            ty: PhantomData,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub struct ConditionalExpression<I, T, E> {
    pub condition: Box<BooleanExpression<I, T>>,
    pub consequence: Box<E>,
    pub alternative: Box<E>,
}

impl<I, T, E> ConditionalExpression<I, T, E> {
    pub fn new(condition: BooleanExpression<I, T>, consequence: E, alternative: E) -> Self {
        ConditionalExpression {
            condition: box condition,
            consequence: box consequence,
            alternative: box alternative,
        }
    }
}

impl<I: fmt::Display, T: fmt::Display, E: fmt::Display> fmt::Display
    for ConditionalExpression<I, T, E>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} ? {} : {}",
            self.condition, self.consequence, self.alternative
        )
    }
}

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub struct SelectExpression<I, T, E> {
    pub array: Vec<E>,
    pub index: Box<UExpression<I, T>>,
}

impl<I, T, E> SelectExpression<I, T, E> {
    pub fn new(array: Vec<E>, index: UExpression<I, T>) -> Self {
        SelectExpression {
            array,
            index: box index,
        }
    }
}

impl<I: fmt::Display, T: fmt::Display, E: fmt::Display> fmt::Display for SelectExpression<I, T, E> {
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

/// A typed expression
#[derive(Clone, PartialEq, Hash, Eq)]
pub enum ZirExpression<I, T> {
    Boolean(BooleanExpression<I, T>),
    FieldElement(FieldElementExpression<I, T>),
    Uint(UExpression<I, T>),
}

impl<I: IdTrait, T: fmt::Debug> From<BooleanExpression<I, T>> for ZirExpression<I, T> {
    fn from(e: BooleanExpression<I, T>) -> ZirExpression<I, T> {
        ZirExpression::Boolean(e)
    }
}

impl<I: IdTrait, T: fmt::Debug> From<FieldElementExpression<I, T>> for ZirExpression<I, T> {
    fn from(e: FieldElementExpression<I, T>) -> ZirExpression<I, T> {
        ZirExpression::FieldElement(e)
    }
}

impl<I: IdTrait, T: fmt::Debug> From<UExpression<I, T>> for ZirExpression<I, T> {
    fn from(e: UExpression<I, T>) -> ZirExpression<I, T> {
        ZirExpression::Uint(e)
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for ZirExpression<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ZirExpression::Boolean(ref e) => write!(f, "{}", e),
            ZirExpression::FieldElement(ref e) => write!(f, "{}", e),
            ZirExpression::Uint(ref e) => write!(f, "{}", e),
        }
    }
}

impl<I: fmt::Debug, T: fmt::Debug> fmt::Debug for ZirExpression<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ZirExpression::Boolean(ref e) => write!(f, "{:?}", e),
            ZirExpression::FieldElement(ref e) => write!(f, "{:?}", e),
            ZirExpression::Uint(ref e) => write!(f, "{:?}", e),
        }
    }
}

impl<I: IdTrait, T: fmt::Debug> Typed for ZirExpression<I, T> {
    fn get_type(&self) -> Type {
        match *self {
            ZirExpression::Boolean(ref e) => e.get_type(),
            ZirExpression::FieldElement(ref e) => e.get_type(),
            ZirExpression::Uint(ref e) => e.get_type(),
        }
    }
}

impl<I: IdTrait, T: fmt::Debug> Typed for FieldElementExpression<I, T> {
    fn get_type(&self) -> Type {
        Type::FieldElement
    }
}

impl<I: IdTrait, T: fmt::Debug> Typed for UExpression<I, T> {
    fn get_type(&self) -> Type {
        Type::Uint(self.bitwidth)
    }
}

impl<I: IdTrait, T: fmt::Debug> Typed for BooleanExpression<I, T> {
    fn get_type(&self) -> Type {
        Type::Boolean
    }
}

pub trait MultiTyped {
    fn get_types(&self) -> &Vec<Type>;
}

#[derive(Clone, PartialEq, Hash, Eq)]
pub enum ZirExpressionList<I, T> {
    EmbedCall(FlatEmbed, Vec<u32>, Vec<ZirExpression<I, T>>),
}

/// An expression of type `field`
#[derive(Clone, PartialEq, Hash, Eq, Debug)]
pub enum FieldElementExpression<I, T> {
    Number(T),
    Identifier(IdentifierExpression<I, Self>),
    Select(SelectExpression<I, T, Self>),
    Add(
        Box<FieldElementExpression<I, T>>,
        Box<FieldElementExpression<I, T>>,
    ),
    Sub(
        Box<FieldElementExpression<I, T>>,
        Box<FieldElementExpression<I, T>>,
    ),
    Mult(
        Box<FieldElementExpression<I, T>>,
        Box<FieldElementExpression<I, T>>,
    ),
    Div(
        Box<FieldElementExpression<I, T>>,
        Box<FieldElementExpression<I, T>>,
    ),
    Pow(Box<FieldElementExpression<I, T>>, Box<UExpression<I, T>>),
    Conditional(ConditionalExpression<I, T, FieldElementExpression<I, T>>),
}

/// An expression of type `bool`
#[derive(Clone, PartialEq, Hash, Eq, Debug)]
pub enum BooleanExpression<I, T> {
    Value(bool),
    Identifier(IdentifierExpression<I, Self>),
    Select(SelectExpression<I, T, Self>),
    FieldLt(
        Box<FieldElementExpression<I, T>>,
        Box<FieldElementExpression<I, T>>,
    ),
    FieldLe(
        Box<FieldElementExpression<I, T>>,
        Box<FieldElementExpression<I, T>>,
    ),
    FieldEq(
        Box<FieldElementExpression<I, T>>,
        Box<FieldElementExpression<I, T>>,
    ),
    UintLt(Box<UExpression<I, T>>, Box<UExpression<I, T>>),
    UintLe(Box<UExpression<I, T>>, Box<UExpression<I, T>>),
    UintEq(Box<UExpression<I, T>>, Box<UExpression<I, T>>),
    BoolEq(Box<BooleanExpression<I, T>>, Box<BooleanExpression<I, T>>),
    Or(Box<BooleanExpression<I, T>>, Box<BooleanExpression<I, T>>),
    And(Box<BooleanExpression<I, T>>, Box<BooleanExpression<I, T>>),
    Not(Box<BooleanExpression<I, T>>),
    Conditional(ConditionalExpression<I, T, BooleanExpression<I, T>>),
}

pub struct ConjunctionIterator<T> {
    current: Vec<T>,
}

impl<I, T> Iterator for ConjunctionIterator<BooleanExpression<I, T>> {
    type Item = BooleanExpression<I, T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.current.pop().and_then(|n| match n {
            BooleanExpression::And(box left, box right) => {
                self.current.push(left);
                self.current.push(right);
                self.next()
            }
            n => Some(n),
        })
    }
}

impl<I, T> BooleanExpression<I, T> {
    pub fn into_conjunction_iterator(self) -> ConjunctionIterator<Self> {
        ConjunctionIterator {
            current: vec![self],
        }
    }
}

// Downcasts
impl<I, T> From<ZirExpression<I, T>> for FieldElementExpression<I, T> {
    fn from(e: ZirExpression<I, T>) -> FieldElementExpression<I, T> {
        match e {
            ZirExpression::FieldElement(e) => e,
            _ => unreachable!("downcast failed"),
        }
    }
}

impl<I, T> From<ZirExpression<I, T>> for BooleanExpression<I, T> {
    fn from(e: ZirExpression<I, T>) -> BooleanExpression<I, T> {
        match e {
            ZirExpression::Boolean(e) => e,
            _ => unreachable!("downcast failed"),
        }
    }
}

impl<I, T> From<ZirExpression<I, T>> for UExpression<I, T> {
    fn from(e: ZirExpression<I, T>) -> UExpression<I, T> {
        match e {
            ZirExpression::Uint(e) => e,
            _ => unreachable!("downcast failed"),
        }
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for FieldElementExpression<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FieldElementExpression::Number(ref i) => write!(f, "{}", i),
            FieldElementExpression::Identifier(ref var) => write!(f, "{}", var),
            FieldElementExpression::Select(ref e) => write!(f, "{}", e),
            FieldElementExpression::Add(ref lhs, ref rhs) => write!(f, "({} + {})", lhs, rhs),
            FieldElementExpression::Sub(ref lhs, ref rhs) => write!(f, "({} - {})", lhs, rhs),
            FieldElementExpression::Mult(ref lhs, ref rhs) => write!(f, "({} * {})", lhs, rhs),
            FieldElementExpression::Div(ref lhs, ref rhs) => write!(f, "({} / {})", lhs, rhs),
            FieldElementExpression::Pow(ref lhs, ref rhs) => write!(f, "{}**{}", lhs, rhs),
            FieldElementExpression::Conditional(ref c) => {
                write!(f, "{}", c)
            }
        }
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for UExpression<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.inner {
            UExpressionInner::Value(ref v) => write!(f, "{}", v),
            UExpressionInner::Identifier(ref var) => write!(f, "{}", var),
            UExpressionInner::Select(ref e) => write!(f, "{}", e),
            UExpressionInner::Add(ref lhs, ref rhs) => write!(f, "({} + {})", lhs, rhs),
            UExpressionInner::Sub(ref lhs, ref rhs) => write!(f, "({} - {})", lhs, rhs),
            UExpressionInner::Mult(ref lhs, ref rhs) => write!(f, "({} * {})", lhs, rhs),
            UExpressionInner::Div(ref lhs, ref rhs) => write!(f, "({} * {})", lhs, rhs),
            UExpressionInner::Rem(ref lhs, ref rhs) => write!(f, "({} % {})", lhs, rhs),
            UExpressionInner::Xor(ref lhs, ref rhs) => write!(f, "({} ^ {})", lhs, rhs),
            UExpressionInner::And(ref lhs, ref rhs) => write!(f, "({} & {})", lhs, rhs),
            UExpressionInner::Or(ref lhs, ref rhs) => write!(f, "({} | {})", lhs, rhs),
            UExpressionInner::LeftShift(ref e, ref by) => write!(f, "({} << {})", e, by),
            UExpressionInner::RightShift(ref e, ref by) => write!(f, "({} >> {})", e, by),
            UExpressionInner::Not(ref e) => write!(f, "!{}", e),
            UExpressionInner::Conditional(ref c) => {
                write!(f, "{}", c)
            }
        }
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for BooleanExpression<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            BooleanExpression::Identifier(ref var) => write!(f, "{}", var),
            BooleanExpression::Value(b) => write!(f, "{}", b),
            BooleanExpression::Select(ref e) => write!(f, "{}", e),
            BooleanExpression::FieldLt(ref lhs, ref rhs) => write!(f, "({} < {})", lhs, rhs),
            BooleanExpression::UintLt(ref lhs, ref rhs) => write!(f, "({} < {})", lhs, rhs),
            BooleanExpression::FieldLe(ref lhs, ref rhs) => write!(f, "({} <= {})", lhs, rhs),
            BooleanExpression::UintLe(ref lhs, ref rhs) => write!(f, "({} <= {})", lhs, rhs),
            BooleanExpression::FieldEq(ref lhs, ref rhs) => write!(f, "({} == {})", lhs, rhs),
            BooleanExpression::BoolEq(ref lhs, ref rhs) => write!(f, "({} == {})", lhs, rhs),
            BooleanExpression::UintEq(ref lhs, ref rhs) => write!(f, "({} == {})", lhs, rhs),
            BooleanExpression::Or(ref lhs, ref rhs) => write!(f, "({} || {})", lhs, rhs),
            BooleanExpression::And(ref lhs, ref rhs) => write!(f, "({} && {})", lhs, rhs),
            BooleanExpression::Not(ref exp) => write!(f, "!{}", exp),
            BooleanExpression::Conditional(ref c) => {
                write!(f, "{}", c)
            }
        }
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for ZirExpressionList<I, T> {
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

impl<I: fmt::Debug, T: fmt::Debug> fmt::Debug for ZirExpressionList<I, T> {
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

// Common behaviour across expressions
pub trait Expr<I, T>: fmt::Display + PartialEq + From<ZirExpression<I, T>> {
    type Inner;
    type Ty: Clone + IntoType;

    fn ty(&self) -> &Self::Ty;

    fn into_inner(self) -> Self::Inner;

    fn as_inner(&self) -> &Self::Inner;

    fn as_inner_mut(&mut self) -> &mut Self::Inner;
}

impl<I: fmt::Display + PartialEq, T: Field> Expr<I, T> for FieldElementExpression<I, T> {
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

impl<I: fmt::Display + PartialEq, T: Field> Expr<I, T> for BooleanExpression<I, T> {
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

impl<I: fmt::Display + PartialEq, T: Field> Expr<I, T> for UExpression<I, T> {
    type Inner = UExpressionInner<I, T>;
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

pub trait Id<I, T>: Expr<I, T> {
    fn identifier(id: Identifier<I>) -> Self::Inner;
}

impl<I: fmt::Display + PartialEq, T: Field> Id<I, T> for FieldElementExpression<I, T> {
    fn identifier(id: Identifier<I>) -> Self::Inner {
        FieldElementExpression::Identifier(IdentifierExpression::new(id))
    }
}

impl<I: fmt::Display + PartialEq, T: Field> Id<I, T> for BooleanExpression<I, T> {
    fn identifier(id: Identifier<I>) -> Self::Inner {
        BooleanExpression::Identifier(IdentifierExpression::new(id))
    }
}

impl<I: fmt::Display + PartialEq, T: Field> Id<I, T> for UExpression<I, T> {
    fn identifier(id: Identifier<I>) -> Self::Inner {
        UExpressionInner::Identifier(IdentifierExpression::new(id))
    }
}

pub enum IdentifierOrExpression<I, T, E: Expr<I, T>> {
    Identifier(IdentifierExpression<I, E>),
    Expression(E::Inner),
}

pub trait Conditional<I, T> {
    fn conditional(
        condition: BooleanExpression<I, T>,
        consequence: Self,
        alternative: Self,
    ) -> Self;
}

pub enum ConditionalOrExpression<I, T, E: Expr<I, T>> {
    Conditional(ConditionalExpression<I, T, E>),
    Expression(E::Inner),
}

impl<I, T> Conditional<I, T> for FieldElementExpression<I, T> {
    fn conditional(
        condition: BooleanExpression<I, T>,
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

impl<I, T> Conditional<I, T> for BooleanExpression<I, T> {
    fn conditional(
        condition: BooleanExpression<I, T>,
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

impl<I, T> Conditional<I, T> for UExpression<I, T> {
    fn conditional(
        condition: BooleanExpression<I, T>,
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
pub trait Select<I, T>: Sized {
    fn select(array: Vec<Self>, index: UExpression<I, T>) -> Self;
}

pub enum SelectOrExpression<I, T, E: Expr<I, T>> {
    Select(SelectExpression<I, T, E>),
    Expression(E::Inner),
}

impl<I, T> Select<I, T> for FieldElementExpression<I, T> {
    fn select(array: Vec<Self>, index: UExpression<I, T>) -> Self {
        FieldElementExpression::Select(SelectExpression::new(array, index))
    }
}

impl<I, T> Select<I, T> for BooleanExpression<I, T> {
    fn select(array: Vec<Self>, index: UExpression<I, T>) -> Self {
        BooleanExpression::Select(SelectExpression::new(array, index))
    }
}

impl<I, T> Select<I, T> for UExpression<I, T> {
    fn select(array: Vec<Self>, index: UExpression<I, T>) -> Self {
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
