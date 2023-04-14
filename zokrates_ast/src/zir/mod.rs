pub mod canonicalizer;
pub mod folder;
mod from_typed;
mod identifier;
pub mod lqc;
mod parameter;
pub mod result_folder;
pub mod types;
mod uint;
mod variable;

pub use self::parameter::Parameter;
pub use self::types::{Type, UBitwidth};
pub use self::variable::Variable;
use crate::common::expressions::{BooleanValueExpression, UnaryExpression};
use crate::common::SourceMetadata;
use crate::common::{self, FlatEmbed, ModuleMap, Span, Value, WithSpan};
use crate::common::{
    expressions::{self, BinaryExpression, ValueExpression},
    operators::*,
};
use crate::typed::ConcreteType;
pub use crate::zir::uint::{ShouldReduce, UExpression, UExpressionInner, UMetadata};

use crate::zir::types::Signature;
use std::fmt;

use derivative::Derivative;
use zokrates_field::Field;

pub use self::folder::Folder;
pub use self::identifier::{Identifier, SourceIdentifier};
use serde::{Deserialize, Serialize};

/// A typed program as a collection of modules, one of them being the main
#[derive(Derivative)]
#[derivative(PartialEq, Hash)]
#[derive(Clone, Debug)]
pub struct ZirProgram<'ast, T> {
    pub main: ZirFunction<'ast, T>,
    pub module_map: ModuleMap,
}

impl<'ast, T: fmt::Display> fmt::Display for ZirProgram<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.main)
    }
}
/// A typed function
#[derive(Derivative)]
#[derivative(PartialEq, Hash, Eq)]
#[derive(Clone, Serialize, Deserialize)]
pub struct ZirFunction<'ast, T> {
    /// Arguments of the function
    pub arguments: Vec<Parameter<'ast>>,
    /// Vector of statements that are executed when running the function
    #[serde(borrow)]
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

        write!(f, "}}")
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

#[derive(Debug, Clone, PartialEq, Hash, Eq, Serialize, Deserialize)]
pub enum RuntimeError {
    SourceAssertion(SourceMetadata),
    SelectRangeCheck,
    DivisionByZero,
    IncompleteDynamicRange,
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeError::SourceAssertion(metadata) => write!(f, "{}", metadata),
            RuntimeError::SelectRangeCheck => write!(f, "Range check on array access"),
            RuntimeError::DivisionByZero => write!(f, "Division by zero"),
            RuntimeError::IncompleteDynamicRange => write!(f, "Dynamic comparison is incomplete"),
        }
    }
}

impl RuntimeError {
    pub fn mock() -> Self {
        RuntimeError::SourceAssertion(SourceMetadata::default())
    }
}

pub type AssemblyConstraint<'ast, T> =
    crate::common::statements::AssemblyConstraint<FieldElementExpression<'ast, T>>;
pub type AssemblyAssignment<'ast, T> =
    crate::common::statements::AssemblyAssignment<Vec<ZirAssignee<'ast>>, ZirFunction<'ast, T>>;

#[derive(Clone, PartialEq, Hash, Eq, Debug, Serialize, Deserialize)]
pub enum ZirAssemblyStatement<'ast, T> {
    #[serde(borrow)]
    Assignment(AssemblyAssignment<'ast, T>),
    Constraint(AssemblyConstraint<'ast, T>),
}

impl<'ast, T> ZirAssemblyStatement<'ast, T> {
    pub fn assignment(assignee: Vec<ZirAssignee<'ast>>, expression: ZirFunction<'ast, T>) -> Self {
        ZirAssemblyStatement::Assignment(AssemblyAssignment::new(assignee, expression))
    }

    pub fn constraint(
        left: FieldElementExpression<'ast, T>,
        right: FieldElementExpression<'ast, T>,
        metadata: SourceMetadata,
    ) -> Self {
        ZirAssemblyStatement::Constraint(AssemblyConstraint::new(left, right, metadata))
    }
}

impl<'ast, T> WithSpan for ZirAssemblyStatement<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        match self {
            ZirAssemblyStatement::Assignment(s) => ZirAssemblyStatement::Assignment(s.span(span)),
            ZirAssemblyStatement::Constraint(s) => ZirAssemblyStatement::Constraint(s.span(span)),
        }
    }

    fn get_span(&self) -> Option<Span> {
        match self {
            ZirAssemblyStatement::Assignment(s) => s.get_span(),
            ZirAssemblyStatement::Constraint(s) => s.get_span(),
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for ZirAssemblyStatement<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ZirAssemblyStatement::Assignment(ref s) => {
                write!(
                    f,
                    "{} <-- {};",
                    s.assignee
                        .iter()
                        .map(|a| a.to_string())
                        .collect::<Vec<_>>()
                        .join(", "),
                    s.expression
                )
            }
            ZirAssemblyStatement::Constraint(ref s) => {
                write!(f, "{}", s)
            }
        }
    }
}

pub type DefinitionStatement<'ast, T> =
    common::expressions::DefinitionStatement<ZirAssignee<'ast>, ZirExpression<'ast, T>>;
pub type AssertionStatement<'ast, T> =
    common::expressions::AssertionStatement<BooleanExpression<'ast, T>, RuntimeError>;
pub type ReturnStatement<'ast, T> =
    common::expressions::ReturnStatement<Vec<ZirExpression<'ast, T>>>;
pub type LogStatement<'ast, T> =
    common::statements::LogStatement<(ConcreteType, Vec<ZirExpression<'ast, T>>)>;

#[derive(Derivative)]
#[derivative(PartialEq, Hash)]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct IfElseStatement<'ast, T> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    #[serde(borrow)]
    pub condition: BooleanExpression<'ast, T>,
    pub consequence: Vec<ZirStatement<'ast, T>>,
    pub alternative: Vec<ZirStatement<'ast, T>>,
}

impl<'ast, T> IfElseStatement<'ast, T> {
    pub fn new(
        condition: BooleanExpression<'ast, T>,
        consequence: Vec<ZirStatement<'ast, T>>,
        alternative: Vec<ZirStatement<'ast, T>>,
    ) -> Self {
        Self {
            span: None,
            condition,
            consequence,
            alternative,
        }
    }
}

impl<'ast, T> WithSpan for IfElseStatement<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        Self { span, ..self }
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

#[derive(Derivative)]
#[derivative(PartialEq, Hash)]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MultipleDefinitionStatement<'ast, T> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    #[serde(borrow)]
    pub assignees: Vec<ZirAssignee<'ast>>,
    pub rhs: ZirExpressionList<'ast, T>,
}

impl<'ast, T> MultipleDefinitionStatement<'ast, T> {
    pub fn new(assignees: Vec<ZirAssignee<'ast>>, rhs: ZirExpressionList<'ast, T>) -> Self {
        Self {
            span: None,
            assignees,
            rhs,
        }
    }
}

impl<'ast, T> WithSpan for MultipleDefinitionStatement<'ast, T> {
    fn span(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

impl<'ast, T: fmt::Display> fmt::Display for MultipleDefinitionStatement<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, id) in self.assignees.iter().enumerate() {
            write!(f, "{}", id)?;
            if i < self.assignees.len() - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, " = {};", self.rhs)
    }
}

#[derive(Derivative)]
#[derivative(PartialEq, Hash)]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AssemblyBlockStatement<'ast, T> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    #[serde(borrow)]
    pub inner: Vec<ZirAssemblyStatement<'ast, T>>,
}

impl<'ast, T> AssemblyBlockStatement<'ast, T> {
    pub fn new(inner: Vec<ZirAssemblyStatement<'ast, T>>) -> Self {
        Self { span: None, inner }
    }
}

impl<'ast, T> WithSpan for AssemblyBlockStatement<'ast, T> {
    fn span(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

/// A statement in a `ZirFunction`
#[derive(Derivative)]
#[derivative(PartialEq, Hash)]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ZirStatement<'ast, T> {
    Return(ReturnStatement<'ast, T>),
    Definition(DefinitionStatement<'ast, T>),
    IfElse(IfElseStatement<'ast, T>),
    Assertion(AssertionStatement<'ast, T>),
    MultipleDefinition(MultipleDefinitionStatement<'ast, T>),
    Log(LogStatement<'ast, T>),
    #[serde(borrow)]
    Assembly(AssemblyBlockStatement<'ast, T>),
}

impl<'ast, T> ZirStatement<'ast, T> {
    pub fn definition(a: ZirAssignee<'ast>, e: ZirExpression<'ast, T>) -> Self {
        Self::Definition(DefinitionStatement::new(a, e))
    }

    pub fn multiple_definition(
        assignees: Vec<ZirAssignee<'ast>>,
        e: ZirExpressionList<'ast, T>,
    ) -> Self {
        Self::MultipleDefinition(MultipleDefinitionStatement::new(assignees, e))
    }

    pub fn assertion(e: BooleanExpression<'ast, T>, error: RuntimeError) -> Self {
        Self::Assertion(AssertionStatement::new(e, error))
    }

    pub fn ret(e: Vec<ZirExpression<'ast, T>>) -> Self {
        Self::Return(ReturnStatement::new(e))
    }

    pub fn assembly(s: Vec<ZirAssemblyStatement<'ast, T>>) -> Self {
        Self::Assembly(AssemblyBlockStatement::new(s))
    }

    pub fn if_else(
        condition: BooleanExpression<'ast, T>,
        consequence: Vec<ZirStatement<'ast, T>>,
        alternative: Vec<ZirStatement<'ast, T>>,
    ) -> Self {
        Self::IfElse(IfElseStatement::new(condition, consequence, alternative))
    }
}

impl<'ast, T> WithSpan for ZirStatement<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        use ZirStatement::*;

        match self {
            Return(e) => Return(e.span(span)),
            Definition(e) => Definition(e.span(span)),
            Assertion(e) => Assertion(e.span(span)),
            IfElse(e) => IfElse(e.span(span)),
            MultipleDefinition(e) => MultipleDefinition(e.span(span)),
            Log(e) => Log(e.span(span)),
            Assembly(e) => Assembly(e.span(span)),
        }
    }

    fn get_span(&self) -> Option<Span> {
        use ZirStatement::*;

        match self {
            Return(e) => e.get_span(),
            Definition(e) => e.get_span(),
            Assertion(e) => e.get_span(),
            IfElse(e) => e.get_span(),
            MultipleDefinition(e) => e.get_span(),
            Log(e) => e.get_span(),
            Assembly(e) => e.get_span(),
        }
    }
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
            ZirStatement::Return(ref s) => {
                write!(f, "return")?;
                if !s.inner.is_empty() {
                    write!(
                        f,
                        " {}",
                        s.inner
                            .iter()
                            .map(|e| e.to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    )?;
                }
                write!(f, ";")
            }
            ZirStatement::Definition(ref s) => {
                write!(f, "{}", s)
            }
            ZirStatement::IfElse(ref s) => {
                writeln!(f, "if {} {{", s.condition)?;
                for s in &s.consequence {
                    s.fmt_indented(f, depth + 1)?;
                    writeln!(f)?;
                }
                writeln!(f, "{}}} else {{", "\t".repeat(depth))?;
                for s in &s.alternative {
                    s.fmt_indented(f, depth + 1)?;
                    writeln!(f)?;
                }
                write!(f, "{}}}", "\t".repeat(depth))
            }
            ZirStatement::Assertion(ref s) => {
                write!(f, "assert({}", s.expression)?;
                match &s.error {
                    RuntimeError::SourceAssertion(message) => write!(f, ", \"{}\");", message),
                    error => write!(f, "); // {}", error),
                }
            }
            ZirStatement::MultipleDefinition(ref s) => {
                write!(f, "{}", s)
            }
            ZirStatement::Log(ref e) => write!(
                f,
                "log(\"{}\"), {});",
                e.format_string,
                e.expressions
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
            ZirStatement::Assembly(s) => {
                writeln!(f, "asm {{")?;
                for s in &s.inner {
                    writeln!(f, "{}{}", "\t".repeat(depth + 1), s)?;
                }
                write!(f, "{}}}", "\t".repeat(depth))
            }
        }
    }
}

pub trait Typed {
    fn get_type(&self) -> Type;
}

#[derive(Derivative)]
#[derivative(PartialEq, Hash)]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ConditionalExpression<'ast, T, E> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    #[serde(borrow)]
    pub condition: Box<BooleanExpression<'ast, T>>,
    pub consequence: Box<E>,
    pub alternative: Box<E>,
}

impl<'ast, T, E> ConditionalExpression<'ast, T, E> {
    pub fn new(condition: BooleanExpression<'ast, T>, consequence: E, alternative: E) -> Self {
        ConditionalExpression {
            span: None,
            condition: Box::new(condition),
            consequence: Box::new(consequence),
            alternative: Box::new(alternative),
        }
    }
}

impl<'ast, T: fmt::Display, E: fmt::Display> fmt::Display for ConditionalExpression<'ast, T, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} ? {} : {}",
            self.condition, self.consequence, self.alternative,
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

#[derive(Derivative)]
#[derivative(PartialEq, Hash)]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SelectExpression<'ast, T, E> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub array: Vec<E>,
    #[serde(borrow)]
    pub index: Box<UExpression<'ast, T>>,
}

impl<'ast, T, E> SelectExpression<'ast, T, E> {
    pub fn new(array: Vec<E>, index: UExpression<'ast, T>) -> Self {
        SelectExpression {
            span: None,
            array,
            index: Box::new(index),
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
#[derive(Derivative)]
#[derivative(PartialEq, Hash)]
#[derive(Clone, Serialize, Deserialize)]
pub enum ZirExpression<'ast, T> {
    #[serde(borrow)]
    Boolean(BooleanExpression<'ast, T>),
    FieldElement(FieldElementExpression<'ast, T>),
    Uint(UExpression<'ast, T>),
}

impl<'ast, T> WithSpan for ZirExpression<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        use ZirExpression::*;
        match self {
            Boolean(e) => Boolean(e.span(span)),
            FieldElement(e) => FieldElement(e.span(span)),
            Uint(e) => Uint(e.span(span)),
        }
    }

    fn get_span(&self) -> Option<Span> {
        use ZirExpression::*;
        match self {
            Boolean(e) => e.get_span(),
            FieldElement(e) => e.get_span(),
            Uint(e) => e.get_span(),
        }
    }
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

#[derive(Derivative)]
#[derivative(PartialEq, Hash)]
#[derive(Clone, Serialize, Deserialize)]
pub enum ZirExpressionList<'ast, T> {
    EmbedCall(
        FlatEmbed,
        Vec<u32>,
        #[serde(borrow)] Vec<ZirExpression<'ast, T>>,
    ),
}

pub type IdentifierExpression<'ast, E> = expressions::IdentifierExpression<Identifier<'ast>, E>;

/// An expression of type `field`
#[derive(Derivative)]
#[derivative(PartialEq, Eq, Hash)]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum FieldElementExpression<'ast, T> {
    Value(ValueExpression<T>),
    #[serde(borrow)]
    Identifier(IdentifierExpression<'ast, Self>),
    Select(SelectExpression<'ast, T, Self>),
    Add(BinaryExpression<OpAdd, Self, Self, Self>),
    Sub(BinaryExpression<OpSub, Self, Self, Self>),
    Mult(BinaryExpression<OpMul, Self, Self, Self>),
    Div(BinaryExpression<OpDiv, Self, Self, Self>),
    Pow(BinaryExpression<OpPow, Self, UExpression<'ast, T>, Self>),
    And(BinaryExpression<OpAnd, Self, Self, Self>),
    Or(BinaryExpression<OpOr, Self, Self, Self>),
    Xor(BinaryExpression<OpXor, Self, Self, Self>),
    LeftShift(BinaryExpression<OpLsh, Self, UExpression<'ast, T>, Self>),
    RightShift(BinaryExpression<OpRsh, Self, UExpression<'ast, T>, Self>),
    Conditional(ConditionalExpression<'ast, T, FieldElementExpression<'ast, T>>),
}

impl<'ast, T> FieldElementExpression<'ast, T> {
    pub fn number(n: T) -> Self {
        Self::Value(ValueExpression::new(n))
    }

    pub fn pow(self, right: UExpression<'ast, T>) -> Self {
        Self::Pow(BinaryExpression::new(self, right))
    }

    pub fn is_linear(&self) -> bool {
        match self {
            FieldElementExpression::Value(_) => true,
            FieldElementExpression::Identifier(_) => true,
            FieldElementExpression::Add(e) => e.left.is_linear() && e.right.is_linear(),
            FieldElementExpression::Sub(e) => e.left.is_linear() && e.right.is_linear(),
            FieldElementExpression::Mult(e) => matches!(
                (&*e.left, &*e.right),
                (FieldElementExpression::Value(_), _) | (_, FieldElementExpression::Value(_))
            ),
            _ => false,
        }
    }

    pub fn left_shift(self, by: UExpression<'ast, T>) -> Self {
        FieldElementExpression::LeftShift(BinaryExpression::new(self, by))
    }

    pub fn right_shift(self, by: UExpression<'ast, T>) -> Self {
        FieldElementExpression::RightShift(BinaryExpression::new(self, by))
    }
}

impl<'ast, T: Field> std::ops::BitAnd for FieldElementExpression<'ast, T> {
    type Output = Self;

    fn bitand(self, other: Self) -> Self {
        FieldElementExpression::And(BinaryExpression::new(self, other))
    }
}

impl<'ast, T: Field> std::ops::BitOr for FieldElementExpression<'ast, T> {
    type Output = Self;

    fn bitor(self, other: Self) -> Self {
        FieldElementExpression::Or(BinaryExpression::new(self, other))
    }
}

impl<'ast, T: Field> std::ops::BitXor for FieldElementExpression<'ast, T> {
    type Output = Self;

    fn bitxor(self, other: Self) -> Self {
        FieldElementExpression::Xor(BinaryExpression::new(self, other))
    }
}

/// An expression of type `bool`
#[derive(Derivative)]
#[derivative(PartialEq, Hash)]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum BooleanExpression<'ast, T> {
    Value(BooleanValueExpression),
    #[serde(borrow)]
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
            FieldElementExpression::Value(ref i) => write!(f, "{}", i),
            FieldElementExpression::Identifier(ref var) => write!(f, "{}", var),
            FieldElementExpression::Select(ref e) => write!(f, "{}", e),
            FieldElementExpression::Add(ref e) => write!(f, "{}", e),
            FieldElementExpression::Sub(ref e) => write!(f, "{}", e),
            FieldElementExpression::Mult(ref e) => write!(f, "{}", e),
            FieldElementExpression::Div(ref e) => write!(f, "{}", e),
            FieldElementExpression::Pow(ref e) => write!(f, "{}", e),
            FieldElementExpression::And(ref e) => write!(f, "{}", e),
            FieldElementExpression::Or(ref e) => write!(f, "{}", e),
            FieldElementExpression::Xor(ref e) => write!(f, "{}", e),
            FieldElementExpression::LeftShift(ref e) => write!(f, "{}", e),
            FieldElementExpression::RightShift(ref e) => write!(f, "{}", e),
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

impl<'ast, T> std::ops::Not for BooleanExpression<'ast, T> {
    type Output = Self;

    fn not(self) -> Self {
        Self::Not(UnaryExpression::new(self))
    }
}

impl<'ast, T> std::ops::BitAnd for BooleanExpression<'ast, T> {
    type Output = Self;

    fn bitand(self, other: Self) -> Self {
        Self::And(BinaryExpression::new(self, other))
    }
}

impl<'ast, T> std::ops::BitOr for BooleanExpression<'ast, T> {
    type Output = Self;

    fn bitor(self, other: Self) -> Self {
        Self::Or(BinaryExpression::new(self, other))
    }
}

impl<'ast, T> BooleanExpression<'ast, T> {
    pub fn uint_eq(left: UExpression<'ast, T>, right: UExpression<'ast, T>) -> Self {
        Self::UintEq(BinaryExpression::new(left, right))
    }

    pub fn bool_eq(left: BooleanExpression<'ast, T>, right: BooleanExpression<'ast, T>) -> Self {
        Self::BoolEq(BinaryExpression::new(left, right))
    }

    pub fn field_eq(
        left: FieldElementExpression<'ast, T>,
        right: FieldElementExpression<'ast, T>,
    ) -> Self {
        Self::FieldEq(BinaryExpression::new(left, right))
    }

    pub fn uint_lt(left: UExpression<'ast, T>, right: UExpression<'ast, T>) -> Self {
        Self::UintLt(BinaryExpression::new(left, right))
    }

    pub fn uint_le(left: UExpression<'ast, T>, right: UExpression<'ast, T>) -> Self {
        Self::UintLe(BinaryExpression::new(left, right))
    }

    pub fn field_lt(
        left: FieldElementExpression<'ast, T>,
        right: FieldElementExpression<'ast, T>,
    ) -> Self {
        Self::FieldLt(BinaryExpression::new(left, right))
    }

    pub fn field_le(
        left: FieldElementExpression<'ast, T>,
        right: FieldElementExpression<'ast, T>,
    ) -> Self {
        Self::FieldLe(BinaryExpression::new(left, right))
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

    fn value(_: Self::Value) -> Self::Inner;
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

    fn value(v: <Self as Value>::Value) -> Self::Inner {
        Self::Value(ValueExpression::new(v))
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

    fn value(v: <crate::zir::BooleanExpression<'ast, T> as Value>::Value) -> Self::Inner {
        Self::Value(ValueExpression::new(v))
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

    fn value(v: Self::Value) -> Self::Inner {
        UExpressionInner::Value(ValueExpression::new(v))
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

pub trait Constant: Sized {
    // return whether this is constant
    fn is_constant(&self) -> bool;
}

impl<'ast, T: Field> Constant for ZirExpression<'ast, T> {
    fn is_constant(&self) -> bool {
        match self {
            ZirExpression::FieldElement(e) => e.is_constant(),
            ZirExpression::Boolean(e) => e.is_constant(),
            ZirExpression::Uint(e) => e.is_constant(),
        }
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
            Value(e) => Value(e.span(span)),
            Sub(e) => Sub(e.span(span)),
            Mult(e) => Mult(e.span(span)),
            Div(e) => Div(e.span(span)),
            Pow(e) => Pow(e.span(span)),
            And(e) => And(e.span(span)),
            Or(e) => Or(e.span(span)),
            Xor(e) => Xor(e.span(span)),
            LeftShift(e) => LeftShift(e.span(span)),
            RightShift(e) => RightShift(e.span(span)),
        }
    }

    fn get_span(&self) -> Option<Span> {
        use FieldElementExpression::*;
        match self {
            Select(e) => e.get_span(),
            Identifier(e) => e.get_span(),
            Conditional(e) => e.get_span(),
            Add(e) => e.get_span(),
            Value(e) => e.get_span(),
            Sub(e) => e.get_span(),
            Mult(e) => e.get_span(),
            Div(e) => e.get_span(),
            Pow(e) => e.get_span(),
            And(e) => e.get_span(),
            Or(e) => e.get_span(),
            Xor(e) => e.get_span(),
            LeftShift(e) => e.get_span(),
            RightShift(e) => e.get_span(),
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
            Value(e) => Value(e.span(span)),
            FieldLt(e) => FieldLt(e.span(span)),
            FieldLe(e) => FieldLe(e.span(span)),
            FieldEq(e) => FieldEq(e.span(span)),
            UintLt(e) => UintLt(e.span(span)),
            UintLe(e) => UintLe(e.span(span)),
            UintEq(e) => UintEq(e.span(span)),
            BoolEq(e) => BoolEq(e.span(span)),
            Or(e) => Or(e.span(span)),
            And(e) => And(e.span(span)),
            Not(e) => Not(e.span(span)),
        }
    }

    fn get_span(&self) -> Option<Span> {
        use BooleanExpression::*;
        match self {
            Select(e) => e.get_span(),
            Identifier(e) => e.get_span(),
            Conditional(e) => e.get_span(),
            Value(e) => e.get_span(),
            FieldLt(e) => e.get_span(),
            FieldLe(e) => e.get_span(),
            FieldEq(e) => e.get_span(),
            UintLt(e) => e.get_span(),
            UintLe(e) => e.get_span(),
            UintEq(e) => e.get_span(),
            BoolEq(e) => e.get_span(),
            Or(e) => e.get_span(),
            And(e) => e.get_span(),
            Not(e) => e.get_span(),
        }
    }
}

impl<'ast, T> WithSpan for UExpression<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        Self {
            inner: self.inner.span(span),
            ..self
        }
    }

    fn get_span(&self) -> Option<Span> {
        self.inner.get_span()
    }
}

impl<'ast, T> WithSpan for UExpressionInner<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        use UExpressionInner::*;
        match self {
            Select(e) => Select(e.span(span)),
            Identifier(e) => Identifier(e.span(span)),
            Conditional(e) => Conditional(e.span(span)),
            Value(e) => Value(e.span(span)),
            Add(e) => Add(e.span(span)),
            Sub(e) => Sub(e.span(span)),
            Mult(e) => Mult(e.span(span)),
            Div(e) => Div(e.span(span)),
            Rem(e) => Rem(e.span(span)),
            Xor(e) => Xor(e.span(span)),
            And(e) => And(e.span(span)),
            Or(e) => Or(e.span(span)),
            LeftShift(e) => LeftShift(e.span(span)),
            RightShift(e) => RightShift(e.span(span)),
            Not(e) => Not(e.span(span)),
        }
    }

    fn get_span(&self) -> Option<Span> {
        use UExpressionInner::*;
        match self {
            Select(e) => e.get_span(),
            Identifier(e) => e.get_span(),
            Conditional(e) => e.get_span(),
            Value(e) => e.get_span(),
            Add(e) => e.get_span(),
            Sub(e) => e.get_span(),
            Mult(e) => e.get_span(),
            Div(e) => e.get_span(),
            Rem(e) => e.get_span(),
            Xor(e) => e.get_span(),
            And(e) => e.get_span(),
            Or(e) => e.get_span(),
            LeftShift(e) => e.get_span(),
            RightShift(e) => e.get_span(),
            Not(e) => e.get_span(),
        }
    }
}

impl<'ast, T: Field> Constant for FieldElementExpression<'ast, T> {
    fn is_constant(&self) -> bool {
        matches!(self, FieldElementExpression::Value(..))
    }
}

impl<'ast, T: Field> Constant for BooleanExpression<'ast, T> {
    fn is_constant(&self) -> bool {
        matches!(self, BooleanExpression::Value(..))
    }
}

impl<'ast, T: Field> Constant for UExpression<'ast, T> {
    fn is_constant(&self) -> bool {
        matches!(self.as_inner(), UExpressionInner::Value(..))
    }
}
