//! Module containing structs and enums to represent a program.
//!
//! @file absy.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

mod from_ast;
mod node;
pub mod parameter;
mod position;
pub mod types;
pub mod variable;

pub use self::node::{Node, NodeValue};
pub use self::parameter::{Parameter, ParameterNode};
pub use self::position::Position;
use self::types::{UnresolvedSignature, UnresolvedType, UserTypeId};
pub use self::variable::{Variable, VariableNode};
use crate::common::FlatEmbed;
use std::path::{Path, PathBuf};

use std::fmt;

use num_bigint::BigUint;
use std::collections::HashMap;

/// An identifier of a function or a variable
pub type Identifier<'ast> = &'ast str;

/// The identifier of a `Module`, typically a path or uri
pub type OwnedModuleId = PathBuf;
pub type ModuleId = Path;

/// A collection of `Module`s
pub type Modules<'ast> = HashMap<OwnedModuleId, Module<'ast>>;

/// A collection of `SymbolDeclaration`. Duplicates are allowed here as they are fine syntactically.
pub type Declarations<'ast> = Vec<SymbolDeclarationNode<'ast>>;

/// A `Program` is a collection of `Module`s and an id of the main `Module`
pub struct Program<'ast> {
    pub modules: HashMap<OwnedModuleId, Module<'ast>>,
    pub main: OwnedModuleId,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct SymbolIdentifier<'ast> {
    pub id: Identifier<'ast>,
    pub alias: Option<Identifier<'ast>>,
}

impl<'ast> From<Identifier<'ast>> for SymbolIdentifier<'ast> {
    fn from(id: &'ast str) -> Self {
        SymbolIdentifier { id, alias: None }
    }
}

impl<'ast> SymbolIdentifier<'ast> {
    pub fn alias(mut self, alias: Option<Identifier<'ast>>) -> Self {
        self.alias = alias;
        self
    }
    pub fn get_alias(&self) -> Identifier<'ast> {
        self.alias.unwrap_or(self.id)
    }
}

impl<'ast> fmt::Display for SymbolIdentifier<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}{}",
            self.id,
            self.alias.map(|a| format!(" as {}", a)).unwrap_or_default()
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalImport<'ast> {
    pub source: &'ast Path,
    pub id: SymbolIdentifier<'ast>,
}

pub type CanonicalImportNode<'ast> = Node<CanonicalImport<'ast>>;

impl<'ast> fmt::Display for CanonicalImport<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "from \"{}\" import {}", self.source.display(), self.id)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolImport<'ast> {
    pub module_id: OwnedModuleId,
    pub symbol_id: Identifier<'ast>,
}

pub type SymbolImportNode<'ast> = Node<SymbolImport<'ast>>;

impl<'ast> SymbolImport<'ast> {
    pub fn with_id_in_module<S: Into<Identifier<'ast>>, U: Into<OwnedModuleId>>(
        symbol_id: S,
        module_id: U,
    ) -> Self {
        SymbolImport {
            symbol_id: symbol_id.into(),
            module_id: module_id.into(),
        }
    }
}

impl<'ast> fmt::Display for SymbolImport<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "from \"{}\" import {}",
            self.module_id.display(),
            self.symbol_id
        )
    }
}

/// A declaration of a symbol
#[derive(Debug, PartialEq, Clone)]
pub struct SymbolDeclaration<'ast> {
    pub id: Identifier<'ast>,
    pub symbol: Symbol<'ast>,
}

#[allow(clippy::large_enum_variant)]
#[derive(Debug, PartialEq, Clone)]
pub enum SymbolDefinition<'ast> {
    Import(CanonicalImportNode<'ast>),
    Struct(StructDefinitionNode<'ast>),
    Constant(ConstantDefinitionNode<'ast>),
    Type(TypeDefinitionNode<'ast>),
    Function(FunctionNode<'ast>),
}

#[allow(clippy::large_enum_variant)]
#[derive(Debug, PartialEq, Clone)]
pub enum Symbol<'ast> {
    Here(SymbolDefinition<'ast>),
    There(SymbolImportNode<'ast>),
    Flat(FlatEmbed),
}

impl<'ast> fmt::Display for SymbolDeclaration<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.symbol {
            Symbol::Here(ref symbol) => match symbol {
                SymbolDefinition::Import(ref i) => write!(
                    f,
                    "from \"{}\" import {}",
                    i.value.source.display(),
                    i.value.id
                ),
                SymbolDefinition::Struct(ref s) => write!(f, "struct {}{}", self.id, s),
                SymbolDefinition::Constant(ref c) => write!(
                    f,
                    "const {} {} = {}",
                    c.value.ty, self.id, c.value.expression
                ),
                SymbolDefinition::Type(ref t) => {
                    write!(f, "type {}", self.id)?;
                    if !t.value.generics.is_empty() {
                        write!(
                            f,
                            "<{}>",
                            t.value
                                .generics
                                .iter()
                                .map(|g| g.to_string())
                                .collect::<Vec<_>>()
                                .join(", ")
                        )?;
                    }
                    write!(f, " = {}", t.value.ty)
                }
                SymbolDefinition::Function(ref func) => {
                    write!(f, "def {}{}", self.id, func)
                }
            },
            Symbol::There(ref i) => write!(
                f,
                "from \"{}\" import {} as {}",
                i.value.module_id.display(),
                i.value.symbol_id,
                self.id
            ),
            Symbol::Flat(ref flat_fun) => {
                write!(f, "def {}{}:\n\t// hidden", self.id, flat_fun.signature())
            }
        }
    }
}

pub type SymbolDeclarationNode<'ast> = Node<SymbolDeclaration<'ast>>;

/// A module as a collection of `FunctionDeclaration`s
#[derive(Debug, Clone, PartialEq)]
pub struct Module<'ast> {
    /// Symbols of the module
    pub symbols: Declarations<'ast>,
}

impl<'ast> Module<'ast> {
    pub fn with_symbols<I: IntoIterator<Item = SymbolDeclarationNode<'ast>>>(i: I) -> Self {
        Module {
            symbols: i.into_iter().collect(),
        }
    }
}

pub type UnresolvedTypeNode<'ast> = Node<UnresolvedType<'ast>>;

/// A struct type definition
#[derive(Debug, Clone, PartialEq)]
pub struct StructDefinition<'ast> {
    pub generics: Vec<ConstantGenericNode<'ast>>,
    pub fields: Vec<StructDefinitionFieldNode<'ast>>,
}

impl<'ast> fmt::Display for StructDefinition<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !self.generics.is_empty() {
            write!(
                f,
                "<{}> ",
                self.generics
                    .iter()
                    .map(|g| g.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )?;
        }
        writeln!(f, "{{")?;
        for field in &self.fields {
            writeln!(f, "  {}", field)?;
        }
        write!(f, "}}",)
    }
}

pub type StructDefinitionNode<'ast> = Node<StructDefinition<'ast>>;

/// A struct type definition
#[derive(Debug, Clone, PartialEq)]
pub struct StructDefinitionField<'ast> {
    pub id: Identifier<'ast>,
    pub ty: UnresolvedTypeNode<'ast>,
}

impl<'ast> fmt::Display for StructDefinitionField<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self.ty, self.id)
    }
}

type StructDefinitionFieldNode<'ast> = Node<StructDefinitionField<'ast>>;

#[derive(Debug, Clone, PartialEq)]
pub struct ConstantDefinition<'ast> {
    pub ty: UnresolvedTypeNode<'ast>,
    pub expression: ExpressionNode<'ast>,
}

pub type ConstantDefinitionNode<'ast> = Node<ConstantDefinition<'ast>>;

impl<'ast> fmt::Display for ConstantDefinition<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "const {} _ = {}", self.ty, self.expression)
    }
}

/// A type definition
#[derive(Debug, Clone, PartialEq)]
pub struct TypeDefinition<'ast> {
    pub generics: Vec<ConstantGenericNode<'ast>>,
    pub ty: UnresolvedTypeNode<'ast>,
}

pub type TypeDefinitionNode<'ast> = Node<TypeDefinition<'ast>>;

impl<'ast> fmt::Display for TypeDefinition<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "type _")?;
        if !self.generics.is_empty() {
            write!(
                f,
                "<{}>",
                self.generics
                    .iter()
                    .map(|g| g.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )?;
        }
        write!(f, " = {}", self.ty)
    }
}

impl<'ast> fmt::Display for Module<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let res = self
            .symbols
            .iter()
            .map(|x| format!("{}", x))
            .collect::<Vec<_>>();
        write!(f, "{}", res.join("\n"))
    }
}

pub type ConstantGenericNode<'ast> = Node<Identifier<'ast>>;

/// A function defined locally
#[derive(Debug, Clone, PartialEq)]
pub struct Function<'ast> {
    /// Arguments of the function
    pub arguments: Vec<ParameterNode<'ast>>,
    /// Vector of statements that are executed when running the function
    pub statements: Vec<StatementNode<'ast>>,
    /// function signature
    pub signature: UnresolvedSignature<'ast>,
}

pub type FunctionNode<'ast> = Node<Function<'ast>>;

impl<'ast> fmt::Display for Function<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !self.signature.generics.is_empty() {
            write!(
                f,
                "<{}>",
                self.signature
                    .generics
                    .iter()
                    .map(|g| g.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )?;
        }

        write!(
            f,
            "({}) {{\n{}\n}}",
            self.arguments
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>()
                .join(","),
            self.statements
                .iter()
                .map(|x| format!("\t{}", x))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

/// Something that we can assign to
#[derive(Debug, Clone, PartialEq)]
pub enum Assignee<'ast> {
    Identifier(Identifier<'ast>),
    Select(Box<AssigneeNode<'ast>>, Box<RangeOrExpression<'ast>>),
    Member(Box<AssigneeNode<'ast>>, Box<Identifier<'ast>>),
    Element(Box<AssigneeNode<'ast>>, u32),
}

pub type AssigneeNode<'ast> = Node<Assignee<'ast>>;

impl<'ast> fmt::Display for Assignee<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Assignee::Identifier(ref s) => write!(f, "{}", s),
            Assignee::Select(ref a, ref e) => write!(f, "{}[{}]", a, e),
            Assignee::Member(ref s, ref m) => write!(f, "{}.{}", s, m),
            Assignee::Element(ref s, i) => write!(f, "{}.{}", s, i),
        }
    }
}

/// A statement in a `Function`
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, PartialEq)]
pub enum Statement<'ast> {
    Return(Option<ExpressionNode<'ast>>),
    Definition(VariableNode<'ast>, ExpressionNode<'ast>),
    Assignment(AssigneeNode<'ast>, ExpressionNode<'ast>),
    Assertion(ExpressionNode<'ast>, Option<String>),
    For(
        VariableNode<'ast>,
        ExpressionNode<'ast>,
        ExpressionNode<'ast>,
        Vec<StatementNode<'ast>>,
    ),
    Log(&'ast str, Vec<ExpressionNode<'ast>>),
}

pub type StatementNode<'ast> = Node<Statement<'ast>>;

impl<'ast> fmt::Display for Statement<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Statement::Return(ref expr) => {
                write!(f, "return")?;
                match expr {
                    Some(e) => write!(f, " {};", e),
                    None => write!(f, ";"),
                }
            }
            Statement::Definition(ref var, ref rhs) => {
                write!(f, "{} = {};", var, rhs)
            }
            Statement::Assignment(ref lhs, ref rhs) => write!(f, "{} = {};", lhs, rhs),
            Statement::Assertion(ref e, ref message) => {
                write!(f, "assert({}", e)?;
                match message {
                    Some(m) => write!(f, ", \"{}\");", m),
                    None => write!(f, ");"),
                }
            }
            Statement::For(ref var, ref start, ref stop, ref list) => {
                writeln!(f, "for {} in {}..{} {{", var, start, stop)?;
                for l in list {
                    writeln!(f, "\t\t{}", l)?;
                }
                write!(f, "\t}}")
            }
            Statement::Log(ref l, ref expressions) => write!(
                f,
                "log({}, {})",
                l,
                expressions
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

/// An element of an inline array, can be a spread `...a` or an expression `a`
#[derive(Debug, Clone, PartialEq)]
pub enum SpreadOrExpression<'ast> {
    Spread(SpreadNode<'ast>),
    Expression(ExpressionNode<'ast>),
}

impl<'ast> From<ExpressionNode<'ast>> for SpreadOrExpression<'ast> {
    fn from(e: ExpressionNode<'ast>) -> SpreadOrExpression<'ast> {
        SpreadOrExpression::Expression(e)
    }
}

impl<'ast> fmt::Display for SpreadOrExpression<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            SpreadOrExpression::Spread(ref s) => write!(f, "{}", s),
            SpreadOrExpression::Expression(ref e) => write!(f, "{}", e),
        }
    }
}

/// The index in an array selector. Can be a range or an expression.
#[derive(Debug, Clone, PartialEq)]
pub enum RangeOrExpression<'ast> {
    Range(RangeNode<'ast>),
    Expression(ExpressionNode<'ast>),
}

impl<'ast> fmt::Display for RangeOrExpression<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            RangeOrExpression::Range(ref s) => write!(f, "{}", s),
            RangeOrExpression::Expression(ref e) => write!(f, "{}", e),
        }
    }
}

/// A spread
#[derive(Debug, Clone, PartialEq)]
pub struct Spread<'ast> {
    pub expression: ExpressionNode<'ast>,
}

pub type SpreadNode<'ast> = Node<Spread<'ast>>;

impl<'ast> fmt::Display for Spread<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "...{}", self.expression)
    }
}

/// A range
#[derive(Debug, Clone, PartialEq)]
pub struct Range<'ast> {
    pub from: Option<ExpressionNode<'ast>>,
    pub to: Option<ExpressionNode<'ast>>,
}

pub type RangeNode<'ast> = Node<Range<'ast>>;

impl<'ast> fmt::Display for Range<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}..{}",
            self.from
                .as_ref()
                .map(|e| e.to_string())
                .unwrap_or_else(|| "".to_string()),
            self.to
                .as_ref()
                .map(|e| e.to_string())
                .unwrap_or_else(|| "".to_string())
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConditionalKind {
    IfElse,
    Ternary,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ConditionalExpression<'ast> {
    pub condition: Box<ExpressionNode<'ast>>,
    pub consequence_statements: Vec<StatementNode<'ast>>,
    pub consequence: Box<ExpressionNode<'ast>>,
    pub alternative_statements: Vec<StatementNode<'ast>>,
    pub alternative: Box<ExpressionNode<'ast>>,
    pub kind: ConditionalKind,
}

impl<'ast> fmt::Display for ConditionalExpression<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.kind {
            ConditionalKind::IfElse => {
                writeln!(f, "if {} {{", self.condition)?;
                for cs in self.consequence_statements.iter() {
                    writeln!(f, "\t{}", cs)?;
                }
                writeln!(f, "\t{}", self.consequence)?;
                write!(f, "}} else {{")?;
                for als in self.alternative_statements.iter() {
                    writeln!(f, "\t{}", als)?;
                }
                writeln!(f, "\t{}", self.alternative)?;
                write!(f, "}}")
            }
            ConditionalKind::Ternary => {
                write!(
                    f,
                    "{} ? {} : {}",
                    self.condition, self.consequence, self.alternative
                )
            }
        }
    }
}

/// An expression
#[derive(Debug, Clone, PartialEq)]
pub enum Expression<'ast> {
    IntConstant(BigUint),
    FieldConstant(BigUint),
    BooleanConstant(bool),
    U8Constant(u8),
    U16Constant(u16),
    U32Constant(u32),
    U64Constant(u64),
    Identifier(Identifier<'ast>),
    Add(Box<ExpressionNode<'ast>>, Box<ExpressionNode<'ast>>),
    Sub(Box<ExpressionNode<'ast>>, Box<ExpressionNode<'ast>>),
    Mult(Box<ExpressionNode<'ast>>, Box<ExpressionNode<'ast>>),
    Div(Box<ExpressionNode<'ast>>, Box<ExpressionNode<'ast>>),
    Rem(Box<ExpressionNode<'ast>>, Box<ExpressionNode<'ast>>),
    Pow(Box<ExpressionNode<'ast>>, Box<ExpressionNode<'ast>>),
    Neg(Box<ExpressionNode<'ast>>),
    Pos(Box<ExpressionNode<'ast>>),
    Conditional(Box<ConditionalExpression<'ast>>),
    FunctionCall(
        Box<ExpressionNode<'ast>>,
        Option<Vec<Option<ExpressionNode<'ast>>>>,
        Vec<ExpressionNode<'ast>>,
    ),
    Lt(Box<ExpressionNode<'ast>>, Box<ExpressionNode<'ast>>),
    Le(Box<ExpressionNode<'ast>>, Box<ExpressionNode<'ast>>),
    Eq(Box<ExpressionNode<'ast>>, Box<ExpressionNode<'ast>>),
    Ge(Box<ExpressionNode<'ast>>, Box<ExpressionNode<'ast>>),
    Gt(Box<ExpressionNode<'ast>>, Box<ExpressionNode<'ast>>),
    And(Box<ExpressionNode<'ast>>, Box<ExpressionNode<'ast>>),
    Not(Box<ExpressionNode<'ast>>),
    InlineArray(Vec<SpreadOrExpression<'ast>>),
    ArrayInitializer(Box<ExpressionNode<'ast>>, Box<ExpressionNode<'ast>>),
    InlineStruct(UserTypeId, Vec<(Identifier<'ast>, ExpressionNode<'ast>)>),
    InlineTuple(Vec<ExpressionNode<'ast>>),
    Select(Box<ExpressionNode<'ast>>, Box<RangeOrExpression<'ast>>),
    Member(Box<ExpressionNode<'ast>>, Box<Identifier<'ast>>),
    Element(Box<ExpressionNode<'ast>>, u32),
    Or(Box<ExpressionNode<'ast>>, Box<ExpressionNode<'ast>>),
    BitXor(Box<ExpressionNode<'ast>>, Box<ExpressionNode<'ast>>),
    BitAnd(Box<ExpressionNode<'ast>>, Box<ExpressionNode<'ast>>),
    BitOr(Box<ExpressionNode<'ast>>, Box<ExpressionNode<'ast>>),
    LeftShift(Box<ExpressionNode<'ast>>, Box<ExpressionNode<'ast>>),
    RightShift(Box<ExpressionNode<'ast>>, Box<ExpressionNode<'ast>>),
}

pub type ExpressionNode<'ast> = Node<Expression<'ast>>;

impl<'ast> fmt::Display for Expression<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Expression::FieldConstant(ref i) => write!(f, "{}", i.to_str_radix(10)),
            Expression::U8Constant(ref i) => write!(f, "{}", i),
            Expression::U16Constant(ref i) => write!(f, "{}", i),
            Expression::U32Constant(ref i) => write!(f, "{}", i),
            Expression::U64Constant(ref i) => write!(f, "{}", i),
            Expression::IntConstant(ref i) => write!(f, "{}", i),
            Expression::Identifier(ref var) => write!(f, "{}", var),
            Expression::Add(ref lhs, ref rhs) => write!(f, "({} + {})", lhs, rhs),
            Expression::Sub(ref lhs, ref rhs) => write!(f, "({} - {})", lhs, rhs),
            Expression::Mult(ref lhs, ref rhs) => write!(f, "({} * {})", lhs, rhs),
            Expression::Div(ref lhs, ref rhs) => write!(f, "({} / {})", lhs, rhs),
            Expression::Rem(ref lhs, ref rhs) => write!(f, "({} % {})", lhs, rhs),
            Expression::Pow(ref lhs, ref rhs) => write!(f, "({}**{})", lhs, rhs),
            Expression::Neg(ref e) => write!(f, "(-{})", e),
            Expression::Pos(ref e) => write!(f, "(+{})", e),
            Expression::BooleanConstant(b) => write!(f, "{}", b),
            Expression::Conditional(ref c) => write!(f, "{}", c),
            Expression::FunctionCall(ref i, ref g, ref p) => {
                if let Some(g) = g {
                    write!(
                        f,
                        "::<{}>",
                        g.iter()
                            .map(|g| g
                                .as_ref()
                                .map(|g| g.to_string())
                                .unwrap_or_else(|| "_".into()))
                            .collect::<Vec<_>>()
                            .join(", "),
                    )?;
                }
                write!(f, "{}(", i)?;
                for (i, param) in p.iter().enumerate() {
                    write!(f, "{}", param)?;
                    if i < p.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            Expression::Lt(ref lhs, ref rhs) => write!(f, "({} < {})", lhs, rhs),
            Expression::Le(ref lhs, ref rhs) => write!(f, "({} <= {})", lhs, rhs),
            Expression::Eq(ref lhs, ref rhs) => write!(f, "({} == {})", lhs, rhs),
            Expression::Ge(ref lhs, ref rhs) => write!(f, "({} >= {})", lhs, rhs),
            Expression::Gt(ref lhs, ref rhs) => write!(f, "({} > {})", lhs, rhs),
            Expression::And(ref lhs, ref rhs) => write!(f, "({} && {})", lhs, rhs),
            Expression::Not(ref exp) => write!(f, "!{}", exp),
            Expression::InlineArray(ref exprs) => {
                write!(f, "[")?;
                for (i, e) in exprs.iter().enumerate() {
                    write!(f, "{}", e)?;
                    if i < exprs.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "]")
            }
            Expression::InlineTuple(ref exprs) => {
                write!(f, "(")?;
                match exprs.len() {
                    1 => write!(f, "{},", exprs[0]),
                    _ => write!(
                        f,
                        "{}",
                        exprs
                            .iter()
                            .map(|e| e.to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                }?;
                write!(f, ")")
            }
            Expression::ArrayInitializer(ref e, ref count) => write!(f, "[{}; {}]", e, count),
            Expression::InlineStruct(ref id, ref members) => {
                write!(f, "{} {{", id)?;
                for (i, (member_id, e)) in members.iter().enumerate() {
                    write!(f, "{}: {}", member_id, e)?;
                    if i < members.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "}}")
            }
            Expression::Select(ref array, ref index) => write!(f, "{}[{}]", array, index),
            Expression::Member(ref struc, ref id) => write!(f, "{}.{}", struc, id),
            Expression::Element(ref tuple, ref id) => write!(f, "{}.{}", tuple, id),
            Expression::Or(ref lhs, ref rhs) => write!(f, "({} || {})", lhs, rhs),
            Expression::BitXor(ref lhs, ref rhs) => write!(f, "({} ^ {})", lhs, rhs),
            Expression::BitAnd(ref lhs, ref rhs) => write!(f, "({} & {})", lhs, rhs),
            Expression::BitOr(ref lhs, ref rhs) => write!(f, "({} | {})", lhs, rhs),
            Expression::LeftShift(ref lhs, ref rhs) => write!(f, "({} << {})", lhs, rhs),
            Expression::RightShift(ref lhs, ref rhs) => write!(f, "({} >> {})", lhs, rhs),
        }
    }
}
