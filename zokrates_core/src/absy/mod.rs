//! Module containing structs and enums to represent a program.
//!
//! @file absy.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

mod from_ast;
mod node;
pub mod parameter;
pub mod types;
pub mod variable;

pub use crate::absy::node::{Node, NodeValue};
pub use crate::absy::parameter::{Parameter, ParameterNode};
use crate::absy::types::{FunctionIdentifier, UnresolvedSignature, UnresolvedType, UserTypeId};
pub use crate::absy::variable::{Variable, VariableNode};
use crate::embed::FlatEmbed;
use std::path::{Path, PathBuf};

use crate::imports::ImportNode;
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

/// A declaration of a `FunctionSymbol`, be it from an import or a function definition
#[derive(PartialEq, Clone, Debug)]
pub struct SymbolDeclaration<'ast> {
    pub id: Identifier<'ast>,
    pub symbol: Symbol<'ast>,
}

#[derive(PartialEq, Clone)]
pub enum Symbol<'ast> {
    HereType(StructDefinitionNode<'ast>),
    HereFunction(FunctionNode<'ast>),
    There(SymbolImportNode<'ast>),
    Flat(FlatEmbed),
}

impl<'ast> fmt::Debug for Symbol<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Symbol::HereType(t) => write!(f, "HereType({:?})", t),
            Symbol::HereFunction(fun) => write!(f, "HereFunction({:?})", fun),
            Symbol::There(t) => write!(f, "There({:?})", t),
            Symbol::Flat(flat) => write!(f, "Flat({:?})", flat),
        }
    }
}

impl<'ast> fmt::Display for SymbolDeclaration<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.symbol {
            Symbol::HereType(ref t) => write!(f, "struct {} {}", self.id, t),
            Symbol::HereFunction(ref fun) => write!(f, "def {}{}", self.id, fun),
            Symbol::There(ref import) => write!(f, "import {} as {}", import, self.id),
            Symbol::Flat(ref flat_fun) => {
                write!(f, "def {}{}:\n\t// hidden", self.id, flat_fun.signature())
            }
        }
    }
}

pub type SymbolDeclarationNode<'ast> = Node<SymbolDeclaration<'ast>>;

/// A module as a collection of `FunctionDeclaration`s
#[derive(Clone, PartialEq)]
pub struct Module<'ast> {
    /// Symbols of the module
    pub symbols: Declarations<'ast>,
    pub imports: Vec<ImportNode<'ast>>, // we still use `imports` as they are not directly converted into `FunctionDeclaration`s after the importer is done, `imports` is empty
}

impl<'ast> Module<'ast> {
    pub fn with_symbols<I: IntoIterator<Item = SymbolDeclarationNode<'ast>>>(i: I) -> Self {
        Module {
            symbols: i.into_iter().collect(),
            imports: vec![],
        }
    }

    pub fn imports<I: IntoIterator<Item = ImportNode<'ast>>>(mut self, i: I) -> Self {
        self.imports = i.into_iter().collect();
        self
    }
}

pub type UnresolvedTypeNode<'ast> = Node<UnresolvedType<'ast>>;

/// A struct type definition
#[derive(Debug, Clone, PartialEq)]
pub struct StructDefinition<'ast> {
    pub fields: Vec<StructDefinitionFieldNode<'ast>>,
}

impl<'ast> fmt::Display for StructDefinition<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            self.fields
                .iter()
                .map(|fi| fi.to_string())
                .collect::<Vec<_>>()
                .join("\n")
        )
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
        write!(f, "{}: {},", self.id, self.ty)
    }
}

type StructDefinitionFieldNode<'ast> = Node<StructDefinitionField<'ast>>;

/// An import
#[derive(Debug, Clone, PartialEq)]
pub struct SymbolImport<'ast> {
    /// the id of the symbol in the target module. Note: there may be many candidates as imports statements do not specify the signature. In that case they must all be functions however.
    pub symbol_id: Identifier<'ast>,
    /// the id of the module to import from
    pub module_id: OwnedModuleId,
}

type SymbolImportNode<'ast> = Node<SymbolImport<'ast>>;

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
            "{} from {}",
            self.symbol_id,
            self.module_id.display().to_string()
        )
    }
}

impl<'ast> fmt::Display for Module<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut res = vec![];
        res.extend(
            self.imports
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>(),
        );
        res.extend(
            self.symbols
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>(),
        );
        write!(f, "{}", res.join("\n"))
    }
}

impl<'ast> fmt::Debug for Module<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "module(\n\timports:\n\t\t{}\n\tsymbols:\n\t\t{}\n)",
            self.imports
                .iter()
                .map(|x| format!("{:?}", x))
                .collect::<Vec<_>>()
                .join("\n\t\t"),
            self.symbols
                .iter()
                .map(|x| format!("{:?}", x))
                .collect::<Vec<_>>()
                .join("\n\t\t")
        )
    }
}

pub type ConstantGenericNode<'ast> = Node<Identifier<'ast>>;

/// A function defined locally
#[derive(Clone, PartialEq)]
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
            "({}):\n{}",
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

impl<'ast> fmt::Debug for Function<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Function(arguments: {:?}, ...):\n{}",
            self.arguments,
            self.statements
                .iter()
                .map(|x| format!("\t{:?}", x))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

/// Something that we can assign to
#[derive(Clone, PartialEq)]
pub enum Assignee<'ast> {
    Identifier(Identifier<'ast>),
    Select(Box<AssigneeNode<'ast>>, Box<RangeOrExpression<'ast>>),
    Member(Box<AssigneeNode<'ast>>, Box<Identifier<'ast>>),
}

pub type AssigneeNode<'ast> = Node<Assignee<'ast>>;

impl<'ast> fmt::Debug for Assignee<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Assignee::Identifier(ref s) => write!(f, "Identifier({:?})", s),
            Assignee::Select(ref a, ref e) => write!(f, "Select({:?}[{:?}])", a, e),
            Assignee::Member(ref s, ref m) => write!(f, "Member({:?}.{:?})", s, m),
        }
    }
}

impl<'ast> fmt::Display for Assignee<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Assignee::Identifier(ref s) => write!(f, "{}", s),
            Assignee::Select(ref a, ref e) => write!(f, "{}[{}]", a, e),
            Assignee::Member(ref s, ref m) => write!(f, "{}.{}", s, m),
        }
    }
}

/// A statement in a `Function`
#[allow(clippy::large_enum_variant)]
#[derive(Clone, PartialEq)]
pub enum Statement<'ast> {
    Return(ExpressionListNode<'ast>),
    Declaration(VariableNode<'ast>),
    Definition(AssigneeNode<'ast>, ExpressionNode<'ast>),
    Assertion(ExpressionNode<'ast>),
    For(
        VariableNode<'ast>,
        ExpressionNode<'ast>,
        ExpressionNode<'ast>,
        Vec<StatementNode<'ast>>,
    ),
    MultipleDefinition(Vec<AssigneeNode<'ast>>, ExpressionNode<'ast>),
}

pub type StatementNode<'ast> = Node<Statement<'ast>>;

impl<'ast> fmt::Display for Statement<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Statement::Return(ref expr) => write!(f, "return {}", expr),
            Statement::Declaration(ref var) => write!(f, "{}", var),
            Statement::Definition(ref lhs, ref rhs) => write!(f, "{} = {}", lhs, rhs),
            Statement::Assertion(ref e) => write!(f, "assert({})", e),
            Statement::For(ref var, ref start, ref stop, ref list) => {
                writeln!(f, "for {} in {}..{} do", var, start, stop)?;
                for l in list {
                    writeln!(f, "\t\t{}", l)?;
                }
                write!(f, "\tendfor")
            }
            Statement::MultipleDefinition(ref ids, ref rhs) => {
                for (i, id) in ids.iter().enumerate() {
                    write!(f, "{}", id)?;
                    if i < ids.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, " = {}", rhs)
            }
        }
    }
}

impl<'ast> fmt::Debug for Statement<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Statement::Return(ref expr) => write!(f, "Return({:?})", expr),
            Statement::Declaration(ref var) => write!(f, "Declaration({:?})", var),
            Statement::Definition(ref lhs, ref rhs) => {
                write!(f, "Definition({:?}, {:?})", lhs, rhs)
            }
            Statement::Assertion(ref e) => write!(f, "Assertion({:?})", e),
            Statement::For(ref var, ref start, ref stop, ref list) => {
                writeln!(f, "for {:?} in {:?}..{:?} do", var, start, stop)?;
                for l in list {
                    writeln!(f, "\t\t{:?}", l)?;
                }
                write!(f, "\tendfor")
            }
            Statement::MultipleDefinition(ref lhs, ref rhs) => {
                write!(f, "MultipleDefinition({:?}, {:?})", lhs, rhs)
            }
        }
    }
}

/// An element of an inline array, can be a spread `...a` or an expression `a`
#[derive(Clone, PartialEq)]
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

impl<'ast> fmt::Debug for SpreadOrExpression<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            SpreadOrExpression::Spread(ref s) => write!(f, "{:?}", s),
            SpreadOrExpression::Expression(ref e) => write!(f, "{:?}", e),
        }
    }
}

/// The index in an array selector. Can be a range or an expression.
#[derive(Clone, PartialEq)]
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

impl<'ast> fmt::Debug for RangeOrExpression<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            RangeOrExpression::Range(ref s) => write!(f, "{:?}", s),
            RangeOrExpression::Expression(ref e) => write!(f, "{:?}", e),
        }
    }
}

pub type SpreadNode<'ast> = Node<Spread<'ast>>;

impl<'ast> fmt::Display for Spread<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "...{}", self.expression)
    }
}

impl<'ast> fmt::Debug for Spread<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Spread({:?})", self.expression)
    }
}

/// A spread
#[derive(Clone, PartialEq)]
pub struct Spread<'ast> {
    pub expression: ExpressionNode<'ast>,
}

/// A range
#[derive(Clone, PartialEq)]
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

impl<'ast> fmt::Debug for Range<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Range({:?}, {:?})", self.from, self.to)
    }
}

/// An expression
#[derive(Clone, PartialEq)]
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
    IfElse(
        Box<ExpressionNode<'ast>>,
        Box<ExpressionNode<'ast>>,
        Box<ExpressionNode<'ast>>,
    ),
    FunctionCall(
        FunctionIdentifier<'ast>,
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
    Select(Box<ExpressionNode<'ast>>, Box<RangeOrExpression<'ast>>),
    Member(Box<ExpressionNode<'ast>>, Box<Identifier<'ast>>),
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
            Expression::IfElse(ref condition, ref consequent, ref alternative) => write!(
                f,
                "if {} then {} else {} fi",
                condition, consequent, alternative
            ),
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
            Expression::Or(ref lhs, ref rhs) => write!(f, "({} || {})", lhs, rhs),
            Expression::BitXor(ref lhs, ref rhs) => write!(f, "({} ^ {})", lhs, rhs),
            Expression::BitAnd(ref lhs, ref rhs) => write!(f, "({} & {})", lhs, rhs),
            Expression::BitOr(ref lhs, ref rhs) => write!(f, "({} | {})", lhs, rhs),
            Expression::LeftShift(ref lhs, ref rhs) => write!(f, "({} << {})", lhs, rhs),
            Expression::RightShift(ref lhs, ref rhs) => write!(f, "({} >> {})", lhs, rhs),
        }
    }
}

impl<'ast> fmt::Debug for Expression<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Expression::U8Constant(ref i) => write!(f, "U8({:x})", i),
            Expression::U16Constant(ref i) => write!(f, "U16({:x})", i),
            Expression::U32Constant(ref i) => write!(f, "U32({:x})", i),
            Expression::U64Constant(ref i) => write!(f, "U64({:x})", i),
            Expression::FieldConstant(ref i) => write!(f, "Field({:?})", i),
            Expression::IntConstant(ref i) => write!(f, "Int({:?})", i),
            Expression::Identifier(ref var) => write!(f, "Ide({})", var),
            Expression::Add(ref lhs, ref rhs) => write!(f, "Add({:?}, {:?})", lhs, rhs),
            Expression::Sub(ref lhs, ref rhs) => write!(f, "Sub({:?}, {:?})", lhs, rhs),
            Expression::Mult(ref lhs, ref rhs) => write!(f, "Mult({:?}, {:?})", lhs, rhs),
            Expression::Div(ref lhs, ref rhs) => write!(f, "Div({:?}, {:?})", lhs, rhs),
            Expression::Rem(ref lhs, ref rhs) => write!(f, "Rem({:?}, {:?})", lhs, rhs),
            Expression::Pow(ref lhs, ref rhs) => write!(f, "Pow({:?}, {:?})", lhs, rhs),
            Expression::Neg(ref e) => write!(f, "Neg({:?})", e),
            Expression::Pos(ref e) => write!(f, "Pos({:?})", e),
            Expression::BooleanConstant(b) => write!(f, "{}", b),
            Expression::IfElse(ref condition, ref consequent, ref alternative) => write!(
                f,
                "IfElse({:?}, {:?}, {:?})",
                condition, consequent, alternative
            ),
            Expression::FunctionCall(ref g, ref i, ref p) => {
                write!(f, "FunctionCall({:?}, {:?}, (", g, i)?;
                f.debug_list().entries(p.iter()).finish()?;
                write!(f, ")")
            }
            Expression::Lt(ref lhs, ref rhs) => write!(f, "Lt({:?}, {:?})", lhs, rhs),
            Expression::Le(ref lhs, ref rhs) => write!(f, "Le({:?}, {:?})", lhs, rhs),
            Expression::Eq(ref lhs, ref rhs) => write!(f, "Eq({:?}, {:?})", lhs, rhs),
            Expression::Ge(ref lhs, ref rhs) => write!(f, "Ge({:?}, {:?})", lhs, rhs),
            Expression::Gt(ref lhs, ref rhs) => write!(f, "Gt({:?}, {:?})", lhs, rhs),
            Expression::And(ref lhs, ref rhs) => write!(f, "And({:?}, {:?})", lhs, rhs),
            Expression::Not(ref exp) => write!(f, "Not({:?})", exp),
            Expression::InlineArray(ref exprs) => {
                write!(f, "InlineArray([")?;
                f.debug_list().entries(exprs.iter()).finish()?;
                write!(f, "]")
            }
            Expression::ArrayInitializer(ref e, ref count) => {
                write!(f, "ArrayInitializer({:?}, {:?})", e, count)
            }
            Expression::InlineStruct(ref id, ref members) => {
                write!(f, "InlineStruct({:?}, [", id)?;
                f.debug_list().entries(members.iter()).finish()?;
                write!(f, "]")
            }
            Expression::Select(ref array, ref index) => {
                write!(f, "Select({:?}, {:?})", array, index)
            }
            Expression::Member(ref struc, ref id) => write!(f, "Member({:?}, {:?})", struc, id),
            Expression::Or(ref lhs, ref rhs) => write!(f, "Or({:?}, {:?})", lhs, rhs),
            Expression::BitXor(ref lhs, ref rhs) => write!(f, "BitXor({:?}, {:?})", lhs, rhs),
            Expression::BitAnd(ref lhs, ref rhs) => write!(f, "BitAnd({:?}, {:?})", lhs, rhs),
            Expression::BitOr(ref lhs, ref rhs) => write!(f, "BitOr({:?}, {:?})", lhs, rhs),
            Expression::LeftShift(ref lhs, ref rhs) => write!(f, "LeftShift({:?}, {:?})", lhs, rhs),
            Expression::RightShift(ref lhs, ref rhs) => {
                write!(f, "RightShift({:?}, {:?})", lhs, rhs)
            }
        }
    }
}

/// A list of expressions, used in return statements
#[derive(Clone, PartialEq, Default)]
pub struct ExpressionList<'ast> {
    pub expressions: Vec<ExpressionNode<'ast>>,
}

pub type ExpressionListNode<'ast> = Node<ExpressionList<'ast>>;

impl<'ast> fmt::Display for ExpressionList<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, param) in self.expressions.iter().enumerate() {
            write!(f, "{}", param)?;
            if i < self.expressions.len() - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, "")
    }
}

impl<'ast> fmt::Debug for ExpressionList<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ExpressionList({:?})", self.expressions)
    }
}
