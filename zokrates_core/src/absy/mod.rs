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
use embed::FlatEmbed;
use std::path::PathBuf;

use crate::imports::ImportNode;
use std::fmt;
use zokrates_field::field::Field;

use std::collections::HashMap;

/// An identifier of a function or a variable
pub type Identifier<'ast> = &'ast str;

/// The identifier of a `Module`, typically a path or uri
pub type ModuleId = PathBuf;

/// A collection of `Module`s
pub type Modules<'ast, T> = HashMap<ModuleId, Module<'ast, T>>;

/// A collection of `SymbolDeclaration`. Duplicates are allowed here as they are fine syntactically.
pub type Declarations<'ast, T> = Vec<SymbolDeclarationNode<'ast, T>>;

/// A `Program` is a collection of `Module`s and an id of the main `Module`
pub struct Program<'ast, T: Field> {
    pub modules: HashMap<ModuleId, Module<'ast, T>>,
    pub main: ModuleId,
}

/// A declaration of a `FunctionSymbol`, be it from an import or a function definition
#[derive(PartialEq, Debug, Clone)]
pub struct SymbolDeclaration<'ast, T: Field> {
    pub id: Identifier<'ast>,
    pub symbol: Symbol<'ast, T>,
}

#[derive(PartialEq, Debug, Clone)]
pub enum Symbol<'ast, T: Field> {
    HereType(StructTypeNode<'ast>),
    HereFunction(FunctionNode<'ast, T>),
    There(SymbolImportNode<'ast>),
    Flat(FlatEmbed),
}

impl<'ast, T: Field> fmt::Display for SymbolDeclaration<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.symbol {
            Symbol::HereType(ref t) => write!(f, "struct {} {}", self.id, t),
            Symbol::HereFunction(ref fun) => write!(f, "def {}{}", self.id, fun),
            Symbol::There(ref import) => write!(f, "import {} as {}", import, self.id),
            Symbol::Flat(ref flat_fun) => write!(
                f,
                "def {}{}:\n\t// hidden",
                self.id,
                flat_fun.signature::<T>()
            ),
        }
    }
}

pub type SymbolDeclarationNode<'ast, T> = Node<SymbolDeclaration<'ast, T>>;

/// A module as a collection of `FunctionDeclaration`s
#[derive(Clone, PartialEq)]
pub struct Module<'ast, T: Field> {
    /// Symbols of the module
    pub symbols: Declarations<'ast, T>,
    pub imports: Vec<ImportNode<'ast>>, // we still use `imports` as they are not directly converted into `FunctionDeclaration`s after the importer is done, `imports` is empty
}

impl<'ast, T: Field> Module<'ast, T> {
    pub fn with_symbols<I: IntoIterator<Item = SymbolDeclarationNode<'ast, T>>>(i: I) -> Self {
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

pub type UnresolvedTypeNode = Node<UnresolvedType>;

/// A struct type definition
#[derive(Debug, Clone, PartialEq)]
pub struct StructType<'ast> {
    pub fields: Vec<StructFieldNode<'ast>>,
}

impl<'ast> fmt::Display for StructType<'ast> {
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

pub type StructTypeNode<'ast> = Node<StructType<'ast>>;

/// A struct type definition
#[derive(Debug, Clone, PartialEq)]
pub struct StructField<'ast> {
    pub id: Identifier<'ast>,
    pub ty: UnresolvedTypeNode,
}

impl<'ast> fmt::Display for StructField<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {},", self.id, self.ty)
    }
}

type StructFieldNode<'ast> = Node<StructField<'ast>>;

/// An import
#[derive(Debug, Clone, PartialEq)]
pub struct SymbolImport<'ast> {
    /// the id of the symbol in the target module. Note: there may be many candidates as imports statements do not specify the signature. In that case they must all be functions however.
    pub symbol_id: Identifier<'ast>,
    /// the id of the module to import from
    pub module_id: ModuleId,
}

type SymbolImportNode<'ast> = Node<SymbolImport<'ast>>;

impl<'ast> SymbolImport<'ast> {
    pub fn with_id_in_module<S: Into<Identifier<'ast>>, U: Into<ModuleId>>(
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

impl<'ast, T: Field> fmt::Display for Module<'ast, T> {
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

impl<'ast, T: Field> fmt::Debug for Module<'ast, T> {
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

/// A function defined locally
#[derive(Clone, PartialEq)]
pub struct Function<'ast, T: Field> {
    /// Arguments of the function
    pub arguments: Vec<ParameterNode<'ast>>,
    /// Vector of statements that are executed when running the function
    pub statements: Vec<StatementNode<'ast, T>>,
    /// function signature
    pub signature: UnresolvedSignature,
}

pub type FunctionNode<'ast, T> = Node<Function<'ast, T>>;

impl<'ast, T: Field> fmt::Display for Function<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
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

impl<'ast, T: Field> fmt::Debug for Function<'ast, T> {
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
pub enum Assignee<'ast, T: Field> {
    Identifier(Identifier<'ast>),
    Select(Box<AssigneeNode<'ast, T>>, Box<RangeOrExpression<'ast, T>>),
    Member(Box<AssigneeNode<'ast, T>>, Box<Identifier<'ast>>),
}

pub type AssigneeNode<'ast, T> = Node<Assignee<'ast, T>>;

impl<'ast, T: Field> fmt::Debug for Assignee<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Assignee::Identifier(ref s) => write!(f, "Identifier({:?})", s),
            Assignee::Select(ref a, ref e) => write!(f, "Select({:?}[{:?}])", a, e),
            Assignee::Member(ref s, ref m) => write!(f, "Member({:?}.{:?})", s, m),
        }
    }
}

impl<'ast, T: Field> fmt::Display for Assignee<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// A statement in a `Function`
#[derive(Clone, PartialEq)]
pub enum Statement<'ast, T: Field> {
    Return(ExpressionListNode<'ast, T>),
    Declaration(VariableNode<'ast>),
    Definition(AssigneeNode<'ast, T>, ExpressionNode<'ast, T>),
    Condition(ExpressionNode<'ast, T>, ExpressionNode<'ast, T>),
    For(
        VariableNode<'ast>,
        ExpressionNode<'ast, T>,
        ExpressionNode<'ast, T>,
        Vec<StatementNode<'ast, T>>,
    ),
    MultipleDefinition(Vec<AssigneeNode<'ast, T>>, ExpressionNode<'ast, T>),
}

pub type StatementNode<'ast, T> = Node<Statement<'ast, T>>;

impl<'ast, T: Field> fmt::Display for Statement<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Statement::Return(ref expr) => write!(f, "return {}", expr),
            Statement::Declaration(ref var) => write!(f, "{}", var),
            Statement::Definition(ref lhs, ref rhs) => write!(f, "{} = {}", lhs, rhs),
            Statement::Condition(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            Statement::For(ref var, ref start, ref stop, ref list) => {
                write!(f, "for {} in {}..{} do\n", var, start, stop)?;
                for l in list {
                    write!(f, "\t\t{}\n", l)?;
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

impl<'ast, T: Field> fmt::Debug for Statement<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Statement::Return(ref expr) => write!(f, "Return({:?})", expr),
            Statement::Declaration(ref var) => write!(f, "Declaration({:?})", var),
            Statement::Definition(ref lhs, ref rhs) => {
                write!(f, "Definition({:?}, {:?})", lhs, rhs)
            }
            Statement::Condition(ref lhs, ref rhs) => write!(f, "Condition({:?}, {:?})", lhs, rhs),
            Statement::For(ref var, ref start, ref stop, ref list) => {
                write!(f, "for {:?} in {:?}..{:?} do\n", var, start, stop)?;
                for l in list {
                    write!(f, "\t\t{:?}\n", l)?;
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
pub enum SpreadOrExpression<'ast, T: Field> {
    Spread(SpreadNode<'ast, T>),
    Expression(ExpressionNode<'ast, T>),
}

impl<'ast, T: Field> From<ExpressionNode<'ast, T>> for SpreadOrExpression<'ast, T> {
    fn from(e: ExpressionNode<'ast, T>) -> SpreadOrExpression<'ast, T> {
        SpreadOrExpression::Expression(e)
    }
}

impl<'ast, T: Field> fmt::Display for SpreadOrExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            SpreadOrExpression::Spread(ref s) => write!(f, "{}", s),
            SpreadOrExpression::Expression(ref e) => write!(f, "{}", e),
        }
    }
}

impl<'ast, T: Field> fmt::Debug for SpreadOrExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            SpreadOrExpression::Spread(ref s) => write!(f, "{:?}", s),
            SpreadOrExpression::Expression(ref e) => write!(f, "{:?}", e),
        }
    }
}

/// The index in an array selector. Can be a range or an expression.
#[derive(Clone, PartialEq)]
pub enum RangeOrExpression<'ast, T: Field> {
    Range(RangeNode<T>),
    Expression(ExpressionNode<'ast, T>),
}

impl<'ast, T: Field> fmt::Display for RangeOrExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            RangeOrExpression::Range(ref s) => write!(f, "{}", s),
            RangeOrExpression::Expression(ref e) => write!(f, "{}", e),
        }
    }
}

impl<'ast, T: Field> fmt::Debug for RangeOrExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            RangeOrExpression::Range(ref s) => write!(f, "{:?}", s),
            RangeOrExpression::Expression(ref e) => write!(f, "{:?}", e),
        }
    }
}

pub type SpreadNode<'ast, T> = Node<Spread<'ast, T>>;

impl<'ast, T: Field> fmt::Display for Spread<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "...{}", self.expression)
    }
}

impl<'ast, T: Field> fmt::Debug for Spread<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Spread({:?})", self.expression)
    }
}

/// A spread
#[derive(Clone, PartialEq)]
pub struct Spread<'ast, T: Field> {
    pub expression: ExpressionNode<'ast, T>,
}

/// A range
#[derive(Clone, PartialEq)]
pub struct Range<T: Field> {
    pub from: Option<T>,
    pub to: Option<T>,
}

pub type RangeNode<T> = Node<Range<T>>;

impl<'ast, T: Field> fmt::Display for Range<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}..{}",
            self.from
                .as_ref()
                .map(|e| e.to_string())
                .unwrap_or("".to_string()),
            self.to
                .as_ref()
                .map(|e| e.to_string())
                .unwrap_or("".to_string())
        )
    }
}

impl<'ast, T: Field> fmt::Debug for Range<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Range({:?}, {:?})", self.from, self.to)
    }
}

/// An expression
#[derive(Clone, PartialEq)]
pub enum Expression<'ast, T: Field> {
    FieldConstant(T),
    BooleanConstant(bool),
    Identifier(Identifier<'ast>),
    Add(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
    Sub(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
    Mult(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
    Div(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
    Pow(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
    IfElse(
        Box<ExpressionNode<'ast, T>>,
        Box<ExpressionNode<'ast, T>>,
        Box<ExpressionNode<'ast, T>>,
    ),
    FunctionCall(FunctionIdentifier<'ast>, Vec<ExpressionNode<'ast, T>>),
    Lt(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
    Le(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
    Eq(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
    Ge(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
    Gt(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
    And(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
    Not(Box<ExpressionNode<'ast, T>>),
    InlineArray(Vec<SpreadOrExpression<'ast, T>>),
    InlineStruct(UserTypeId, Vec<(Identifier<'ast>, ExpressionNode<'ast, T>)>),
    Select(
        Box<ExpressionNode<'ast, T>>,
        Box<RangeOrExpression<'ast, T>>,
    ),
    Member(Box<ExpressionNode<'ast, T>>, Box<Identifier<'ast>>),
    Or(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
}

pub type ExpressionNode<'ast, T> = Node<Expression<'ast, T>>;

impl<'ast, T: Field> fmt::Display for Expression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Expression::FieldConstant(ref i) => write!(f, "{}", i),
            Expression::Identifier(ref var) => write!(f, "{}", var),
            Expression::Add(ref lhs, ref rhs) => write!(f, "({} + {})", lhs, rhs),
            Expression::Sub(ref lhs, ref rhs) => write!(f, "({} - {})", lhs, rhs),
            Expression::Mult(ref lhs, ref rhs) => write!(f, "({} * {})", lhs, rhs),
            Expression::Div(ref lhs, ref rhs) => write!(f, "({} / {})", lhs, rhs),
            Expression::Pow(ref lhs, ref rhs) => write!(f, "{}**{}", lhs, rhs),
            Expression::BooleanConstant(b) => write!(f, "{}", b),
            Expression::IfElse(ref condition, ref consequent, ref alternative) => write!(
                f,
                "if {} then {} else {} fi",
                condition, consequent, alternative
            ),
            Expression::FunctionCall(ref i, ref p) => {
                write!(f, "{}(", i,)?;
                for (i, param) in p.iter().enumerate() {
                    write!(f, "{}", param)?;
                    if i < p.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            Expression::Lt(ref lhs, ref rhs) => write!(f, "{} < {}", lhs, rhs),
            Expression::Le(ref lhs, ref rhs) => write!(f, "{} <= {}", lhs, rhs),
            Expression::Eq(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            Expression::Ge(ref lhs, ref rhs) => write!(f, "{} >= {}", lhs, rhs),
            Expression::Gt(ref lhs, ref rhs) => write!(f, "{} > {}", lhs, rhs),
            Expression::And(ref lhs, ref rhs) => write!(f, "{} && {}", lhs, rhs),
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
            Expression::Or(ref lhs, ref rhs) => write!(f, "{} || {}", lhs, rhs),
        }
    }
}

impl<'ast, T: Field> fmt::Debug for Expression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Expression::FieldConstant(ref i) => write!(f, "Num({})", i),
            Expression::Identifier(ref var) => write!(f, "Ide({})", var),
            Expression::Add(ref lhs, ref rhs) => write!(f, "Add({:?}, {:?})", lhs, rhs),
            Expression::Sub(ref lhs, ref rhs) => write!(f, "Sub({:?}, {:?})", lhs, rhs),
            Expression::Mult(ref lhs, ref rhs) => write!(f, "Mult({:?}, {:?})", lhs, rhs),
            Expression::Div(ref lhs, ref rhs) => write!(f, "Div({:?}, {:?})", lhs, rhs),
            Expression::Pow(ref lhs, ref rhs) => write!(f, "Pow({:?}, {:?})", lhs, rhs),
            Expression::BooleanConstant(b) => write!(f, "{}", b),
            Expression::IfElse(ref condition, ref consequent, ref alternative) => write!(
                f,
                "IfElse({:?}, {:?}, {:?})",
                condition, consequent, alternative
            ),
            Expression::FunctionCall(ref i, ref p) => {
                write!(f, "FunctionCall({:?}, (", i)?;
                f.debug_list().entries(p.iter()).finish()?;
                write!(f, ")")
            }
            Expression::Lt(ref lhs, ref rhs) => write!(f, "{} < {}", lhs, rhs),
            Expression::Le(ref lhs, ref rhs) => write!(f, "{} <= {}", lhs, rhs),
            Expression::Eq(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            Expression::Ge(ref lhs, ref rhs) => write!(f, "{} >= {}", lhs, rhs),
            Expression::Gt(ref lhs, ref rhs) => write!(f, "{} > {}", lhs, rhs),
            Expression::And(ref lhs, ref rhs) => write!(f, "{} && {}", lhs, rhs),
            Expression::Not(ref exp) => write!(f, "!{}", exp),
            Expression::InlineArray(ref exprs) => {
                write!(f, "InlineArray([")?;
                f.debug_list().entries(exprs.iter()).finish()?;
                write!(f, "]")
            }
            Expression::InlineStruct(ref id, ref members) => {
                write!(f, "InlineStruct({:?}, [", id)?;
                f.debug_list().entries(members.iter()).finish()?;
                write!(f, "]")
            }
            Expression::Select(ref array, ref index) => {
                write!(f, "Select({:?}, {:?})", array, index)
            }
            Expression::Member(ref struc, ref id) => write!(f, "{}.{}", struc, id),
            Expression::Or(ref lhs, ref rhs) => write!(f, "{} || {}", lhs, rhs),
        }
    }
}

/// A list of expressions, used in return statements
#[derive(Clone, PartialEq)]
pub struct ExpressionList<'ast, T: Field> {
    pub expressions: Vec<ExpressionNode<'ast, T>>,
}

pub type ExpressionListNode<'ast, T> = Node<ExpressionList<'ast, T>>;

impl<'ast, T: Field> ExpressionList<'ast, T> {
    pub fn new() -> ExpressionList<'ast, T> {
        ExpressionList {
            expressions: vec![],
        }
    }
}

impl<'ast, T: Field> fmt::Display for ExpressionList<'ast, T> {
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

impl<'ast, T: Field> fmt::Debug for ExpressionList<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ExpressionList({:?})", self.expressions)
    }
}
