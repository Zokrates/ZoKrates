//! Module containing structs and enums to represent a program.
//!
//! @file absy.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

pub mod abi;
pub mod folder;
mod parameter;
pub mod types;
mod variable;

pub use crate::typed_absy::parameter::Parameter;
pub use crate::typed_absy::types::{Signature, Type};
pub use crate::typed_absy::variable::Variable;
use std::path::PathBuf;

use crate::typed_absy::types::{FunctionKey, MemberId};
use embed::FlatEmbed;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt;
use zokrates_field::field::Field;

pub use self::folder::Folder;
use typed_absy::abi::{Abi, AbiInput};
use typed_absy::types::StructMember;

/// A identifier for a variable
#[derive(Debug, PartialEq, Clone, Hash, Eq)]
pub struct Identifier<'ast> {
    /// the id of the variable
    pub id: &'ast str,
    /// the version of the variable, used after SSA transformation
    pub version: usize,
    /// the call stack of the variable, used when inlining
    pub stack: Vec<(TypedModuleId, FunctionKey<'ast>, usize)>,
}

/// An identifier for a `TypedModule`. Typically a path or uri.
pub type TypedModuleId = PathBuf;

/// A collection of `TypedModule`s
pub type TypedModules<'ast, T> = HashMap<TypedModuleId, TypedModule<'ast, T>>;

/// A collection of `TypedFunctionSymbol`s
/// # Remarks
/// * It is the role of the semantic checker to make sure there are no duplicates for a given `FunctionKey`
///   in a given `TypedModule`, hence the use of a HashMap
pub type TypedFunctionSymbols<'ast, T> = HashMap<FunctionKey<'ast>, TypedFunctionSymbol<'ast, T>>;

/// A typed program as a collection of modules, one of them being the main
#[derive(PartialEq, Debug)]
pub struct TypedProgram<'ast, T: Field> {
    pub modules: TypedModules<'ast, T>,
    pub main: TypedModuleId,
}

impl<'ast, T: Field> TypedProgram<'ast, T> {
    pub fn abi(&self) -> Abi {
        let main = self.modules[&self.main]
            .functions
            .iter()
            .find(|(id, _)| id.id == "main")
            .unwrap()
            .1;
        let main = match main {
            TypedFunctionSymbol::Here(main) => main,
            _ => unreachable!(),
        };

        Abi {
            inputs: main
                .arguments
                .iter()
                .map(|p| AbiInput {
                    public: !p.private,
                    name: p.id.id.to_string(),
                    ty: p.id._type.clone(),
                })
                .collect(),
            outputs: main.signature.outputs.clone(),
        }
    }
}

impl<'ast, T: Field> fmt::Display for TypedProgram<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (module_id, module) in &self.modules {
            writeln!(
                f,
                "| {}: |{}",
                module_id.display(),
                if *module_id == self.main {
                    "<---- main"
                } else {
                    ""
                }
            )?;
            writeln!(f, "{}", "-".repeat(100))?;
            writeln!(f, "{}", module)?;
            writeln!(f, "{}", "-".repeat(100))?;
            writeln!(f, "")?;
        }
        write!(f, "")
    }
}

/// A typed program as a collection of functions. Types have been resolved during semantic checking.
#[derive(PartialEq, Clone)]
pub struct TypedModule<'ast, T: Field> {
    /// Functions of the program
    pub functions: TypedFunctionSymbols<'ast, T>,
}

impl<'ast> fmt::Display for Identifier<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.stack.len() == 0 && self.version == 0 {
            write!(f, "{}", self.id)
        } else {
            write!(
                f,
                "{}_{}_{}",
                self.stack
                    .iter()
                    .map(|(name, sig, count)| format!(
                        "{}_{}_{}",
                        name.display(),
                        sig.to_slug(),
                        count
                    ))
                    .collect::<Vec<_>>()
                    .join("_"),
                self.id,
                self.version
            )
        }
    }
}

impl<'ast> From<&'ast str> for Identifier<'ast> {
    fn from(id: &'ast str) -> Identifier<'ast> {
        Identifier {
            id,
            version: 0,
            stack: vec![],
        }
    }
}

#[cfg(test)]
impl<'ast> Identifier<'ast> {
    pub fn version(mut self, version: usize) -> Self {
        self.version = version;
        self
    }

    pub fn stack(mut self, stack: Vec<(TypedModuleId, FunctionKey<'ast>, usize)>) -> Self {
        self.stack = stack;
        self
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypedFunctionSymbol<'ast, T: Field> {
    Here(TypedFunction<'ast, T>),
    There(FunctionKey<'ast>, TypedModuleId),
    Flat(FlatEmbed),
}

impl<'ast, T: Field> TypedFunctionSymbol<'ast, T> {
    pub fn signature<'a>(&'a self, modules: &'a TypedModules<T>) -> Signature {
        match self {
            TypedFunctionSymbol::Here(f) => f.signature.clone(),
            TypedFunctionSymbol::There(key, module_id) => modules
                .get(module_id)
                .unwrap()
                .functions
                .get(key)
                .unwrap()
                .signature(&modules)
                .clone(),
            TypedFunctionSymbol::Flat(flat_fun) => flat_fun.signature::<T>(),
        }
    }
}

impl<'ast, T: Field> fmt::Display for TypedModule<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let res = self
            .functions
            .iter()
            .map(|(key, symbol)| match symbol {
                TypedFunctionSymbol::Here(ref function) => format!("def {}{}", key.id, function),
                TypedFunctionSymbol::There(ref fun_key, ref module_id) => format!(
                    "import {} from \"{}\" as {} // with signature {}",
                    fun_key.id,
                    module_id.display(),
                    key.id,
                    key.signature
                ),
                TypedFunctionSymbol::Flat(ref flat_fun) => {
                    format!("def {}{}:\n\t// hidden", key.id, flat_fun.signature::<T>())
                }
            })
            .collect::<Vec<_>>();
        write!(f, "{}", res.join("\n"))
    }
}

impl<'ast, T: Field> fmt::Debug for TypedModule<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "module(\n\tfunctions:\n\t\t{}\n)",
            self.functions
                .iter()
                .map(|x| format!("{:?}", x))
                .collect::<Vec<_>>()
                .join("\n\t\t")
        )
    }
}

/// A typed function
#[derive(Clone, PartialEq)]
pub struct TypedFunction<'ast, T: Field> {
    /// Arguments of the function
    pub arguments: Vec<Parameter<'ast>>,
    /// Vector of statements that are executed when running the function
    pub statements: Vec<TypedStatement<'ast, T>>,
    /// function signature
    pub signature: Signature,
}

impl<'ast, T: Field> fmt::Display for TypedFunction<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "({}) -> ({}):",
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
                .join(", "),
        )?;

        writeln!(f, "")?;

        for s in &self.statements {
            s.fmt_indented(f, 1)?;
            writeln!(f, "")?;
        }

        Ok(())
    }
}

impl<'ast, T: Field> fmt::Debug for TypedFunction<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "TypedFunction(arguments: {:?}, ...):\n{}",
            self.arguments,
            self.statements
                .iter()
                .map(|x| format!("\t{:?}", x))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

/// Something we can assign to.
#[derive(Clone, PartialEq, Hash, Eq)]
pub enum TypedAssignee<'ast, T: Field> {
    Identifier(Variable<'ast>),
    Select(
        Box<TypedAssignee<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    Member(Box<TypedAssignee<'ast, T>>, MemberId),
}

impl<'ast, T: Field> Typed for TypedAssignee<'ast, T> {
    fn get_type(&self) -> Type {
        match *self {
            TypedAssignee::Identifier(ref v) => v.get_type(),
            TypedAssignee::Select(ref a, _) => {
                let a_type = a.get_type();
                match a_type {
                    Type::Array(t) => *t.ty,
                    _ => unreachable!("an array element should only be defined over arrays"),
                }
            }
            TypedAssignee::Member(ref s, ref m) => {
                let s_type = s.get_type();
                match s_type {
                    Type::Struct(members) => *members
                        .iter()
                        .find(|member| member.id == *m)
                        .unwrap()
                        .ty
                        .clone(),
                    _ => unreachable!("a struct access should only be defined over structs"),
                }
            }
        }
    }
}

impl<'ast, T: Field> fmt::Debug for TypedAssignee<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedAssignee::Identifier(ref s) => write!(f, "{}", s.id),
            TypedAssignee::Select(ref a, ref e) => write!(f, "{}[{}]", a, e),
            TypedAssignee::Member(ref s, ref m) => write!(f, "{}.{}", s, m),
        }
    }
}

impl<'ast, T: Field> fmt::Display for TypedAssignee<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// A statement in a `TypedFunction`
#[derive(Clone, PartialEq, Hash, Eq)]
pub enum TypedStatement<'ast, T: Field> {
    Return(Vec<TypedExpression<'ast, T>>),
    Definition(TypedAssignee<'ast, T>, TypedExpression<'ast, T>),
    Declaration(Variable<'ast>),
    Condition(TypedExpression<'ast, T>, TypedExpression<'ast, T>),
    For(
        Variable<'ast>,
        FieldElementExpression<'ast, T>,
        FieldElementExpression<'ast, T>,
        Vec<TypedStatement<'ast, T>>,
    ),
    MultipleDefinition(Vec<Variable<'ast>>, TypedExpressionList<'ast, T>),
}

impl<'ast, T: Field> fmt::Debug for TypedStatement<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedStatement::Return(ref exprs) => {
                write!(f, "Return(")?;
                for (i, expr) in exprs.iter().enumerate() {
                    write!(f, "{}", expr)?;
                    if i < exprs.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            TypedStatement::Declaration(ref var) => write!(f, "Declaration({:?})", var),
            TypedStatement::Definition(ref lhs, ref rhs) => {
                write!(f, "Definition({:?}, {:?})", lhs, rhs)
            }
            TypedStatement::Condition(ref lhs, ref rhs) => {
                write!(f, "Condition({:?}, {:?})", lhs, rhs)
            }
            TypedStatement::For(ref var, ref start, ref stop, ref list) => {
                write!(f, "for {:?} in {:?}..{:?} do\n", var, start, stop)?;
                for l in list {
                    write!(f, "\t\t{:?}\n", l)?;
                }
                write!(f, "\tendfor")
            }
            TypedStatement::MultipleDefinition(ref lhs, ref rhs) => {
                write!(f, "MultipleDefinition({:?}, {:?})", lhs, rhs)
            }
        }
    }
}

impl<'ast, T: Field> TypedStatement<'ast, T> {
    fn fmt_indented(&self, f: &mut fmt::Formatter, depth: usize) -> fmt::Result {
        match self {
            TypedStatement::For(variable, from, to, statements) => {
                write!(f, "{}", "\t".repeat(depth))?;
                writeln!(f, "for {} in {}..{} do", variable, from, to)?;
                for s in statements {
                    s.fmt_indented(f, depth + 1)?;
                    writeln!(f, "")?;
                }
                writeln!(f, "{}endfor", "\t".repeat(depth))
            }
            s => write!(f, "{}{}", "\t".repeat(depth), s),
        }
    }
}

impl<'ast, T: Field> fmt::Display for TypedStatement<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedStatement::Return(ref exprs) => {
                write!(f, "return ")?;
                for (i, expr) in exprs.iter().enumerate() {
                    write!(f, "{}", expr)?;
                    if i < exprs.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "")
            }
            TypedStatement::Declaration(ref var) => write!(f, "{}", var),
            TypedStatement::Definition(ref lhs, ref rhs) => write!(f, "{} = {}", lhs, rhs),
            TypedStatement::Condition(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            TypedStatement::For(ref var, ref start, ref stop, ref list) => {
                write!(f, "for {} in {}..{} do\n", var, start, stop)?;
                for l in list {
                    write!(f, "\t\t{}\n", l)?;
                }
                write!(f, "\tendfor")
            }
            TypedStatement::MultipleDefinition(ref ids, ref rhs) => {
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

pub trait Typed {
    fn get_type(&self) -> Type;
}

/// A typed expression
#[derive(Clone, PartialEq, Hash, Eq)]
pub enum TypedExpression<'ast, T: Field> {
    Boolean(BooleanExpression<'ast, T>),
    FieldElement(FieldElementExpression<'ast, T>),
    Array(ArrayExpression<'ast, T>),
    Struct(StructExpression<'ast, T>),
}

impl<'ast, T: Field> From<BooleanExpression<'ast, T>> for TypedExpression<'ast, T> {
    fn from(e: BooleanExpression<'ast, T>) -> TypedExpression<T> {
        TypedExpression::Boolean(e)
    }
}

impl<'ast, T: Field> From<FieldElementExpression<'ast, T>> for TypedExpression<'ast, T> {
    fn from(e: FieldElementExpression<'ast, T>) -> TypedExpression<T> {
        TypedExpression::FieldElement(e)
    }
}

impl<'ast, T: Field> From<ArrayExpression<'ast, T>> for TypedExpression<'ast, T> {
    fn from(e: ArrayExpression<'ast, T>) -> TypedExpression<T> {
        TypedExpression::Array(e)
    }
}

impl<'ast, T: Field> From<StructExpression<'ast, T>> for TypedExpression<'ast, T> {
    fn from(e: StructExpression<'ast, T>) -> TypedExpression<T> {
        TypedExpression::Struct(e)
    }
}

impl<'ast, T: Field> fmt::Display for TypedExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedExpression::Boolean(ref e) => write!(f, "{}", e),
            TypedExpression::FieldElement(ref e) => write!(f, "{}", e),
            TypedExpression::Array(ref e) => write!(f, "{}", e),
            TypedExpression::Struct(ref s) => write!(f, "{}", s),
        }
    }
}

impl<'ast, T: Field> fmt::Debug for TypedExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedExpression::Boolean(ref e) => write!(f, "{:?}", e),
            TypedExpression::FieldElement(ref e) => write!(f, "{:?}", e),
            TypedExpression::Array(ref e) => write!(f, "{:?}", e),
            TypedExpression::Struct(ref s) => write!(f, "{}", s),
        }
    }
}

impl<'ast, T: Field> fmt::Display for ArrayExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.inner)
    }
}

impl<'ast, T: Field> fmt::Debug for ArrayExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.inner)
    }
}

impl<'ast, T: Field> fmt::Display for StructExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.inner {
            StructExpressionInner::Identifier(ref var) => write!(f, "{}", var),
            StructExpressionInner::Value(ref values) => write!(
                f,
                "{{{}}}",
                self.ty
                    .iter()
                    .map(|member| member.id.clone())
                    .zip(values.iter())
                    .map(|(id, o)| format!("{}: {}", id, o.to_string()))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            StructExpressionInner::FunctionCall(ref key, ref p) => {
                write!(f, "{}(", key.id,)?;
                for (i, param) in p.iter().enumerate() {
                    write!(f, "{}", param)?;
                    if i < p.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            StructExpressionInner::IfElse(ref condition, ref consequent, ref alternative) => {
                write!(
                    f,
                    "if {} then {} else {} fi",
                    condition, consequent, alternative
                )
            }
            StructExpressionInner::Member(ref struc, ref id) => write!(f, "{}.{}", struc, id),
            StructExpressionInner::Select(ref id, ref index) => write!(f, "{}[{}]", id, index),
        }
    }
}

impl<'ast, T: Field> fmt::Debug for StructExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.inner)
    }
}

impl<'ast, T: Field> Typed for TypedExpression<'ast, T> {
    fn get_type(&self) -> Type {
        match *self {
            TypedExpression::Boolean(ref e) => e.get_type(),
            TypedExpression::FieldElement(ref e) => e.get_type(),
            TypedExpression::Array(ref e) => e.get_type(),
            TypedExpression::Struct(ref s) => s.get_type(),
        }
    }
}

impl<'ast, T: Field> Typed for ArrayExpression<'ast, T> {
    fn get_type(&self) -> Type {
        Type::array(self.ty.clone(), self.size)
    }
}

impl<'ast, T: Field> Typed for StructExpression<'ast, T> {
    fn get_type(&self) -> Type {
        Type::Struct(self.ty.clone())
    }
}

impl<'ast, T: Field> Typed for FieldElementExpression<'ast, T> {
    fn get_type(&self) -> Type {
        Type::FieldElement
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
pub enum TypedExpressionList<'ast, T: Field> {
    FunctionCall(FunctionKey<'ast>, Vec<TypedExpression<'ast, T>>, Vec<Type>),
}

impl<'ast, T: Field> MultiTyped for TypedExpressionList<'ast, T> {
    fn get_types(&self) -> &Vec<Type> {
        match *self {
            TypedExpressionList::FunctionCall(_, _, ref types) => types,
        }
    }
}

/// An expression of type `field`
#[derive(Clone, PartialEq, Hash, Eq)]
pub enum FieldElementExpression<'ast, T: Field> {
    Number(T),
    Identifier(Identifier<'ast>),
    Add(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    Sub(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    Mult(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    Div(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    Pow(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    IfElse(
        Box<BooleanExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    FunctionCall(FunctionKey<'ast>, Vec<TypedExpression<'ast, T>>),
    Member(Box<StructExpression<'ast, T>>, MemberId),
    Select(
        Box<ArrayExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
}

/// An expression of type `bool`
#[derive(Clone, PartialEq, Hash, Eq)]
pub enum BooleanExpression<'ast, T: Field> {
    Identifier(Identifier<'ast>),
    Value(bool),
    Lt(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    Le(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    FieldEq(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    BoolEq(
        Box<BooleanExpression<'ast, T>>,
        Box<BooleanExpression<'ast, T>>,
    ),
    Ge(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    Gt(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    Or(
        Box<BooleanExpression<'ast, T>>,
        Box<BooleanExpression<'ast, T>>,
    ),
    And(
        Box<BooleanExpression<'ast, T>>,
        Box<BooleanExpression<'ast, T>>,
    ),
    Not(Box<BooleanExpression<'ast, T>>),
    IfElse(
        Box<BooleanExpression<'ast, T>>,
        Box<BooleanExpression<'ast, T>>,
        Box<BooleanExpression<'ast, T>>,
    ),
    Member(Box<StructExpression<'ast, T>>, MemberId),
    FunctionCall(FunctionKey<'ast>, Vec<TypedExpression<'ast, T>>),
    Select(
        Box<ArrayExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
}

/// An expression of type `array`
/// # Remarks
/// * Contrary to basic types which are represented as enums, we wrap an enum `ArrayExpressionInner` in a struct in order to keep track of the type (content and size)
/// of the array. Only using an enum would require generics, which would propagate up to TypedExpression which we want to keep simple, hence this "runtime"
/// type checking
#[derive(Clone, PartialEq, Hash, Eq)]
pub struct ArrayExpression<'ast, T: Field> {
    size: usize,
    ty: Type,
    inner: ArrayExpressionInner<'ast, T>,
}

#[derive(Clone, PartialEq, Hash, Eq)]
pub enum ArrayExpressionInner<'ast, T: Field> {
    Identifier(Identifier<'ast>),
    Value(Vec<TypedExpression<'ast, T>>),
    FunctionCall(FunctionKey<'ast>, Vec<TypedExpression<'ast, T>>),
    IfElse(
        Box<BooleanExpression<'ast, T>>,
        Box<ArrayExpression<'ast, T>>,
        Box<ArrayExpression<'ast, T>>,
    ),
    Member(Box<StructExpression<'ast, T>>, MemberId),
    Select(
        Box<ArrayExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
}

impl<'ast, T: Field> ArrayExpressionInner<'ast, T> {
    pub fn annotate(self, ty: Type, size: usize) -> ArrayExpression<'ast, T> {
        ArrayExpression {
            size,
            ty,
            inner: self,
        }
    }
}

impl<'ast, T: Field> ArrayExpression<'ast, T> {
    pub fn inner_type(&self) -> &Type {
        &self.ty
    }

    pub fn size(&self) -> usize {
        self.size
    }

    pub fn as_inner(&self) -> &ArrayExpressionInner<'ast, T> {
        &self.inner
    }

    pub fn into_inner(self) -> ArrayExpressionInner<'ast, T> {
        self.inner
    }
}

#[derive(Clone, PartialEq, Hash, Eq)]
pub struct StructExpression<'ast, T: Field> {
    ty: Vec<StructMember>,
    inner: StructExpressionInner<'ast, T>,
}

impl<'ast, T: Field> StructExpression<'ast, T> {
    pub fn ty(&self) -> &Vec<StructMember> {
        &self.ty
    }

    pub fn as_inner(&self) -> &StructExpressionInner<'ast, T> {
        &self.inner
    }

    pub fn into_inner(self) -> StructExpressionInner<'ast, T> {
        self.inner
    }
}

#[derive(Clone, PartialEq, Hash, Eq)]
pub enum StructExpressionInner<'ast, T: Field> {
    Identifier(Identifier<'ast>),
    Value(Vec<TypedExpression<'ast, T>>),
    FunctionCall(FunctionKey<'ast>, Vec<TypedExpression<'ast, T>>),
    IfElse(
        Box<BooleanExpression<'ast, T>>,
        Box<StructExpression<'ast, T>>,
        Box<StructExpression<'ast, T>>,
    ),
    Member(Box<StructExpression<'ast, T>>, MemberId),
    Select(
        Box<ArrayExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
}

impl<'ast, T: Field> StructExpressionInner<'ast, T> {
    pub fn annotate(self, ty: Vec<StructMember>) -> StructExpression<'ast, T> {
        StructExpression { ty, inner: self }
    }
}

// Downcasts
// Due to the fact that we keep TypedExpression simple, we end up with ArrayExpressionInner::Value whose elements are any TypedExpression, but we enforce by
// construction that these elements are of the type declared in the corresponding ArrayExpression. As we know this by construction, we can downcast the TypedExpression to the correct type
// ArrayExpression { type: Type::FieldElement, size: 42, inner: [TypedExpression::FieldElement(FieldElementExpression), ...]} <- the fact that inner only contains field elements is not enforced by the rust type system
impl<'ast, T: Field> TryFrom<TypedExpression<'ast, T>> for FieldElementExpression<'ast, T> {
    type Error = ();

    fn try_from(
        te: TypedExpression<'ast, T>,
    ) -> Result<FieldElementExpression<'ast, T>, Self::Error> {
        match te {
            TypedExpression::FieldElement(e) => Ok(e),
            _ => Err(()),
        }
    }
}

impl<'ast, T: Field> TryFrom<TypedExpression<'ast, T>> for BooleanExpression<'ast, T> {
    type Error = ();

    fn try_from(te: TypedExpression<'ast, T>) -> Result<BooleanExpression<'ast, T>, Self::Error> {
        match te {
            TypedExpression::Boolean(e) => Ok(e),
            _ => Err(()),
        }
    }
}

impl<'ast, T: Field> TryFrom<TypedExpression<'ast, T>> for ArrayExpression<'ast, T> {
    type Error = ();

    fn try_from(te: TypedExpression<'ast, T>) -> Result<ArrayExpression<'ast, T>, Self::Error> {
        match te {
            TypedExpression::Array(e) => Ok(e),
            _ => Err(()),
        }
    }
}

impl<'ast, T: Field> TryFrom<TypedExpression<'ast, T>> for StructExpression<'ast, T> {
    type Error = ();

    fn try_from(te: TypedExpression<'ast, T>) -> Result<StructExpression<'ast, T>, Self::Error> {
        match te {
            TypedExpression::Struct(e) => Ok(e),
            _ => Err(()),
        }
    }
}

impl<'ast, T: Field> fmt::Display for FieldElementExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FieldElementExpression::Number(ref i) => write!(f, "{}", i),
            FieldElementExpression::Identifier(ref var) => write!(f, "{}", var),
            FieldElementExpression::Add(ref lhs, ref rhs) => write!(f, "({} + {})", lhs, rhs),
            FieldElementExpression::Sub(ref lhs, ref rhs) => write!(f, "({} - {})", lhs, rhs),
            FieldElementExpression::Mult(ref lhs, ref rhs) => write!(f, "({} * {})", lhs, rhs),
            FieldElementExpression::Div(ref lhs, ref rhs) => write!(f, "({} / {})", lhs, rhs),
            FieldElementExpression::Pow(ref lhs, ref rhs) => write!(f, "{}**{}", lhs, rhs),
            FieldElementExpression::IfElse(ref condition, ref consequent, ref alternative) => {
                write!(
                    f,
                    "if {} then {} else {} fi",
                    condition, consequent, alternative
                )
            }
            FieldElementExpression::FunctionCall(ref k, ref p) => {
                write!(f, "{}(", k.id,)?;
                for (i, param) in p.iter().enumerate() {
                    write!(f, "{}", param)?;
                    if i < p.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            FieldElementExpression::Member(ref struc, ref id) => write!(f, "{}.{}", struc, id),
            FieldElementExpression::Select(ref id, ref index) => write!(f, "{}[{}]", id, index),
        }
    }
}

impl<'ast, T: Field> fmt::Display for BooleanExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            BooleanExpression::Identifier(ref var) => write!(f, "{}", var),
            BooleanExpression::Lt(ref lhs, ref rhs) => write!(f, "{} < {}", lhs, rhs),
            BooleanExpression::Le(ref lhs, ref rhs) => write!(f, "{} <= {}", lhs, rhs),
            BooleanExpression::FieldEq(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            BooleanExpression::BoolEq(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            BooleanExpression::Ge(ref lhs, ref rhs) => write!(f, "{} >= {}", lhs, rhs),
            BooleanExpression::Gt(ref lhs, ref rhs) => write!(f, "{} > {}", lhs, rhs),
            BooleanExpression::Or(ref lhs, ref rhs) => write!(f, "{} || {}", lhs, rhs),
            BooleanExpression::And(ref lhs, ref rhs) => write!(f, "{} && {}", lhs, rhs),
            BooleanExpression::Not(ref exp) => write!(f, "!{}", exp),
            BooleanExpression::Value(b) => write!(f, "{}", b),
            BooleanExpression::FunctionCall(ref k, ref p) => {
                write!(f, "{}(", k.id,)?;
                for (i, param) in p.iter().enumerate() {
                    write!(f, "{}", param)?;
                    if i < p.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            BooleanExpression::IfElse(ref condition, ref consequent, ref alternative) => write!(
                f,
                "if {} then {} else {} fi",
                condition, consequent, alternative
            ),
            BooleanExpression::Member(ref struc, ref id) => write!(f, "{}.{}", struc, id),
            BooleanExpression::Select(ref id, ref index) => write!(f, "{}[{}]", id, index),
        }
    }
}

impl<'ast, T: Field> fmt::Display for ArrayExpressionInner<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ArrayExpressionInner::Identifier(ref var) => write!(f, "{}", var),
            ArrayExpressionInner::Value(ref values) => write!(
                f,
                "[{}]",
                values
                    .iter()
                    .map(|o| o.to_string())
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            ArrayExpressionInner::FunctionCall(ref key, ref p) => {
                write!(f, "{}(", key.id,)?;
                for (i, param) in p.iter().enumerate() {
                    write!(f, "{}", param)?;
                    if i < p.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            ArrayExpressionInner::IfElse(ref condition, ref consequent, ref alternative) => write!(
                f,
                "if {} then {} else {} fi",
                condition, consequent, alternative
            ),
            ArrayExpressionInner::Member(ref s, ref id) => write!(f, "{}.{}", s, id),
            ArrayExpressionInner::Select(ref id, ref index) => write!(f, "{}[{}]", id, index),
        }
    }
}

impl<'ast, T: Field> fmt::Debug for BooleanExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl<'ast, T: Field> fmt::Debug for FieldElementExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FieldElementExpression::Number(ref i) => write!(f, "Num({})", i),
            FieldElementExpression::Identifier(ref var) => write!(f, "Ide({})", var),
            FieldElementExpression::Add(ref lhs, ref rhs) => write!(f, "Add({:?}, {:?})", lhs, rhs),
            FieldElementExpression::Sub(ref lhs, ref rhs) => write!(f, "Sub({:?}, {:?})", lhs, rhs),
            FieldElementExpression::Mult(ref lhs, ref rhs) => {
                write!(f, "Mult({:?}, {:?})", lhs, rhs)
            }
            FieldElementExpression::Div(ref lhs, ref rhs) => write!(f, "Div({:?}, {:?})", lhs, rhs),
            FieldElementExpression::Pow(ref lhs, ref rhs) => write!(f, "Pow({:?}, {:?})", lhs, rhs),
            FieldElementExpression::IfElse(ref condition, ref consequent, ref alternative) => {
                write!(
                    f,
                    "IfElse({:?}, {:?}, {:?})",
                    condition, consequent, alternative
                )
            }
            FieldElementExpression::FunctionCall(ref i, ref p) => {
                write!(f, "FunctionCall({:?}, (", i)?;
                f.debug_list().entries(p.iter()).finish()?;
                write!(f, ")")
            }
            FieldElementExpression::Member(ref struc, ref id) => {
                write!(f, "Member({:?}, {:?})", struc, id)
            }
            FieldElementExpression::Select(ref id, ref index) => {
                write!(f, "Select({:?}, {:?})", id, index)
            }
        }
    }
}

impl<'ast, T: Field> fmt::Debug for ArrayExpressionInner<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ArrayExpressionInner::Identifier(ref var) => write!(f, "Identifier({:?})", var),
            ArrayExpressionInner::Value(ref values) => write!(f, "Value({:?})", values),
            ArrayExpressionInner::FunctionCall(ref i, ref p) => {
                write!(f, "FunctionCall({:?}, (", i)?;
                f.debug_list().entries(p.iter()).finish()?;
                write!(f, ")")
            }
            ArrayExpressionInner::IfElse(ref condition, ref consequent, ref alternative) => write!(
                f,
                "IfElse({:?}, {:?}, {:?})",
                condition, consequent, alternative
            ),
            ArrayExpressionInner::Member(ref struc, ref id) => {
                write!(f, "Member({:?}, {:?})", struc, id)
            }
            ArrayExpressionInner::Select(ref id, ref index) => {
                write!(f, "Select({:?}, {:?})", id, index)
            }
        }
    }
}

impl<'ast, T: Field> fmt::Debug for StructExpressionInner<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            StructExpressionInner::Identifier(ref var) => write!(f, "{:?}", var),
            StructExpressionInner::Value(ref values) => write!(f, "{:?}", values),
            StructExpressionInner::FunctionCall(ref i, ref p) => {
                write!(f, "FunctionCall({:?}, (", i)?;
                f.debug_list().entries(p.iter()).finish()?;
                write!(f, ")")
            }
            StructExpressionInner::IfElse(ref condition, ref consequent, ref alternative) => {
                write!(
                    f,
                    "IfElse({:?}, {:?}, {:?})",
                    condition, consequent, alternative
                )
            }
            StructExpressionInner::Member(ref struc, ref id) => {
                write!(f, "Member({:?}, {:?})", struc, id)
            }
            StructExpressionInner::Select(ref id, ref index) => {
                write!(f, "Select({:?}, {:?})", id, index)
            }
        }
    }
}

impl<'ast, T: Field> fmt::Display for TypedExpressionList<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedExpressionList::FunctionCall(ref key, ref p, _) => {
                write!(f, "{}(", key.id,)?;
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

impl<'ast, T: Field> fmt::Debug for TypedExpressionList<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedExpressionList::FunctionCall(ref i, ref p, _) => {
                write!(f, "FunctionCall({:?}, (", i)?;
                f.debug_list().entries(p.iter()).finish()?;
                write!(f, ")")
            }
        }
    }
}

// Common behaviour across expressions

pub trait IfElse<'ast, T: Field> {
    fn if_else(condition: BooleanExpression<'ast, T>, consequence: Self, alternative: Self)
        -> Self;
}

impl<'ast, T: Field> IfElse<'ast, T> for FieldElementExpression<'ast, T> {
    fn if_else(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
    ) -> Self {
        FieldElementExpression::IfElse(box condition, box consequence, box alternative)
    }
}

impl<'ast, T: Field> IfElse<'ast, T> for BooleanExpression<'ast, T> {
    fn if_else(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
    ) -> Self {
        BooleanExpression::IfElse(box condition, box consequence, box alternative)
    }
}

impl<'ast, T: Field> IfElse<'ast, T> for ArrayExpression<'ast, T> {
    fn if_else(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
    ) -> Self {
        let ty = consequence.inner_type().clone();
        let size = consequence.size();
        ArrayExpressionInner::IfElse(box condition, box consequence, box alternative)
            .annotate(ty, size)
    }
}

impl<'ast, T: Field> IfElse<'ast, T> for StructExpression<'ast, T> {
    fn if_else(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
    ) -> Self {
        let ty = consequence.ty().clone();
        StructExpressionInner::IfElse(box condition, box consequence, box alternative).annotate(ty)
    }
}

pub trait Select<'ast, T: Field> {
    fn select(array: ArrayExpression<'ast, T>, index: FieldElementExpression<'ast, T>) -> Self;
}

impl<'ast, T: Field> Select<'ast, T> for FieldElementExpression<'ast, T> {
    fn select(array: ArrayExpression<'ast, T>, index: FieldElementExpression<'ast, T>) -> Self {
        FieldElementExpression::Select(box array, box index)
    }
}

impl<'ast, T: Field> Select<'ast, T> for BooleanExpression<'ast, T> {
    fn select(array: ArrayExpression<'ast, T>, index: FieldElementExpression<'ast, T>) -> Self {
        BooleanExpression::Select(box array, box index)
    }
}

impl<'ast, T: Field> Select<'ast, T> for ArrayExpression<'ast, T> {
    fn select(array: ArrayExpression<'ast, T>, index: FieldElementExpression<'ast, T>) -> Self {
        let (ty, size) = match array.inner_type() {
            Type::Array(array_type) => (array_type.ty.clone(), array_type.size.clone()),
            _ => unreachable!(),
        };

        ArrayExpressionInner::Select(box array, box index).annotate(*ty, size)
    }
}

impl<'ast, T: Field> Select<'ast, T> for StructExpression<'ast, T> {
    fn select(array: ArrayExpression<'ast, T>, index: FieldElementExpression<'ast, T>) -> Self {
        let members = match array.inner_type().clone() {
            Type::Struct(members) => members,
            _ => unreachable!(),
        };

        StructExpressionInner::Select(box array, box index).annotate(members)
    }
}

pub trait Member<'ast, T: Field> {
    fn member(s: StructExpression<'ast, T>, member_id: MemberId) -> Self;
}

impl<'ast, T: Field> Member<'ast, T> for FieldElementExpression<'ast, T> {
    fn member(s: StructExpression<'ast, T>, member_id: MemberId) -> Self {
        FieldElementExpression::Member(box s, member_id)
    }
}

impl<'ast, T: Field> Member<'ast, T> for BooleanExpression<'ast, T> {
    fn member(s: StructExpression<'ast, T>, member_id: MemberId) -> Self {
        BooleanExpression::Member(box s, member_id)
    }
}

impl<'ast, T: Field> Member<'ast, T> for ArrayExpression<'ast, T> {
    fn member(s: StructExpression<'ast, T>, member_id: MemberId) -> Self {
        let members = s.ty().clone();

        let ty = members
            .into_iter()
            .find(|member| *member.id == member_id)
            .unwrap()
            .ty;

        let (ty, size) = match *ty {
            Type::Array(array_type) => (array_type.ty, array_type.size),
            _ => unreachable!(),
        };

        ArrayExpressionInner::Member(box s, member_id).annotate(*ty, size)
    }
}

impl<'ast, T: Field> Member<'ast, T> for StructExpression<'ast, T> {
    fn member(s: StructExpression<'ast, T>, member_id: MemberId) -> Self {
        let members = s.ty().clone();

        let ty = members
            .into_iter()
            .find(|member| *member.id == member_id)
            .unwrap()
            .ty;

        let members = match *ty {
            Type::Struct(members) => members,
            _ => unreachable!(),
        };

        StructExpressionInner::Member(box s, member_id).annotate(members)
    }
}
