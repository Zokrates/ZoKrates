//! Module containing structs and enums to represent a program.
//!
//! @file absy.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

pub mod abi;
pub mod folder;
pub mod identifier;
pub mod result_folder;

mod integer;
mod parameter;
pub mod types;
mod uint;
mod variable;

pub use self::identifier::CoreIdentifier;
pub use self::parameter::{DeclarationParameter, GParameter};
pub use self::types::{
    ConcreteFunctionKey, ConcreteSignature, ConcreteType, DeclarationFunctionKey,
    DeclarationSignature, DeclarationType, GArrayType, GStructType, GType, GenericIdentifier,
    Signature, StructType, Type, UBitwidth,
};
use crate::typed_absy::types::ConcreteGenericsAssignment;

pub use self::variable::{ConcreteVariable, DeclarationVariable, GVariable, Variable};
use std::path::{Path, PathBuf};

pub use crate::typed_absy::integer::IntExpression;
pub use crate::typed_absy::uint::{bitwidth, UExpression, UExpressionInner, UMetadata};

use crate::embed::FlatEmbed;

use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};
use std::fmt;

pub use crate::typed_absy::types::{ArrayType, FunctionKey, MemberId};

use zokrates_field::Field;

pub use self::folder::Folder;
use crate::typed_absy::abi::{Abi, AbiInput};
use std::ops::{Add, Div, Mul, Sub};

pub use self::identifier::Identifier;

/// An identifier for a `TypedModule`. Typically a path or uri.
pub type OwnedTypedModuleId = PathBuf;
pub type TypedModuleId = Path;

/// A collection of `TypedModule`s
pub type TypedModules<'ast, T> = HashMap<OwnedTypedModuleId, TypedModule<'ast, T>>;

/// A collection of `TypedFunctionSymbol`s
/// # Remarks
/// * It is the role of the semantic checker to make sure there are no duplicates for a given `FunctionKey`
///   in a given `TypedModule`, hence the use of a HashMap
pub type TypedFunctionSymbols<'ast, T> =
    HashMap<DeclarationFunctionKey<'ast>, TypedFunctionSymbol<'ast, T>>;

/// A typed program as a collection of modules, one of them being the main
#[derive(PartialEq, Debug, Clone)]
pub struct TypedProgram<'ast, T> {
    pub modules: TypedModules<'ast, T>,
    pub main: OwnedTypedModuleId,
}

impl<'ast, T> TypedProgram<'ast, T> {
    pub fn main_function(&self) -> TypedFunction<'ast, T> {
        unimplemented!()
    }
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
                .map(|p| {
                    types::ConcreteType::try_from(types::Type::<T>::from(p.id._type.clone()))
                        .map(|ty| AbiInput {
                            public: !p.private,
                            name: p.id.id.to_string(),
                            ty,
                        })
                        .unwrap()
                })
                .collect(),
            outputs: main
                .signature
                .outputs
                .iter()
                .map(|ty| {
                    types::ConcreteType::try_from(types::Type::<T>::from(ty.clone())).unwrap()
                })
                .collect(),
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for TypedProgram<'ast, T> {
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
            writeln!(f)?;
        }
        write!(f, "")
    }
}

/// A typed program as a collection of functions. Types have been resolved during semantic checking.
#[derive(PartialEq, Clone)]
pub struct TypedModule<'ast, T> {
    /// Functions of the program
    pub functions: TypedFunctionSymbols<'ast, T>,
}

#[derive(Clone, PartialEq)]
pub enum TypedFunctionSymbol<'ast, T> {
    Here(TypedFunction<'ast, T>),
    There(DeclarationFunctionKey<'ast>),
    Flat(FlatEmbed),
}

// this should be deriveable but it seems like the bounds are not infered correctly
impl<'ast, T: fmt::Debug> fmt::Debug for TypedFunctionSymbol<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TypedFunctionSymbol::Here(s) => write!(f, "Here({:?})", s),
            TypedFunctionSymbol::There(key) => write!(f, "There({:?})", key),
            TypedFunctionSymbol::Flat(s) => write!(f, "Flat({:?})", s),
        }
    }
}

impl<'ast, T: Field> TypedFunctionSymbol<'ast, T> {
    pub fn signature<'a>(
        &'a self,
        modules: &'a TypedModules<'ast, T>,
    ) -> DeclarationSignature<'ast> {
        match self {
            TypedFunctionSymbol::Here(f) => f.signature.clone(),
            TypedFunctionSymbol::There(key) => modules
                .get(&key.module)
                .unwrap()
                .functions
                .get(key)
                .unwrap()
                .signature(&modules),
            TypedFunctionSymbol::Flat(flat_fun) => flat_fun.signature(),
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for TypedModule<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let res = self
            .functions
            .iter()
            .map(|(key, symbol)| match symbol {
                TypedFunctionSymbol::Here(ref function) => format!("def {}{}", key.id, function),
                TypedFunctionSymbol::There(ref fun_key) => format!(
                    "import {} from \"{}\" as {} // with signature {}",
                    fun_key.id,
                    fun_key.module.display(),
                    key.id,
                    key.signature
                ),
                TypedFunctionSymbol::Flat(ref flat_fun) => {
                    format!("def {}{}:\n\t// hidden", key.id, flat_fun.signature())
                }
            })
            .collect::<Vec<_>>();
        write!(f, "{}", res.join("\n"))
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for TypedModule<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "module(\n\tfunctions:\n\t\t{:?}\n)",
            self.functions
                .iter()
                .map(|x| format!("{:?}", x))
                .collect::<Vec<_>>()
                .join("\n\t\t")
        )
    }
}

/// A typed function
#[derive(Clone, PartialEq, Hash)]
pub struct TypedFunction<'ast, T> {
    /// Arguments of the function
    pub arguments: Vec<DeclarationParameter<'ast>>,
    /// Vector of statements that are executed when running the function
    pub statements: Vec<TypedStatement<'ast, T>>,
    /// function signature
    pub signature: DeclarationSignature<'ast>,
}

impl<'ast, T: fmt::Display> fmt::Display for TypedFunction<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !self.signature.generics.is_empty() {
            write!(
                f,
                "<{}>",
                self.signature
                    .generics
                    .iter()
                    .map(|g| g.as_ref().unwrap().to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )?;
        }
        write!(
            f,
            "({})",
            self.arguments
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>()
                .join(", "),
        )?;

        write!(
            f,
            "{}:",
            match self.signature.outputs.len() {
                0 => "".into(),
                1 => format!(" -> {}", self.signature.outputs[0]),
                _ => format!(
                    " -> ({})",
                    self.signature
                        .outputs
                        .iter()
                        .map(|x| format!("{}", x))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
            }
        )?;

        writeln!(f)?;

        let mut tab = 0;

        for s in &self.statements {
            if let TypedStatement::PopCallLog = s {
                tab -= 1;
            };

            s.fmt_indented(f, 1 + tab)?;
            writeln!(f)?;

            if let TypedStatement::PushCallLog(..) = s {
                tab += 1;
            };
        }

        Ok(())
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for TypedFunction<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "TypedFunction(signature: {:?}, arguments: {:?}, ...):\n{}",
            self.signature,
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
pub enum TypedAssignee<'ast, T> {
    Identifier(Variable<'ast, T>),
    Select(Box<TypedAssignee<'ast, T>>, Box<UExpression<'ast, T>>),
    Member(Box<TypedAssignee<'ast, T>>, MemberId),
}

#[derive(Clone, PartialEq, Hash, Eq, Debug)]
pub struct TypedSpread<'ast, T> {
    pub array: ArrayExpression<'ast, T>,
}

impl<'ast, T> From<ArrayExpression<'ast, T>> for TypedSpread<'ast, T> {
    fn from(array: ArrayExpression<'ast, T>) -> TypedSpread<'ast, T> {
        TypedSpread { array }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for TypedSpread<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "...{}", self.array)
    }
}

#[derive(Clone, PartialEq, Hash, Eq, Debug)]
pub enum TypedExpressionOrSpread<'ast, T> {
    Expression(TypedExpression<'ast, T>),
    Spread(TypedSpread<'ast, T>),
}

impl<'ast, T: Clone> TypedExpressionOrSpread<'ast, T> {
    pub fn size(&self) -> UExpression<'ast, T> {
        match self {
            TypedExpressionOrSpread::Expression(..) => 1u32.into(),
            TypedExpressionOrSpread::Spread(s) => s.array.size(),
        }
    }
}

impl<'ast, T> TryFrom<TypedExpressionOrSpread<'ast, T>> for TypedExpression<'ast, T> {
    type Error = ();

    fn try_from(
        e: TypedExpressionOrSpread<'ast, T>,
    ) -> Result<TypedExpression<'ast, T>, Self::Error> {
        if let TypedExpressionOrSpread::Expression(e) = e {
            Ok(e)
        } else {
            Err(())
        }
    }
}

impl<'ast, T, U: Into<TypedExpression<'ast, T>>> From<U> for TypedExpressionOrSpread<'ast, T> {
    fn from(e: U) -> Self {
        TypedExpressionOrSpread::Expression(e.into())
    }
}

impl<'ast, T: Clone> TypedExpressionOrSpread<'ast, T> {
    pub fn get_type(&self) -> (Type<'ast, T>, UExpression<'ast, T>) {
        match self {
            TypedExpressionOrSpread::Expression(e) => (e.get_type(), 1u32.into()),
            TypedExpressionOrSpread::Spread(s) => (s.array.inner_type().clone(), s.array.size()),
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for TypedExpressionOrSpread<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TypedExpressionOrSpread::Expression(e) => write!(f, "{}", e),
            TypedExpressionOrSpread::Spread(s) => write!(f, "{}", s),
        }
    }
}

impl<'ast, T> From<Variable<'ast, T>> for TypedAssignee<'ast, T> {
    fn from(v: Variable<'ast, T>) -> Self {
        TypedAssignee::Identifier(v)
    }
}

impl<'ast, T: Clone> Typed<'ast, T> for TypedAssignee<'ast, T> {
    fn get_type(&self) -> Type<'ast, T> {
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

impl<'ast, T: fmt::Debug> fmt::Debug for TypedAssignee<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedAssignee::Identifier(ref s) => write!(f, "{:?}", s.id),
            TypedAssignee::Select(ref a, ref e) => write!(f, "Select({:?}, {:?})", a, e),
            TypedAssignee::Member(ref s, ref m) => write!(f, "Member({:?}, {:?})", s, m),
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for TypedAssignee<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedAssignee::Identifier(ref s) => write!(f, "{}", s.id),
            TypedAssignee::Select(ref a, ref e) => write!(f, "{}[{}]", a, e),
            TypedAssignee::Member(ref s, ref m) => write!(f, "{}.{}", s, m),
        }
    }
}

/// A statement in a `TypedFunction`
#[allow(clippy::large_enum_variant)]
#[derive(Clone, PartialEq, Hash, Eq)]
pub enum TypedStatement<'ast, T> {
    Return(Vec<TypedExpression<'ast, T>>),
    Definition(TypedAssignee<'ast, T>, TypedExpression<'ast, T>),
    Declaration(Variable<'ast, T>),
    Assertion(BooleanExpression<'ast, T>),
    For(
        Variable<'ast, T>,
        UExpression<'ast, T>,
        UExpression<'ast, T>,
        Vec<TypedStatement<'ast, T>>,
    ),
    MultipleDefinition(Vec<TypedAssignee<'ast, T>>, TypedExpressionList<'ast, T>),
    // Aux
    PushCallLog(
        DeclarationFunctionKey<'ast>,
        ConcreteGenericsAssignment<'ast>,
    ),
    PopCallLog,
}

impl<'ast, T: fmt::Debug> fmt::Debug for TypedStatement<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedStatement::Return(ref exprs) => {
                write!(f, "Return(")?;
                for (i, expr) in exprs.iter().enumerate() {
                    write!(f, "{:?}", expr)?;
                    if i < exprs.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            TypedStatement::Declaration(ref var) => write!(f, "({:?})", var),
            TypedStatement::Definition(ref lhs, ref rhs) => {
                write!(f, "Definition({:?}, {:?})", lhs, rhs)
            }
            TypedStatement::Assertion(ref e) => write!(f, "Assertion({:?})", e),
            TypedStatement::For(ref var, ref start, ref stop, ref list) => {
                writeln!(f, "for {:?} in {:?}..{:?} do", var, start, stop)?;
                for l in list {
                    writeln!(f, "\t\t{:?}", l)?;
                }
                write!(f, "\tendfor")
            }
            TypedStatement::MultipleDefinition(ref lhs, ref rhs) => {
                write!(f, "MultipleDefinition({:?}, {:?})", lhs, rhs)
            }
            TypedStatement::PushCallLog(ref key, ref generics) => {
                write!(f, "PushCallLog({:?}, {:?})", key, generics)
            }
            TypedStatement::PopCallLog => write!(f, "PopCallLog"),
        }
    }
}

impl<'ast, T: fmt::Display> TypedStatement<'ast, T> {
    fn fmt_indented(&self, f: &mut fmt::Formatter, depth: usize) -> fmt::Result {
        match self {
            TypedStatement::For(variable, from, to, statements) => {
                write!(f, "{}", "\t".repeat(depth))?;
                writeln!(f, "for {} in {}..{} do", variable, from, to)?;
                for s in statements {
                    s.fmt_indented(f, depth + 1)?;
                    writeln!(f)?;
                }
                write!(f, "{}endfor", "\t".repeat(depth))
            }
            s => write!(f, "{}{}", "\t".repeat(depth), s),
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for TypedStatement<'ast, T> {
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
            TypedStatement::Assertion(ref e) => write!(f, "assert({})", e),
            TypedStatement::For(ref var, ref start, ref stop, ref list) => {
                writeln!(f, "for {} in {}..{} do", var, start, stop)?;
                for l in list {
                    writeln!(f, "\t\t{}", l)?;
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
            TypedStatement::PushCallLog(ref key, ref generics) => write!(
                f,
                "// PUSH CALL TO {}/{}::<{}>",
                key.module.display(),
                key.id,
                generics,
            ),
            TypedStatement::PopCallLog => write!(f, "// POP CALL",),
        }
    }
}

pub trait Typed<'ast, T> {
    fn get_type(&self) -> Type<'ast, T>;
}

/// A typed expression
#[allow(clippy::large_enum_variant)]
#[derive(Clone, PartialEq, Hash, Eq)]
pub enum TypedExpression<'ast, T> {
    Boolean(BooleanExpression<'ast, T>),
    FieldElement(FieldElementExpression<'ast, T>),
    Uint(UExpression<'ast, T>),
    Array(ArrayExpression<'ast, T>),
    Struct(StructExpression<'ast, T>),
    Int(IntExpression<'ast, T>),
}

impl<'ast, T> From<BooleanExpression<'ast, T>> for TypedExpression<'ast, T> {
    fn from(e: BooleanExpression<'ast, T>) -> TypedExpression<T> {
        TypedExpression::Boolean(e)
    }
}

impl<'ast, T> From<FieldElementExpression<'ast, T>> for TypedExpression<'ast, T> {
    fn from(e: FieldElementExpression<'ast, T>) -> TypedExpression<T> {
        TypedExpression::FieldElement(e)
    }
}

impl<'ast, T> From<IntExpression<'ast, T>> for TypedExpression<'ast, T> {
    fn from(e: IntExpression<'ast, T>) -> TypedExpression<T> {
        TypedExpression::Int(e)
    }
}

impl<'ast, T> From<UExpression<'ast, T>> for TypedExpression<'ast, T> {
    fn from(e: UExpression<'ast, T>) -> TypedExpression<T> {
        TypedExpression::Uint(e)
    }
}

impl<'ast, T> From<ArrayExpression<'ast, T>> for TypedExpression<'ast, T> {
    fn from(e: ArrayExpression<'ast, T>) -> TypedExpression<T> {
        TypedExpression::Array(e)
    }
}

impl<'ast, T> From<StructExpression<'ast, T>> for TypedExpression<'ast, T> {
    fn from(e: StructExpression<'ast, T>) -> TypedExpression<T> {
        TypedExpression::Struct(e)
    }
}

impl<'ast, T: fmt::Display> fmt::Display for TypedExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedExpression::Boolean(ref e) => write!(f, "{}", e),
            TypedExpression::FieldElement(ref e) => write!(f, "{}", e),
            TypedExpression::Uint(ref e) => write!(f, "{}", e),
            TypedExpression::Array(ref e) => write!(f, "{}", e),
            TypedExpression::Struct(ref s) => write!(f, "{}", s),
            TypedExpression::Int(ref s) => write!(f, "{}", s),
        }
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for TypedExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedExpression::Boolean(ref e) => write!(f, "{:?}", e),
            TypedExpression::FieldElement(ref e) => write!(f, "{:?}", e),
            TypedExpression::Uint(ref e) => write!(f, "{:?}", e),
            TypedExpression::Array(ref e) => write!(f, "{:?}", e),
            TypedExpression::Struct(ref s) => write!(f, "{:?}", s),
            TypedExpression::Int(ref s) => write!(f, "{:?}", s),
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for ArrayExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.inner)
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for ArrayExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.inner)
    }
}

impl<'ast, T: fmt::Display> fmt::Display for StructExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.inner {
            StructExpressionInner::Identifier(ref var) => write!(f, "{}", var),
            StructExpressionInner::Value(ref values) => write!(
                f,
                "{} {{{}}}",
                self.ty.name(),
                self.ty
                    .iter()
                    .map(|member| member.id.clone())
                    .zip(values.iter())
                    .map(|(id, o)| format!("{}: {}", id, o))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            StructExpressionInner::FunctionCall(ref key, ref generics, ref p) => {
                write!(f, "{}", key.id,)?;
                if !generics.is_empty() {
                    write!(
                        f,
                        "::<{}>",
                        generics
                            .iter()
                            .map(|g| g
                                .as_ref()
                                .map(|g| g.to_string())
                                .unwrap_or_else(|| '_'.to_string()))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )?;
                }
                write!(f, "(")?;
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

impl<'ast, T: fmt::Debug> fmt::Debug for StructExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.inner)
    }
}

impl<'ast, T: Clone> Typed<'ast, T> for TypedExpression<'ast, T> {
    fn get_type(&self) -> Type<'ast, T> {
        match *self {
            TypedExpression::Boolean(ref e) => e.get_type(),
            TypedExpression::FieldElement(ref e) => e.get_type(),
            TypedExpression::Array(ref e) => e.get_type(),
            TypedExpression::Uint(ref e) => e.get_type(),
            TypedExpression::Struct(ref s) => s.get_type(),
            TypedExpression::Int(_) => Type::Int,
        }
    }
}

impl<'ast, T: Clone> Typed<'ast, T> for ArrayExpression<'ast, T> {
    fn get_type(&self) -> Type<'ast, T> {
        Type::array(*self.ty.clone())
    }
}

impl<'ast, T: Clone> Typed<'ast, T> for StructExpression<'ast, T> {
    fn get_type(&self) -> Type<'ast, T> {
        Type::Struct(self.ty.clone())
    }
}

impl<'ast, T: Clone> Typed<'ast, T> for FieldElementExpression<'ast, T> {
    fn get_type(&self) -> Type<'ast, T> {
        Type::FieldElement
    }
}

impl<'ast, T: Clone> Typed<'ast, T> for UExpression<'ast, T> {
    fn get_type(&self) -> Type<'ast, T> {
        Type::Uint(self.bitwidth)
    }
}

impl<'ast, T: Clone> Typed<'ast, T> for BooleanExpression<'ast, T> {
    fn get_type(&self) -> Type<'ast, T> {
        Type::Boolean
    }
}

pub trait MultiTyped<'ast, T> {
    fn get_types(&self) -> &Vec<Type<'ast, T>>;
}

#[derive(Clone, PartialEq, Hash, Eq)]
pub enum TypedExpressionList<'ast, T> {
    FunctionCall(
        DeclarationFunctionKey<'ast>,
        Vec<Option<UExpression<'ast, T>>>,
        Vec<TypedExpression<'ast, T>>,
        Vec<Type<'ast, T>>,
    ),
    EmbedCall(
        FlatEmbed,
        Vec<u32>,
        Vec<TypedExpression<'ast, T>>,
        Vec<Type<'ast, T>>,
    ),
}

impl<'ast, T> MultiTyped<'ast, T> for TypedExpressionList<'ast, T> {
    fn get_types(&self) -> &Vec<Type<'ast, T>> {
        match *self {
            TypedExpressionList::FunctionCall(_, _, _, ref types) => types,
            TypedExpressionList::EmbedCall(_, _, _, ref types) => types,
        }
    }
}

/// An expression of type `field`
#[derive(Clone, PartialEq, Hash, Eq)]
pub enum FieldElementExpression<'ast, T> {
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
        Box<UExpression<'ast, T>>,
    ),
    IfElse(
        Box<BooleanExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    Neg(Box<FieldElementExpression<'ast, T>>),
    Pos(Box<FieldElementExpression<'ast, T>>),
    FunctionCall(
        DeclarationFunctionKey<'ast>,
        Vec<Option<UExpression<'ast, T>>>,
        Vec<TypedExpression<'ast, T>>,
    ),
    Member(Box<StructExpression<'ast, T>>, MemberId),
    Select(Box<ArrayExpression<'ast, T>>, Box<UExpression<'ast, T>>),
}
impl<'ast, T> Add for FieldElementExpression<'ast, T> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        FieldElementExpression::Add(box self, box other)
    }
}

impl<'ast, T> Sub for FieldElementExpression<'ast, T> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        FieldElementExpression::Sub(box self, box other)
    }
}

impl<'ast, T> Mul for FieldElementExpression<'ast, T> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        FieldElementExpression::Mult(box self, box other)
    }
}

impl<'ast, T> Div for FieldElementExpression<'ast, T> {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        FieldElementExpression::Div(box self, box other)
    }
}

impl<'ast, T> FieldElementExpression<'ast, T> {
    pub fn pow(self, other: UExpression<'ast, T>) -> Self {
        FieldElementExpression::Pow(box self, box other)
    }
}

impl<'ast, T> From<T> for FieldElementExpression<'ast, T> {
    fn from(n: T) -> Self {
        FieldElementExpression::Number(n)
    }
}

/// An expression of type `bool`
#[derive(Clone, PartialEq, Hash, Eq)]
pub enum BooleanExpression<'ast, T> {
    Identifier(Identifier<'ast>),
    Value(bool),
    FieldLt(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    FieldLe(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    FieldGe(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    FieldGt(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    UintLt(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    UintLe(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    UintGe(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    UintGt(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    FieldEq(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    BoolEq(
        Box<BooleanExpression<'ast, T>>,
        Box<BooleanExpression<'ast, T>>,
    ),
    ArrayEq(Box<ArrayExpression<'ast, T>>, Box<ArrayExpression<'ast, T>>),
    StructEq(
        Box<StructExpression<'ast, T>>,
        Box<StructExpression<'ast, T>>,
    ),
    UintEq(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
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
    FunctionCall(
        DeclarationFunctionKey<'ast>,
        Vec<Option<UExpression<'ast, T>>>,
        Vec<TypedExpression<'ast, T>>,
    ),
    Select(Box<ArrayExpression<'ast, T>>, Box<UExpression<'ast, T>>),
}

impl<'ast, T> From<bool> for BooleanExpression<'ast, T> {
    fn from(b: bool) -> Self {
        BooleanExpression::Value(b)
    }
}

/// An expression of type `array`
/// # Remarks
/// * Contrary to basic types which are represented as enums, we wrap an enum `ArrayExpressionInner` in a struct in order to keep track of the type (content and size)
/// of the array. Only using an enum would require generics, which would propagate up to TypedExpression which we want to keep simple, hence this "runtime"
/// type checking
#[derive(Clone, PartialEq, Hash, Eq)]
pub struct ArrayExpression<'ast, T> {
    ty: Box<ArrayType<'ast, T>>,
    inner: ArrayExpressionInner<'ast, T>,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct ArrayValue<'ast, T>(pub Vec<TypedExpressionOrSpread<'ast, T>>);

impl<'ast, T> From<Vec<TypedExpressionOrSpread<'ast, T>>> for ArrayValue<'ast, T> {
    fn from(array: Vec<TypedExpressionOrSpread<'ast, T>>) -> Self {
        Self(array)
    }
}

impl<'ast, T> IntoIterator for ArrayValue<'ast, T> {
    type Item = TypedExpressionOrSpread<'ast, T>;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'ast, T: Clone> ArrayValue<'ast, T> {
    fn expression_at_aux<U: Select<'ast, T> + Into<TypedExpression<'ast, T>>>(
        v: TypedExpressionOrSpread<'ast, T>,
    ) -> Vec<Option<TypedExpression<'ast, T>>> {
        match v {
            TypedExpressionOrSpread::Expression(e) => vec![Some(e.clone())],
            TypedExpressionOrSpread::Spread(s) => match s.array.size().into_inner() {
                UExpressionInner::Value(size) => {
                    let array_ty = s.array.get_array_type().clone();

                    match s.array.into_inner() {
                        ArrayExpressionInner::Value(v) => v
                            .into_iter()
                            .flat_map(Self::expression_at_aux::<U>)
                            .collect(),
                        a => (0..size)
                            .map(|i| {
                                Some(
                                    U::select(
                                        a.clone()
                                            .annotate(*array_ty.ty.clone(), array_ty.size.clone()),
                                        i as u32,
                                    )
                                    .into(),
                                )
                            })
                            .collect(),
                    }
                }
                _ => vec![None],
            },
        }
    }

    pub fn expression_at<U: Select<'ast, T> + Into<TypedExpression<'ast, T>>>(
        &self,
        index: usize,
    ) -> Option<TypedExpression<'ast, T>> {
        self.0
            .iter()
            .map(|v| Self::expression_at_aux::<U>(v.clone()))
            .flatten()
            .take_while(|e| e.is_some())
            .map(|e| e.unwrap())
            .nth(index)
    }
}

impl<'ast, T> ArrayValue<'ast, T> {
    fn iter(&self) -> std::slice::Iter<TypedExpressionOrSpread<'ast, T>> {
        self.0.iter()
    }
}

impl<'ast, T> std::iter::FromIterator<TypedExpressionOrSpread<'ast, T>> for ArrayValue<'ast, T> {
    fn from_iter<I: IntoIterator<Item = TypedExpressionOrSpread<'ast, T>>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
    }
}

#[derive(Clone, PartialEq, Hash, Eq)]
pub enum ArrayExpressionInner<'ast, T> {
    Identifier(Identifier<'ast>),
    Value(ArrayValue<'ast, T>),
    FunctionCall(
        DeclarationFunctionKey<'ast>,
        Vec<Option<UExpression<'ast, T>>>,
        Vec<TypedExpression<'ast, T>>,
    ),
    IfElse(
        Box<BooleanExpression<'ast, T>>,
        Box<ArrayExpression<'ast, T>>,
        Box<ArrayExpression<'ast, T>>,
    ),
    Member(Box<StructExpression<'ast, T>>, MemberId),
    Select(Box<ArrayExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    Slice(
        Box<ArrayExpression<'ast, T>>,
        Box<UExpression<'ast, T>>,
        Box<UExpression<'ast, T>>,
    ),
    Repeat(Box<TypedExpression<'ast, T>>, Box<UExpression<'ast, T>>),
}

impl<'ast, T> ArrayExpressionInner<'ast, T> {
    pub fn annotate<S: Into<UExpression<'ast, T>>>(
        self,
        ty: Type<'ast, T>,
        size: S,
    ) -> ArrayExpression<'ast, T> {
        ArrayExpression {
            ty: box (ty, size.into()).into(),
            inner: self,
        }
    }
}

impl<'ast, T: Clone> ArrayExpression<'ast, T> {
    pub fn inner_type(&self) -> &Type<'ast, T> {
        &self.ty.ty
    }

    pub fn size(&self) -> UExpression<'ast, T> {
        self.ty.size.clone()
    }

    pub fn as_inner(&self) -> &ArrayExpressionInner<'ast, T> {
        &self.inner
    }

    pub fn as_inner_mut(&mut self) -> &mut ArrayExpressionInner<'ast, T> {
        &mut self.inner
    }

    pub fn into_inner(self) -> ArrayExpressionInner<'ast, T> {
        self.inner
    }

    pub fn get_array_type(&self) -> ArrayType<'ast, T> {
        ArrayType {
            size: self.size(),
            ty: box self.inner_type().clone(),
        }
    }
}

#[derive(Clone, PartialEq, Hash, Eq)]
pub struct StructExpression<'ast, T> {
    ty: StructType<'ast, T>,
    inner: StructExpressionInner<'ast, T>,
}

impl<'ast, T: Field> StructExpression<'ast, T> {
    pub fn try_from_typed(
        e: TypedExpression<'ast, T>,
        target_struct_ty: StructType<'ast, T>,
    ) -> Result<Self, TypedExpression<'ast, T>> {
        match e {
            TypedExpression::Struct(e) => {
                if e.ty() == &target_struct_ty {
                    Ok(e)
                } else {
                    Err(TypedExpression::Struct(e))
                }
            }
            e => Err(e),
        }
    }
}

impl<'ast, T> StructExpression<'ast, T> {
    pub fn ty(&self) -> &StructType<'ast, T> {
        &self.ty
    }

    pub fn as_inner(&self) -> &StructExpressionInner<'ast, T> {
        &self.inner
    }

    pub fn as_inner_mut(&mut self) -> &mut StructExpressionInner<'ast, T> {
        &mut self.inner
    }

    pub fn into_inner(self) -> StructExpressionInner<'ast, T> {
        self.inner
    }
}

#[derive(Clone, PartialEq, Hash, Eq)]
pub enum StructExpressionInner<'ast, T> {
    Identifier(Identifier<'ast>),
    Value(Vec<TypedExpression<'ast, T>>),
    FunctionCall(
        DeclarationFunctionKey<'ast>,
        Vec<Option<UExpression<'ast, T>>>,
        Vec<TypedExpression<'ast, T>>,
    ),
    IfElse(
        Box<BooleanExpression<'ast, T>>,
        Box<StructExpression<'ast, T>>,
        Box<StructExpression<'ast, T>>,
    ),
    Member(Box<StructExpression<'ast, T>>, MemberId),
    Select(Box<ArrayExpression<'ast, T>>, Box<UExpression<'ast, T>>),
}

impl<'ast, T> StructExpressionInner<'ast, T> {
    pub fn annotate(self, ty: StructType<'ast, T>) -> StructExpression<'ast, T> {
        StructExpression { ty, inner: self }
    }
}

// Downcasts
// Due to the fact that we keep TypedExpression simple, we end up with ArrayExpressionInner::Value whose elements are any TypedExpression, but we enforce by
// construction that these elements are of the type declared in the corresponding ArrayExpression. As we know this by construction, we can downcast the TypedExpression to the correct type
// ArrayExpression { type: Type::FieldElement, size: 42, inner: [TypedExpression::FieldElement(FieldElementExpression), ...]} <- the fact that inner only contains field elements is not enforced by the rust type system
impl<'ast, T> TryFrom<TypedExpression<'ast, T>> for FieldElementExpression<'ast, T> {
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

impl<'ast, T> TryFrom<TypedExpression<'ast, T>> for BooleanExpression<'ast, T> {
    type Error = ();

    fn try_from(te: TypedExpression<'ast, T>) -> Result<BooleanExpression<'ast, T>, Self::Error> {
        match te {
            TypedExpression::Boolean(e) => Ok(e),
            _ => Err(()),
        }
    }
}

impl<'ast, T> TryFrom<TypedExpression<'ast, T>> for UExpression<'ast, T> {
    type Error = ();

    fn try_from(te: TypedExpression<'ast, T>) -> Result<UExpression<'ast, T>, Self::Error> {
        match te {
            TypedExpression::Uint(e) => Ok(e),
            _ => Err(()),
        }
    }
}

impl<'ast, T> TryFrom<TypedExpression<'ast, T>> for ArrayExpression<'ast, T> {
    type Error = ();

    fn try_from(te: TypedExpression<'ast, T>) -> Result<ArrayExpression<'ast, T>, Self::Error> {
        match te {
            TypedExpression::Array(e) => Ok(e),
            _ => Err(()),
        }
    }
}

impl<'ast, T> TryFrom<TypedExpression<'ast, T>> for IntExpression<'ast, T> {
    type Error = ();

    fn try_from(te: TypedExpression<'ast, T>) -> Result<IntExpression<'ast, T>, Self::Error> {
        match te {
            TypedExpression::Int(e) => Ok(e),
            _ => Err(()),
        }
    }
}

impl<'ast, T> TryFrom<TypedExpression<'ast, T>> for StructExpression<'ast, T> {
    type Error = ();

    fn try_from(te: TypedExpression<'ast, T>) -> Result<StructExpression<'ast, T>, Self::Error> {
        match te {
            TypedExpression::Struct(e) => Ok(e),
            _ => Err(()),
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for FieldElementExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FieldElementExpression::Number(ref i) => write!(f, "{}f", i),
            FieldElementExpression::Identifier(ref var) => write!(f, "{}", var),
            FieldElementExpression::Add(ref lhs, ref rhs) => write!(f, "({} + {})", lhs, rhs),
            FieldElementExpression::Sub(ref lhs, ref rhs) => write!(f, "({} - {})", lhs, rhs),
            FieldElementExpression::Mult(ref lhs, ref rhs) => write!(f, "({} * {})", lhs, rhs),
            FieldElementExpression::Div(ref lhs, ref rhs) => write!(f, "({} / {})", lhs, rhs),
            FieldElementExpression::Pow(ref lhs, ref rhs) => write!(f, "{}**{}", lhs, rhs),
            FieldElementExpression::Neg(ref e) => write!(f, "(-{})", e),
            FieldElementExpression::Pos(ref e) => write!(f, "(+{})", e),
            FieldElementExpression::IfElse(ref condition, ref consequent, ref alternative) => {
                write!(
                    f,
                    "if {} then {} else {} fi",
                    condition, consequent, alternative
                )
            }
            FieldElementExpression::FunctionCall(ref k, ref generics, ref p) => {
                write!(f, "{}", k.id,)?;
                if !generics.is_empty() {
                    write!(
                        f,
                        "::<{}>",
                        generics
                            .iter()
                            .map(|g| g
                                .as_ref()
                                .map(|g| g.to_string())
                                .unwrap_or_else(|| '_'.to_string()))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )?;
                }
                write!(f, "(")?;
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

impl<'ast, T: fmt::Display> fmt::Display for UExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.inner {
            UExpressionInner::Value(ref v) => write!(f, "{}", v),
            UExpressionInner::Identifier(ref var) => write!(f, "{}", var),
            UExpressionInner::Add(ref lhs, ref rhs) => write!(f, "({} + {})", lhs, rhs),
            UExpressionInner::And(ref lhs, ref rhs) => write!(f, "({} & {})", lhs, rhs),
            UExpressionInner::Or(ref lhs, ref rhs) => write!(f, "({} | {})", lhs, rhs),
            UExpressionInner::Xor(ref lhs, ref rhs) => write!(f, "({} ^ {})", lhs, rhs),
            UExpressionInner::Sub(ref lhs, ref rhs) => write!(f, "({} - {})", lhs, rhs),
            UExpressionInner::Mult(ref lhs, ref rhs) => write!(f, "({} * {})", lhs, rhs),
            UExpressionInner::FloorSub(ref lhs, ref rhs) => {
                write!(f, "(FLOOR_SUB({}, {}))", lhs, rhs)
            }
            UExpressionInner::Div(ref lhs, ref rhs) => write!(f, "({} / {})", lhs, rhs),
            UExpressionInner::Rem(ref lhs, ref rhs) => write!(f, "({} % {})", lhs, rhs),
            UExpressionInner::RightShift(ref e, ref by) => write!(f, "({} >> {})", e, by),
            UExpressionInner::LeftShift(ref e, ref by) => write!(f, "({} << {})", e, by),
            UExpressionInner::Not(ref e) => write!(f, "!{}", e),
            UExpressionInner::Neg(ref e) => write!(f, "(-{})", e),
            UExpressionInner::Pos(ref e) => write!(f, "(+{})", e),
            UExpressionInner::Select(ref id, ref index) => write!(f, "{}[{}]", id, index),
            UExpressionInner::FunctionCall(ref k, ref generics, ref p) => {
                write!(f, "{}", k.id,)?;
                if !generics.is_empty() {
                    write!(
                        f,
                        "::<{}>",
                        generics
                            .iter()
                            .map(|g| g
                                .as_ref()
                                .map(|g| g.to_string())
                                .unwrap_or_else(|| '_'.to_string()))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )?;
                }
                write!(f, "(")?;
                for (i, param) in p.iter().enumerate() {
                    write!(f, "{}", param)?;
                    if i < p.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            UExpressionInner::IfElse(ref condition, ref consequent, ref alternative) => write!(
                f,
                "if {} then {} else {} fi",
                condition, consequent, alternative
            ),
            UExpressionInner::Member(ref struc, ref id) => write!(f, "{}.{}", struc, id),
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for BooleanExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            BooleanExpression::Identifier(ref var) => write!(f, "{}", var),
            BooleanExpression::FieldLt(ref lhs, ref rhs) => write!(f, "{} < {}", lhs, rhs),
            BooleanExpression::FieldLe(ref lhs, ref rhs) => write!(f, "{} <= {}", lhs, rhs),
            BooleanExpression::FieldGe(ref lhs, ref rhs) => write!(f, "{} >= {}", lhs, rhs),
            BooleanExpression::FieldGt(ref lhs, ref rhs) => write!(f, "{} > {}", lhs, rhs),
            BooleanExpression::UintLt(ref lhs, ref rhs) => write!(f, "{} < {}", lhs, rhs),
            BooleanExpression::UintLe(ref lhs, ref rhs) => write!(f, "{} <= {}", lhs, rhs),
            BooleanExpression::UintGe(ref lhs, ref rhs) => write!(f, "{} >= {}", lhs, rhs),
            BooleanExpression::UintGt(ref lhs, ref rhs) => write!(f, "{} > {}", lhs, rhs),
            BooleanExpression::FieldEq(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            BooleanExpression::BoolEq(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            BooleanExpression::ArrayEq(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            BooleanExpression::StructEq(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            BooleanExpression::UintEq(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            BooleanExpression::Or(ref lhs, ref rhs) => write!(f, "{} || {}", lhs, rhs),
            BooleanExpression::And(ref lhs, ref rhs) => write!(f, "{} && {}", lhs, rhs),
            BooleanExpression::Not(ref exp) => write!(f, "!{}", exp),
            BooleanExpression::Value(b) => write!(f, "{}", b),
            BooleanExpression::FunctionCall(ref k, ref generics, ref p) => {
                write!(f, "{}", k.id,)?;
                if !generics.is_empty() {
                    write!(
                        f,
                        "::<{}>",
                        generics
                            .iter()
                            .map(|g| g
                                .as_ref()
                                .map(|g| g.to_string())
                                .unwrap_or_else(|| '_'.to_string()))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )?;
                }
                write!(f, "(")?;
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

impl<'ast, T: fmt::Display> fmt::Display for ArrayExpressionInner<'ast, T> {
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
            ArrayExpressionInner::FunctionCall(ref key, ref generics, ref p) => {
                write!(f, "{}", key.id,)?;
                if !generics.is_empty() {
                    write!(
                        f,
                        "::<{}>",
                        generics
                            .iter()
                            .map(|g| g
                                .as_ref()
                                .map(|g| g.to_string())
                                .unwrap_or_else(|| '_'.to_string()))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )?;
                }
                write!(f, "(")?;
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
            ArrayExpressionInner::Slice(ref a, ref from, ref to) => {
                write!(f, "{}[{}..{}]", a, from, to)
            }
            ArrayExpressionInner::Repeat(ref e, ref count) => {
                write!(f, "[{}; {}]", e, count)
            }
        }
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for BooleanExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            BooleanExpression::Identifier(ref var) => write!(f, "Ide({})", var),
            BooleanExpression::Value(b) => write!(f, "Value({})", b),
            BooleanExpression::IfElse(ref condition, ref consequent, ref alternative) => write!(
                f,
                "IfElse({:?}, {:?}, {:?})",
                condition, consequent, alternative
            ),
            BooleanExpression::FieldLt(ref lhs, ref rhs) => {
                write!(f, "FieldLt({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::FieldLe(ref lhs, ref rhs) => {
                write!(f, "FieldLe({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::FieldGe(ref lhs, ref rhs) => {
                write!(f, "FieldGe({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::FieldGt(ref lhs, ref rhs) => {
                write!(f, "FieldGt({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::UintLt(ref lhs, ref rhs) => {
                write!(f, "UintLt({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::UintLe(ref lhs, ref rhs) => {
                write!(f, "UintLe({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::UintGe(ref lhs, ref rhs) => {
                write!(f, "UintGe({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::UintGt(ref lhs, ref rhs) => {
                write!(f, "UintGt({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::FieldEq(ref lhs, ref rhs) => {
                write!(f, "FieldEq({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::BoolEq(ref lhs, ref rhs) => {
                write!(f, "BoolEq({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::ArrayEq(ref lhs, ref rhs) => {
                write!(f, "ArrayEq({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::StructEq(ref lhs, ref rhs) => {
                write!(f, "StructEq({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::UintEq(ref lhs, ref rhs) => {
                write!(f, "UintEq({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::And(ref lhs, ref rhs) => write!(f, "And({:?}, {:?})", lhs, rhs),
            BooleanExpression::Not(ref exp) => write!(f, "Not({:?})", exp),
            BooleanExpression::FunctionCall(ref i, ref g, ref p) => {
                write!(f, "FunctionCall({:?}, {:?}, (", g, i)?;
                f.debug_list().entries(p.iter()).finish()?;
                write!(f, ")")
            }
            BooleanExpression::Select(ref array, ref index) => {
                write!(f, "Select({:?}, {:?})", array, index)
            }
            BooleanExpression::Member(ref struc, ref id) => {
                write!(f, "Access({:?}, {:?})", struc, id)
            }
            BooleanExpression::Or(ref lhs, ref rhs) => write!(f, "Or({:?}, {:?})", lhs, rhs),
        }
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for FieldElementExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FieldElementExpression::Number(ref i) => write!(f, "Num({:?})", i),
            FieldElementExpression::Identifier(ref var) => write!(f, "Ide({:?})", var),
            FieldElementExpression::Add(ref lhs, ref rhs) => write!(f, "Add({:?}, {:?})", lhs, rhs),
            FieldElementExpression::Sub(ref lhs, ref rhs) => write!(f, "Sub({:?}, {:?})", lhs, rhs),
            FieldElementExpression::Mult(ref lhs, ref rhs) => {
                write!(f, "Mult({:?}, {:?})", lhs, rhs)
            }
            FieldElementExpression::Div(ref lhs, ref rhs) => write!(f, "Div({:?}, {:?})", lhs, rhs),
            FieldElementExpression::Pow(ref lhs, ref rhs) => write!(f, "Pow({:?}, {:?})", lhs, rhs),
            FieldElementExpression::Neg(ref e) => write!(f, "Neg({:?})", e),
            FieldElementExpression::Pos(ref e) => write!(f, "Pos({:?})", e),
            FieldElementExpression::IfElse(ref condition, ref consequent, ref alternative) => {
                write!(
                    f,
                    "IfElse({:?}, {:?}, {:?})",
                    condition, consequent, alternative
                )
            }
            FieldElementExpression::FunctionCall(ref i, ref g, ref p) => {
                write!(f, "FunctionCall({:?}, {:?}, (", g, i)?;
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

impl<'ast, T: fmt::Debug> fmt::Debug for ArrayExpressionInner<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ArrayExpressionInner::Identifier(ref var) => write!(f, "Identifier({:?})", var),
            ArrayExpressionInner::Value(ref values) => write!(f, "Value({:?})", values),
            ArrayExpressionInner::FunctionCall(ref i, ref g, ref p) => {
                write!(f, "FunctionCall({:?}, {:?}, (", g, i)?;
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
            ArrayExpressionInner::Select(ref array, ref index) => {
                write!(f, "Select({:?}, {:?})", array, index)
            }
            ArrayExpressionInner::Slice(ref array, ref from, ref to) => {
                write!(f, "Slice({:?}, {:?}, {:?})", array, from, to)
            }
            ArrayExpressionInner::Repeat(ref e, ref count) => {
                write!(f, "Repeat({:?}, {:?})", e, count)
            }
        }
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for StructExpressionInner<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            StructExpressionInner::Identifier(ref var) => write!(f, "{:?}", var),
            StructExpressionInner::Value(ref values) => write!(f, "{:?}", values),
            StructExpressionInner::FunctionCall(ref i, ref g, ref p) => {
                write!(f, "FunctionCall({:?}, {:?}, (", g, i)?;
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

impl<'ast, T: fmt::Display> fmt::Display for TypedExpressionList<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedExpressionList::FunctionCall(ref k, ref generics, ref p, _) => {
                write!(f, "{}", k.id,)?;
                if !generics.is_empty() {
                    write!(
                        f,
                        "::<{}>",
                        generics
                            .iter()
                            .map(|g| g
                                .as_ref()
                                .map(|g| g.to_string())
                                .unwrap_or_else(|| '_'.to_string()))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )?;
                }
                write!(f, "(")?;
                for (i, param) in p.iter().enumerate() {
                    write!(f, "{}", param)?;
                    if i < p.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            TypedExpressionList::EmbedCall(ref embed, ref generics, ref p, _) => {
                write!(f, "{}", embed.id())?;
                if !generics.is_empty() {
                    write!(
                        f,
                        "::<{}>",
                        generics
                            .iter()
                            .map(|g| g.to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    )?;
                }
                write!(f, "(")?;
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

impl<'ast, T: fmt::Debug> fmt::Debug for TypedExpressionList<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedExpressionList::FunctionCall(ref i, ref g, ref p, _) => {
                write!(f, "FunctionCall({:?}, {:?}, (", g, i)?;
                f.debug_list().entries(p.iter()).finish()?;
                write!(f, ")")
            }
            TypedExpressionList::EmbedCall(ref embed, ref g, ref p, _) => {
                write!(f, "EmbedCall({:?}, {:?}, (", g, embed)?;
                f.debug_list().entries(p.iter()).finish()?;
                write!(f, ")")
            }
        }
    }
}

// Variable to TypedExpression conversion

impl<'ast, T: Field> From<Variable<'ast, T>> for TypedExpression<'ast, T> {
    fn from(v: Variable<'ast, T>) -> Self {
        match v.get_type() {
            Type::FieldElement => FieldElementExpression::Identifier(v.id).into(),
            Type::Boolean => BooleanExpression::Identifier(v.id).into(),
            Type::Array(ty) => ArrayExpressionInner::Identifier(v.id)
                .annotate(*ty.ty, ty.size)
                .into(),
            Type::Struct(ty) => StructExpressionInner::Identifier(v.id).annotate(ty).into(),
            Type::Uint(w) => UExpressionInner::Identifier(v.id).annotate(w).into(),
            Type::Int => unreachable!(),
        }
    }
}

// Common behaviour across expressions

pub trait IfElse<'ast, T> {
    fn if_else(condition: BooleanExpression<'ast, T>, consequence: Self, alternative: Self)
        -> Self;
}

impl<'ast, T> IfElse<'ast, T> for FieldElementExpression<'ast, T> {
    fn if_else(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
    ) -> Self {
        FieldElementExpression::IfElse(box condition, box consequence, box alternative)
    }
}

impl<'ast, T> IfElse<'ast, T> for IntExpression<'ast, T> {
    fn if_else(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
    ) -> Self {
        IntExpression::IfElse(box condition, box consequence, box alternative)
    }
}

impl<'ast, T> IfElse<'ast, T> for BooleanExpression<'ast, T> {
    fn if_else(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
    ) -> Self {
        BooleanExpression::IfElse(box condition, box consequence, box alternative)
    }
}

impl<'ast, T> IfElse<'ast, T> for UExpression<'ast, T> {
    fn if_else(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
    ) -> Self {
        let bitwidth = consequence.bitwidth;

        UExpressionInner::IfElse(box condition, box consequence, box alternative).annotate(bitwidth)
    }
}

impl<'ast, T: Clone> IfElse<'ast, T> for ArrayExpression<'ast, T> {
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

impl<'ast, T: Clone> IfElse<'ast, T> for StructExpression<'ast, T> {
    fn if_else(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
    ) -> Self {
        let ty = consequence.ty().clone();
        StructExpressionInner::IfElse(box condition, box consequence, box alternative).annotate(ty)
    }
}

pub trait Select<'ast, T> {
    fn select<I: Into<UExpression<'ast, T>>>(array: ArrayExpression<'ast, T>, index: I) -> Self;
}

impl<'ast, T> Select<'ast, T> for FieldElementExpression<'ast, T> {
    fn select<I: Into<UExpression<'ast, T>>>(array: ArrayExpression<'ast, T>, index: I) -> Self {
        FieldElementExpression::Select(box array, box index.into())
    }
}

impl<'ast, T> Select<'ast, T> for IntExpression<'ast, T> {
    fn select<I: Into<UExpression<'ast, T>>>(array: ArrayExpression<'ast, T>, index: I) -> Self {
        IntExpression::Select(box array, box index.into())
    }
}

impl<'ast, T> Select<'ast, T> for BooleanExpression<'ast, T> {
    fn select<I: Into<UExpression<'ast, T>>>(array: ArrayExpression<'ast, T>, index: I) -> Self {
        BooleanExpression::Select(box array, box index.into())
    }
}

impl<'ast, T: Clone> Select<'ast, T> for TypedExpression<'ast, T> {
    fn select<I: Into<UExpression<'ast, T>>>(array: ArrayExpression<'ast, T>, index: I) -> Self {
        match *array.get_array_type().ty {
            Type::Array(..) => ArrayExpression::select(array, index).into(),
            Type::Struct(..) => StructExpression::select(array, index).into(),
            Type::FieldElement => FieldElementExpression::select(array, index).into(),
            Type::Boolean => BooleanExpression::select(array, index).into(),
            Type::Int => IntExpression::select(array, index).into(),
            Type::Uint(..) => UExpression::select(array, index).into(),
        }
    }
}

impl<'ast, T: Clone> Select<'ast, T> for UExpression<'ast, T> {
    fn select<I: Into<UExpression<'ast, T>>>(array: ArrayExpression<'ast, T>, index: I) -> Self {
        let bitwidth = match array.inner_type().clone() {
            Type::Uint(bitwidth) => bitwidth,
            _ => unreachable!(),
        };

        UExpressionInner::Select(box array, box index.into()).annotate(bitwidth)
    }
}

impl<'ast, T: Clone> Select<'ast, T> for ArrayExpression<'ast, T> {
    fn select<I: Into<UExpression<'ast, T>>>(array: ArrayExpression<'ast, T>, index: I) -> Self {
        let (ty, size) = match array.inner_type() {
            Type::Array(array_type) => (array_type.ty.clone(), array_type.size.clone()),
            _ => unreachable!(),
        };

        ArrayExpressionInner::Select(box array, box index.into()).annotate(*ty, size)
    }
}

impl<'ast, T: Clone> Select<'ast, T> for StructExpression<'ast, T> {
    fn select<I: Into<UExpression<'ast, T>>>(array: ArrayExpression<'ast, T>, index: I) -> Self {
        let members = match array.inner_type().clone() {
            Type::Struct(members) => members,
            _ => unreachable!(),
        };

        StructExpressionInner::Select(box array, box index.into()).annotate(members)
    }
}

pub trait Member<'ast, T> {
    fn member(s: StructExpression<'ast, T>, member_id: MemberId) -> Self;
}

impl<'ast, T> Member<'ast, T> for FieldElementExpression<'ast, T> {
    fn member(s: StructExpression<'ast, T>, member_id: MemberId) -> Self {
        FieldElementExpression::Member(box s, member_id)
    }
}

impl<'ast, T> Member<'ast, T> for BooleanExpression<'ast, T> {
    fn member(s: StructExpression<'ast, T>, member_id: MemberId) -> Self {
        BooleanExpression::Member(box s, member_id)
    }
}

impl<'ast, T: Clone> Member<'ast, T> for UExpression<'ast, T> {
    fn member(s: StructExpression<'ast, T>, member_id: MemberId) -> Self {
        let members = s.ty().clone();

        let ty = members
            .iter()
            .find(|member| *member.id == member_id)
            .unwrap()
            .ty
            .clone();

        let bitwidth = match *ty {
            Type::Uint(bitwidth) => bitwidth,
            _ => unreachable!(),
        };

        UExpressionInner::Member(box s, member_id).annotate(bitwidth)
    }
}

impl<'ast, T: Clone> Member<'ast, T> for ArrayExpression<'ast, T> {
    fn member(s: StructExpression<'ast, T>, member_id: MemberId) -> Self {
        let members = s.ty().clone();

        let ty = members
            .iter()
            .find(|member| *member.id == member_id)
            .unwrap()
            .ty
            .clone();

        let (ty, size) = match *ty {
            Type::Array(array_type) => (array_type.ty, array_type.size),
            _ => unreachable!(),
        };

        ArrayExpressionInner::Member(box s, member_id).annotate(*ty, size)
    }
}

impl<'ast, T: Clone> Member<'ast, T> for StructExpression<'ast, T> {
    fn member(s: StructExpression<'ast, T>, member_id: MemberId) -> Self {
        let members = s.ty().clone();

        let ty = members
            .iter()
            .find(|member| *member.id == member_id)
            .unwrap()
            .ty
            .clone();

        let members = match *ty {
            Type::Struct(members) => members,
            _ => unreachable!(),
        };

        StructExpressionInner::Member(box s, member_id).annotate(members)
    }
}

pub trait FunctionCall<'ast, T> {
    fn function_call(
        key: DeclarationFunctionKey<'ast>,
        generics: Vec<Option<UExpression<'ast, T>>>,
        arguments: Vec<TypedExpression<'ast, T>>,
        output_type: Type<'ast, T>,
    ) -> Self;
}

impl<'ast, T: Field> FunctionCall<'ast, T> for FieldElementExpression<'ast, T> {
    fn function_call(
        key: DeclarationFunctionKey<'ast>,
        generics: Vec<Option<UExpression<'ast, T>>>,
        arguments: Vec<TypedExpression<'ast, T>>,
        output_type: Type<'ast, T>,
    ) -> Self {
        assert_eq!(output_type, Type::FieldElement);
        FieldElementExpression::FunctionCall(key, generics, arguments)
    }
}

impl<'ast, T: Field> FunctionCall<'ast, T> for BooleanExpression<'ast, T> {
    fn function_call(
        key: DeclarationFunctionKey<'ast>,
        generics: Vec<Option<UExpression<'ast, T>>>,
        arguments: Vec<TypedExpression<'ast, T>>,
        output_type: Type<'ast, T>,
    ) -> Self {
        assert_eq!(output_type, Type::Boolean);
        BooleanExpression::FunctionCall(key, generics, arguments)
    }
}

impl<'ast, T: Field> FunctionCall<'ast, T> for UExpression<'ast, T> {
    fn function_call(
        key: DeclarationFunctionKey<'ast>,
        generics: Vec<Option<UExpression<'ast, T>>>,
        arguments: Vec<TypedExpression<'ast, T>>,
        output_type: Type<'ast, T>,
    ) -> Self {
        let bitwidth = match output_type {
            Type::Uint(bitwidth) => bitwidth,
            _ => unreachable!(),
        };
        UExpressionInner::FunctionCall(key, generics, arguments).annotate(bitwidth)
    }
}

impl<'ast, T: Field> FunctionCall<'ast, T> for ArrayExpression<'ast, T> {
    fn function_call(
        key: DeclarationFunctionKey<'ast>,
        generics: Vec<Option<UExpression<'ast, T>>>,
        arguments: Vec<TypedExpression<'ast, T>>,
        output_type: Type<'ast, T>,
    ) -> Self {
        let array_ty = match output_type {
            Type::Array(array_ty) => array_ty,
            _ => unreachable!(),
        };
        ArrayExpressionInner::FunctionCall(key, generics, arguments)
            .annotate(*array_ty.ty, array_ty.size)
    }
}

impl<'ast, T: Field> FunctionCall<'ast, T> for StructExpression<'ast, T> {
    fn function_call(
        key: DeclarationFunctionKey<'ast>,
        generics: Vec<Option<UExpression<'ast, T>>>,
        arguments: Vec<TypedExpression<'ast, T>>,
        output_type: Type<'ast, T>,
    ) -> Self {
        let struct_ty = match output_type {
            Type::Struct(struct_ty) => struct_ty,
            _ => unreachable!(),
        };

        StructExpressionInner::FunctionCall(key, generics, arguments).annotate(struct_ty)
    }
}
