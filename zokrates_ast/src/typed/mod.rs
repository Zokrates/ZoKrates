//! Module containing structs and enums to represent a program.
//!
//! @file absy.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

pub mod abi;
pub mod byref;
pub mod folder;
pub mod identifier;
pub mod owned;
pub mod result_folder;

mod integer;
mod parameter;
pub mod types;
mod uint;
pub mod utils;
pub mod variable;

use self::identifier::IdTrait;
pub use self::identifier::{CoreIdentifier, ShadowedIdentifier, SourceIdentifier};
pub use self::parameter::{DeclarationParameter, GParameter};
pub use self::types::{
    CanonicalConstantIdentifier, ConcreteFunctionKey, ConcreteSignature, ConcreteTupleType,
    ConcreteType, ConstantIdentifier, DeclarationArrayType, DeclarationConstant,
    DeclarationFunctionKey, DeclarationSignature, DeclarationStructType, DeclarationType,
    GArrayType, GStructType, GType, GenericIdentifier, Signature, StructType, TupleType, Type,
    UBitwidth,
};
use self::types::{ConcreteArrayType, ConcreteStructType};

use crate::typed::types::{ConcreteGenericsAssignment, IntoType};
use crate::untyped::Position;

pub use self::variable::{ConcreteVariable, DeclarationVariable, GVariable, Variable};
use std::marker::PhantomData;
use std::path::{Path, PathBuf};

pub use crate::typed::integer::IntExpression;
pub use crate::typed::uint::{bitwidth, UExpression, UExpressionInner, UMetadata};

use crate::common::{FlatEmbed, FormatString};

use std::collections::BTreeMap;
use std::convert::{TryFrom, TryInto};
use std::fmt;

pub use crate::typed::types::{ArrayType, FunctionKey, MemberId};

use zokrates_field::Field;

pub use self::folder::Folder;
use crate::typed::abi::{Abi, AbiInput};
use std::ops::{Add, Div, Mul, Sub};

pub use self::identifier::Identifier;

/// An identifier for a `TypedModule`. Typically a path or uri.
pub type OwnedTypedModuleId = PathBuf;
pub type TypedModuleId = Path;

/// A collection of `TypedModule`s
pub type TypedModules<I, T> = BTreeMap<OwnedTypedModuleId, TypedModule<I, T>>;

/// A collection of `TypedFunctionSymbol`s
/// # Remarks
/// * It is the role of the semantic checker to make sure there are no duplicates for a given `FunctionKey`
///   in a given `TypedModule`, hence the use of a BTreeMap
pub type TypedFunctionSymbols<I, T> =
    BTreeMap<DeclarationFunctionKey<I, T>, TypedFunctionSymbol<I, T>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypedConstantSymbol<I, T> {
    Here(TypedConstant<I, T>),
    There(CanonicalConstantIdentifier<I>),
}

/// A collection of `TypedConstantSymbol`s
/// It is still ordered, as we inline the constants in the order they are declared
pub type TypedConstantSymbols<I, T> =
    Vec<(CanonicalConstantIdentifier<I>, TypedConstantSymbol<I, T>)>;

/// A typed program as a collection of modules, one of them being the main
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct TypedProgram<I, T> {
    pub modules: TypedModules<I, T>,
    pub main: OwnedTypedModuleId,
}

impl<I: IdTrait, T: Field> TypedProgram<I, T> {
    pub fn abi(&self) -> Abi {
        let main = &self.modules[&self.main]
            .functions_iter()
            .find(|s| s.key.id == "main")
            .unwrap()
            .symbol;
        let main = match main {
            TypedFunctionSymbol::Here(main) => main,
            _ => unreachable!(),
        };

        Abi {
            inputs: main
                .arguments
                .iter()
                .map(|p| {
                    types::ConcreteType::try_from(
                        crate::typed::types::try_from_g_type::<
                            DeclarationConstant<I, T>,
                            UExpression<I, T>,
                        >(p.id._type.clone())
                        .unwrap(),
                    )
                    .map(|ty| AbiInput {
                        public: !p.private,
                        name: p.id.id.to_string(),
                        ty,
                    })
                    .unwrap()
                })
                .collect(),
            output: types::ConcreteType::try_from(
                types::try_from_g_type::<DeclarationConstant<I, T>, UExpression<I, T>>(
                    *main.signature.output.clone(),
                )
                .unwrap(),
            )
            .unwrap(),
        }
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for TypedProgram<I, T> {
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

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct TypedFunctionSymbolDeclaration<I, T> {
    pub key: DeclarationFunctionKey<I, T>,
    pub symbol: TypedFunctionSymbol<I, T>,
}

impl<I, T> TypedFunctionSymbolDeclaration<I, T> {
    pub fn new(key: DeclarationFunctionKey<I, T>, symbol: TypedFunctionSymbol<I, T>) -> Self {
        TypedFunctionSymbolDeclaration { key, symbol }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct TypedConstantSymbolDeclaration<I, T> {
    pub id: CanonicalConstantIdentifier<I>,
    pub symbol: TypedConstantSymbol<I, T>,
}

impl<I, T> TypedConstantSymbolDeclaration<I, T> {
    pub fn new(id: CanonicalConstantIdentifier<I>, symbol: TypedConstantSymbol<I, T>) -> Self {
        TypedConstantSymbolDeclaration { id, symbol }
    }
}

#[allow(clippy::large_enum_variant)]
#[derive(PartialEq, Eq, Debug, Clone)]
pub enum TypedSymbolDeclaration<I, T> {
    Function(TypedFunctionSymbolDeclaration<I, T>),
    Constant(TypedConstantSymbolDeclaration<I, T>),
}

impl<I, T> From<TypedFunctionSymbolDeclaration<I, T>> for TypedSymbolDeclaration<I, T> {
    fn from(d: TypedFunctionSymbolDeclaration<I, T>) -> Self {
        Self::Function(d)
    }
}

impl<I, T> From<TypedConstantSymbolDeclaration<I, T>> for TypedSymbolDeclaration<I, T> {
    fn from(d: TypedConstantSymbolDeclaration<I, T>) -> Self {
        Self::Constant(d)
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for TypedSymbolDeclaration<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TypedSymbolDeclaration::Function(fun) => write!(f, "{}", fun),
            TypedSymbolDeclaration::Constant(c) => write!(f, "{}", c),
        }
    }
}

pub type TypedSymbolDeclarations<I, T> = Vec<TypedSymbolDeclaration<I, T>>;

/// A typed module as a collection of functions. Types have been resolved during semantic checking.
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct TypedModule<I, T> {
    pub symbols: TypedSymbolDeclarations<I, T>,
}

impl<I, T> TypedModule<I, T> {
    pub fn functions_iter(&self) -> impl Iterator<Item = &TypedFunctionSymbolDeclaration<I, T>> {
        self.symbols.iter().filter_map(|s| match s {
            TypedSymbolDeclaration::Function(d) => Some(d),
            _ => None,
        })
    }

    pub fn into_functions_iter(self) -> impl Iterator<Item = TypedFunctionSymbolDeclaration<I, T>> {
        self.symbols.into_iter().filter_map(|s| match s {
            TypedSymbolDeclaration::Function(d) => Some(d),
            _ => None,
        })
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TypedFunctionSymbol<I, T> {
    Here(TypedFunction<I, T>),
    There(DeclarationFunctionKey<I, T>),
    Flat(FlatEmbed),
}

impl<'ast, T: Field> TypedFunctionSymbol<&'ast str, T> {
    pub fn signature<'a>(
        &'a self,
        modules: &'a TypedModules<&'ast str, T>,
    ) -> DeclarationSignature<&'ast str, T> {
        match self {
            TypedFunctionSymbol::Here(f) => f.signature.clone(),
            TypedFunctionSymbol::There(key) => modules
                .get(&key.module)
                .unwrap()
                .functions_iter()
                .find(|d| d.key == *key)
                .unwrap()
                .symbol
                .signature(modules),
            TypedFunctionSymbol::Flat(flat_fun) => flat_fun.typed_signature(),
        }
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for TypedConstantSymbolDeclaration<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.symbol {
            TypedConstantSymbol::Here(ref tc) => {
                write!(f, "const {} {} = {};", tc.ty, self.id, tc.expression)
            }
            TypedConstantSymbol::There(ref imported_id) => {
                write!(
                    f,
                    "from \"{}\" import {} as {};",
                    imported_id.module.display(),
                    imported_id.id,
                    self.id
                )
            }
        }
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for TypedFunctionSymbolDeclaration<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.symbol {
            TypedFunctionSymbol::Here(ref function) => write!(f, "def {}{}", self.key.id, function),
            TypedFunctionSymbol::There(ref fun_key) => write!(
                f,
                "from \"{}\" import {} as {}; // with signature {}",
                fun_key.module.display(),
                fun_key.id,
                self.key.id,
                self.key.signature
            ),
            TypedFunctionSymbol::Flat(ref flat_fun) => {
                write!(
                    f,
                    "def {}{} {{\n\t// hidden\n}}",
                    self.key.id,
                    flat_fun.typed_signature::<T>()
                )
            }
        }
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for TypedModule<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let res = self
            .symbols
            .iter()
            .map(|s| format!("{}", s))
            .collect::<Vec<_>>();

        write!(f, "{}", res.join("\n"))
    }
}

/// A typed function
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct TypedFunction<I, T> {
    /// Arguments of the function
    pub arguments: Vec<DeclarationParameter<I, T>>,
    /// Vector of statements that are executed when running the function
    pub statements: Vec<TypedStatement<I, T>>,
    /// function signature
    pub signature: DeclarationSignature<I, T>,
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for TypedFunction<I, T> {
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

        write!(f, " -> {} {{", self.signature.output)?;

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

        writeln!(f, "}}")?;

        Ok(())
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TypedConstant<I, T> {
    pub expression: TypedExpression<I, T>,
    pub ty: DeclarationType<I, T>,
}

impl<I, T> TypedConstant<I, T> {
    pub fn new(expression: TypedExpression<I, T>, ty: DeclarationType<I, T>) -> Self {
        TypedConstant { expression, ty }
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for TypedConstant<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.expression)
    }
}

impl<I: IdTrait, T: Field> Typed<I, T> for TypedConstant<I, T> {
    fn get_type(&self) -> Type<I, T> {
        self.expression.get_type()
    }
}

/// Something we can assign to.
#[allow(clippy::large_enum_variant)]
#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub enum TypedAssignee<I, T> {
    Identifier(Variable<I, T>),
    Select(Box<TypedAssignee<I, T>>, Box<UExpression<I, T>>),
    Member(Box<TypedAssignee<I, T>>, MemberId),
    Element(Box<TypedAssignee<I, T>>, u32),
}

#[derive(Clone, PartialEq, Hash, Eq, Debug, PartialOrd, Ord)]
pub struct TypedSpread<I, T> {
    pub array: ArrayExpression<I, T>,
}

impl<I, T> From<ArrayExpression<I, T>> for TypedSpread<I, T> {
    fn from(array: ArrayExpression<I, T>) -> TypedSpread<I, T> {
        TypedSpread { array }
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for TypedSpread<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "...{}", self.array)
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub enum TypedExpressionOrSpread<I, T> {
    Expression(TypedExpression<I, T>),
    Spread(TypedSpread<I, T>),
}

impl<I: Clone, T: Clone> TypedExpressionOrSpread<I, T> {
    pub fn size(&self) -> UExpression<I, T> {
        match self {
            TypedExpressionOrSpread::Expression(..) => 1u32.into(),
            TypedExpressionOrSpread::Spread(s) => s.array.size(),
        }
    }
}

impl<I, T> From<TypedExpressionOrSpread<I, T>> for TypedExpression<I, T> {
    fn from(e: TypedExpressionOrSpread<I, T>) -> TypedExpression<I, T> {
        if let TypedExpressionOrSpread::Expression(e) = e {
            e
        } else {
            unreachable!("downcast failed")
        }
    }
}

impl<I, T> From<IntExpression<I, T>> for TypedExpressionOrSpread<I, T> {
    fn from(e: IntExpression<I, T>) -> Self {
        TypedExpressionOrSpread::Expression(e.into())
    }
}

impl<I, T> From<FieldElementExpression<I, T>> for TypedExpressionOrSpread<I, T> {
    fn from(e: FieldElementExpression<I, T>) -> Self {
        TypedExpressionOrSpread::Expression(e.into())
    }
}

impl<I, T> From<BooleanExpression<I, T>> for TypedExpressionOrSpread<I, T> {
    fn from(e: BooleanExpression<I, T>) -> Self {
        TypedExpressionOrSpread::Expression(e.into())
    }
}

impl<I, T> From<UExpression<I, T>> for TypedExpressionOrSpread<I, T> {
    fn from(e: UExpression<I, T>) -> Self {
        TypedExpressionOrSpread::Expression(e.into())
    }
}

impl<I, T> From<ArrayExpression<I, T>> for TypedExpressionOrSpread<I, T> {
    fn from(e: ArrayExpression<I, T>) -> Self {
        TypedExpressionOrSpread::Expression(e.into())
    }
}

impl<I, T> From<StructExpression<I, T>> for TypedExpressionOrSpread<I, T> {
    fn from(e: StructExpression<I, T>) -> Self {
        TypedExpressionOrSpread::Expression(e.into())
    }
}

impl<I, T> From<TupleExpression<I, T>> for TypedExpressionOrSpread<I, T> {
    fn from(e: TupleExpression<I, T>) -> Self {
        TypedExpressionOrSpread::Expression(e.into())
    }
}

impl<I, T> From<TypedExpression<I, T>> for TypedExpressionOrSpread<I, T> {
    fn from(e: TypedExpression<I, T>) -> Self {
        TypedExpressionOrSpread::Expression(e)
    }
}

impl<I: Clone, T: Clone> TypedExpressionOrSpread<I, T> {
    pub fn get_type(&self) -> (Type<I, T>, UExpression<I, T>) {
        match self {
            TypedExpressionOrSpread::Expression(e) => (e.get_type(), 1u32.into()),
            TypedExpressionOrSpread::Spread(s) => (s.array.inner_type().clone(), s.array.size()),
        }
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for TypedExpressionOrSpread<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TypedExpressionOrSpread::Expression(e) => write!(f, "{}", e),
            TypedExpressionOrSpread::Spread(s) => write!(f, "{}", s),
        }
    }
}

impl<I, T> From<Variable<I, T>> for TypedAssignee<I, T> {
    fn from(v: Variable<I, T>) -> Self {
        TypedAssignee::Identifier(v)
    }
}

impl<I: Clone, T: Clone> Typed<I, T> for TypedAssignee<I, T> {
    fn get_type(&self) -> Type<I, T> {
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
            TypedAssignee::Element(ref s, index) => {
                let s_type = s.get_type();
                match s_type {
                    Type::Tuple(tuple_ty) => tuple_ty.elements[index as usize].clone(),
                    _ => unreachable!("a tuple access should only be defined over tuples"),
                }
            }
        }
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for TypedAssignee<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedAssignee::Identifier(ref s) => write!(f, "{}", s.id),
            TypedAssignee::Select(ref a, ref e) => write!(f, "{}[{}]", a, e),
            TypedAssignee::Member(ref s, ref m) => write!(f, "{}.{}", s, m),
            TypedAssignee::Element(ref s, index) => write!(f, "{}.{}", s, index),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Hash, Eq, Default, PartialOrd, Ord)]
pub struct AssertionMetadata {
    pub file: String,
    pub position: Position,
    pub message: Option<String>,
}

impl fmt::Display for AssertionMetadata {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Assertion failed at {}:{}", self.file, self.position)?;
        match &self.message {
            Some(m) => write!(f, ": \"{}\"", m),
            None => write!(f, ""),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub enum RuntimeError {
    SourceAssertion(AssertionMetadata),
    SelectRangeCheck,
    DivisionByZero,
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeError::SourceAssertion(metadata) => write!(f, "{}", metadata),
            RuntimeError::SelectRangeCheck => write!(f, "Range check on array access"),
            RuntimeError::DivisionByZero => write!(f, "Division by zero"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub struct EmbedCall<I, T> {
    pub embed: FlatEmbed,
    pub generics: Vec<u32>,
    pub arguments: Vec<TypedExpression<I, T>>,
}

impl<I, T> EmbedCall<I, T> {
    pub fn new(
        embed: FlatEmbed,
        generics: Vec<u32>,
        arguments: Vec<TypedExpression<I, T>>,
    ) -> Self {
        Self {
            embed,
            generics,
            arguments,
        }
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for EmbedCall<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.embed.id())?;
        if !self.generics.is_empty() {
            write!(
                f,
                "::<{}>",
                self.generics
                    .iter()
                    .map(|g| g.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )?;
        }
        write!(f, "(")?;
        let len = self.arguments.len();
        for (i, arg) in self.arguments.iter().enumerate() {
            write!(f, "{}", arg)?;
            if i < len - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, ")")
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub enum DefinitionRhs<I, T> {
    Expression(TypedExpression<I, T>),
    EmbedCall(EmbedCall<I, T>),
}

impl<I, T> From<TypedExpression<I, T>> for DefinitionRhs<I, T> {
    fn from(e: TypedExpression<I, T>) -> Self {
        Self::Expression(e)
    }
}

impl<I, T> From<EmbedCall<I, T>> for DefinitionRhs<I, T> {
    fn from(c: EmbedCall<I, T>) -> Self {
        Self::EmbedCall(c)
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for DefinitionRhs<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            DefinitionRhs::EmbedCall(c) => write!(f, "{}", c),
            DefinitionRhs::Expression(e) => write!(f, "{}", e),
        }
    }
}

/// A statement in a `TypedFunction`
#[allow(clippy::large_enum_variant)]
#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub enum TypedStatement<I, T> {
    Return(TypedExpression<I, T>),
    Definition(TypedAssignee<I, T>, DefinitionRhs<I, T>),
    Assertion(BooleanExpression<I, T>, RuntimeError),
    For(
        Variable<I, T>,
        UExpression<I, T>,
        UExpression<I, T>,
        Vec<TypedStatement<I, T>>,
    ),
    Log(FormatString, Vec<TypedExpression<I, T>>),
    // Aux
    PushCallLog(DeclarationFunctionKey<I, T>, ConcreteGenericsAssignment<I>),
    PopCallLog,
}

impl<I, T> TypedStatement<I, T> {
    pub fn definition(a: TypedAssignee<I, T>, e: TypedExpression<I, T>) -> Self {
        Self::Definition(a, e.into())
    }

    pub fn embed_call_definition(a: TypedAssignee<I, T>, c: EmbedCall<I, T>) -> Self {
        Self::Definition(a, c.into())
    }
}

impl<I: fmt::Display, T: fmt::Display> TypedStatement<I, T> {
    fn fmt_indented(&self, f: &mut fmt::Formatter, depth: usize) -> fmt::Result {
        match self {
            TypedStatement::For(variable, from, to, statements) => {
                write!(f, "{}", "\t".repeat(depth))?;
                writeln!(f, "for {} in {}..{} {{", variable, from, to)?;
                for s in statements {
                    s.fmt_indented(f, depth + 1)?;
                    writeln!(f)?;
                }
                write!(f, "{}}}", "\t".repeat(depth))
            }
            s => write!(f, "{}{}", "\t".repeat(depth), s),
        }
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for TypedStatement<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedStatement::Return(ref e) => {
                write!(f, "return {};", e)
            }
            TypedStatement::Definition(ref lhs, ref rhs) => write!(f, "{} = {};", lhs, rhs),
            TypedStatement::Assertion(ref e, ref error) => {
                write!(f, "assert({}", e)?;
                match error {
                    RuntimeError::SourceAssertion(metadata) => match &metadata.message {
                        Some(m) => write!(f, ", \"{}\");", m),
                        None => write!(f, ");"),
                    },
                    error => write!(f, "); // {}", error),
                }
            }
            TypedStatement::For(ref var, ref start, ref stop, ref list) => {
                writeln!(f, "for {} in {}..{} {{", var, start, stop)?;
                for l in list {
                    writeln!(f, "\t\t{}", l)?;
                }
                write!(f, "\t}}")
            }
            TypedStatement::Log(ref l, ref expressions) => write!(
                f,
                "log({}, {})",
                l,
                expressions
                    .iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
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

pub trait Typed<I, T> {
    fn get_type(&self) -> Type<I, T>;
}

/// A typed expression
#[allow(clippy::large_enum_variant)]
#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub enum TypedExpression<I, T> {
    Boolean(BooleanExpression<I, T>),
    FieldElement(FieldElementExpression<I, T>),
    Uint(UExpression<I, T>),
    Array(ArrayExpression<I, T>),
    Struct(StructExpression<I, T>),
    Tuple(TupleExpression<I, T>),
    Int(IntExpression<I, T>),
}

impl<I, T> TypedExpression<I, T> {
    pub fn empty_tuple() -> TypedExpression<I, T> {
        TypedExpression::Tuple(TupleExpressionInner::Value(vec![]).annotate(TupleType::new(vec![])))
    }
}

impl<I, T> From<BooleanExpression<I, T>> for TypedExpression<I, T> {
    fn from(e: BooleanExpression<I, T>) -> TypedExpression<I, T> {
        TypedExpression::Boolean(e)
    }
}

impl<I, T> From<FieldElementExpression<I, T>> for TypedExpression<I, T> {
    fn from(e: FieldElementExpression<I, T>) -> TypedExpression<I, T> {
        TypedExpression::FieldElement(e)
    }
}

impl<I, T> From<IntExpression<I, T>> for TypedExpression<I, T> {
    fn from(e: IntExpression<I, T>) -> TypedExpression<I, T> {
        TypedExpression::Int(e)
    }
}

impl<I, T> From<UExpression<I, T>> for TypedExpression<I, T> {
    fn from(e: UExpression<I, T>) -> TypedExpression<I, T> {
        TypedExpression::Uint(e)
    }
}

impl<I, T> From<ArrayExpression<I, T>> for TypedExpression<I, T> {
    fn from(e: ArrayExpression<I, T>) -> TypedExpression<I, T> {
        TypedExpression::Array(e)
    }
}

impl<I, T> From<TupleExpression<I, T>> for TypedExpression<I, T> {
    fn from(e: TupleExpression<I, T>) -> TypedExpression<I, T> {
        TypedExpression::Tuple(e)
    }
}

impl<I, T> From<StructExpression<I, T>> for TypedExpression<I, T> {
    fn from(e: StructExpression<I, T>) -> TypedExpression<I, T> {
        TypedExpression::Struct(e)
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for TypedExpression<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedExpression::Boolean(ref e) => write!(f, "{}", e),
            TypedExpression::FieldElement(ref e) => write!(f, "{}", e),
            TypedExpression::Uint(ref e) => write!(f, "{}", e),
            TypedExpression::Array(ref e) => write!(f, "{}", e),
            TypedExpression::Struct(ref s) => write!(f, "{}", s),
            TypedExpression::Tuple(ref t) => write!(f, "{}", t),
            TypedExpression::Int(ref s) => write!(f, "{}", s),
        }
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for ArrayExpression<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.inner)
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for StructExpression<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.inner {
            StructExpressionInner::Block(ref block) => write!(f, "{}", block),
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
            StructExpressionInner::FunctionCall(ref function_call) => {
                write!(f, "{}", function_call)
            }
            StructExpressionInner::Conditional(ref c) => write!(f, "{}", c),
            StructExpressionInner::Member(ref m) => write!(f, "{}", m),
            StructExpressionInner::Select(ref select) => write!(f, "{}", select),
            StructExpressionInner::Element(ref element) => write!(f, "{}", element),
        }
    }
}

impl<I: Clone, T: Clone> Typed<I, T> for TypedExpression<I, T> {
    fn get_type(&self) -> Type<I, T> {
        match *self {
            TypedExpression::Boolean(ref e) => e.get_type(),
            TypedExpression::FieldElement(ref e) => e.get_type(),
            TypedExpression::Array(ref e) => e.get_type(),
            TypedExpression::Uint(ref e) => e.get_type(),
            TypedExpression::Struct(ref s) => s.get_type(),
            TypedExpression::Tuple(ref s) => s.get_type(),
            TypedExpression::Int(_) => Type::Int,
        }
    }
}

impl<I: Clone, T: Clone> Typed<I, T> for ArrayExpression<I, T> {
    fn get_type(&self) -> Type<I, T> {
        Type::array(*self.ty.clone())
    }
}

impl<I: Clone, T: Clone> Typed<I, T> for TupleExpression<I, T> {
    fn get_type(&self) -> Type<I, T> {
        Type::tuple(self.ty.clone())
    }
}

impl<I: Clone, T: Clone> Typed<I, T> for StructExpression<I, T> {
    fn get_type(&self) -> Type<I, T> {
        Type::Struct(self.ty.clone())
    }
}

impl<I: Clone, T: Clone> Typed<I, T> for FieldElementExpression<I, T> {
    fn get_type(&self) -> Type<I, T> {
        Type::FieldElement
    }
}

impl<I: Clone, T: Clone> Typed<I, T> for UExpression<I, T> {
    fn get_type(&self) -> Type<I, T> {
        Type::Uint(self.bitwidth)
    }
}

impl<I: Clone, T: Clone> Typed<I, T> for BooleanExpression<I, T> {
    fn get_type(&self) -> Type<I, T> {
        Type::Boolean
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct EqExpression<E> {
    pub left: Box<E>,
    pub right: Box<E>,
}

impl<E> EqExpression<E> {
    pub fn new(left: E, right: E) -> Self {
        EqExpression {
            left: box left,
            right: box right,
        }
    }
}

impl<E: fmt::Display> fmt::Display for EqExpression<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({} == {})", self.left, self.right)
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct BlockExpression<I, T, E> {
    pub statements: Vec<TypedStatement<I, T>>,
    pub value: Box<E>,
}

impl<I, T, E> BlockExpression<I, T, E> {
    pub fn new(statements: Vec<TypedStatement<I, T>>, value: E) -> Self {
        BlockExpression {
            statements,
            value: box value,
        }
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct IdentifierExpression<I, E> {
    pub id: Identifier<I>,
    ty: PhantomData<E>,
}

impl<I, E> IdentifierExpression<I, E> {
    pub fn new(id: Identifier<I>) -> Self {
        IdentifierExpression {
            id,
            ty: PhantomData,
        }
    }
}

impl<I: fmt::Display, E> fmt::Display for IdentifierExpression<I, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.id)
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct MemberExpression<I, T, E> {
    pub struc: Box<StructExpression<I, T>>,
    pub id: MemberId,
    ty: PhantomData<E>,
}

impl<I, T, E> MemberExpression<I, T, E> {
    pub fn new(struc: StructExpression<I, T>, id: MemberId) -> Self {
        MemberExpression {
            struc: box struc,
            id,
            ty: PhantomData,
        }
    }
}

impl<I: fmt::Display, T: fmt::Display, E> fmt::Display for MemberExpression<I, T, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}.{}", self.struc, self.id)
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct SelectExpression<I, T, E> {
    pub array: Box<ArrayExpression<I, T>>,
    pub index: Box<UExpression<I, T>>,
    ty: PhantomData<E>,
}

impl<I, T, E> SelectExpression<I, T, E> {
    pub fn new(array: ArrayExpression<I, T>, index: UExpression<I, T>) -> Self {
        SelectExpression {
            array: box array,
            index: box index,
            ty: PhantomData,
        }
    }
}

impl<I: fmt::Display, T: fmt::Display, E> fmt::Display for SelectExpression<I, T, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}[{}]", self.array, self.index)
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct ElementExpression<I, T, E> {
    pub tuple: Box<TupleExpression<I, T>>,
    pub index: u32,
    ty: PhantomData<E>,
}

impl<I, T, E> ElementExpression<I, T, E> {
    pub fn new(tuple: TupleExpression<I, T>, index: u32) -> Self {
        ElementExpression {
            tuple: box tuple,
            index,
            ty: PhantomData,
        }
    }
}

impl<I: fmt::Display, T: fmt::Display, E> fmt::Display for ElementExpression<I, T, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}.{}", self.tuple, self.index)
    }
}

#[derive(Debug, Clone, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub enum ConditionalKind {
    IfElse,
    Ternary,
}

#[derive(Debug, Clone, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub struct ConditionalExpression<I, T, E> {
    pub condition: Box<BooleanExpression<I, T>>,
    pub consequence: Box<E>,
    pub alternative: Box<E>,
    pub kind: ConditionalKind,
}

impl<I, T, E> ConditionalExpression<I, T, E> {
    pub fn new(
        condition: BooleanExpression<I, T>,
        consequence: E,
        alternative: E,
        kind: ConditionalKind,
    ) -> Self {
        ConditionalExpression {
            condition: box condition,
            consequence: box consequence,
            alternative: box alternative,
            kind,
        }
    }
}

impl<I: fmt::Display, T: fmt::Display, E: fmt::Display> fmt::Display
    for ConditionalExpression<I, T, E>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.kind {
            ConditionalKind::IfElse => {
                write!(
                    f,
                    "if {} {} else {}",
                    self.condition, self.consequence, self.alternative
                )
            }
            ConditionalKind::Ternary => write!(
                f,
                "{} ? {} : {}",
                self.condition, self.consequence, self.alternative
            ),
        }
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct FunctionCallExpression<I, T, E> {
    pub function_key: DeclarationFunctionKey<I, T>,
    pub generics: Vec<Option<UExpression<I, T>>>,
    pub arguments: Vec<TypedExpression<I, T>>,
    ty: PhantomData<E>,
}

impl<I, T, E> FunctionCallExpression<I, T, E> {
    pub fn new(
        function_key: DeclarationFunctionKey<I, T>,
        generics: Vec<Option<UExpression<I, T>>>,
        arguments: Vec<TypedExpression<I, T>>,
    ) -> Self {
        FunctionCallExpression {
            function_key,
            generics,
            arguments,
            ty: PhantomData,
        }
    }
}

impl<I: fmt::Display, T: fmt::Display, E> fmt::Display for FunctionCallExpression<I, T, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.function_key.id,)?;
        if !self.generics.is_empty() {
            write!(
                f,
                "::<{}>",
                self.generics
                    .iter()
                    .map(|g| g
                        .as_ref()
                        .map(|g| g.to_string())
                        .unwrap_or_else(|| '_'.to_string()))
                    .collect::<Vec<_>>()
                    .join(", ")
            )?;
        }
        write!(
            f,
            "({})",
            self.arguments
                .iter()
                .map(|a| a.to_string())
                .collect::<Vec<_>>()
                .join(",")
        )
    }
}

/// An expression of type `field`
#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub enum FieldElementExpression<I, T> {
    Block(BlockExpression<I, T, Self>),
    Number(T),
    Identifier(IdentifierExpression<I, Self>),
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
    Conditional(ConditionalExpression<I, T, Self>),
    Neg(Box<FieldElementExpression<I, T>>),
    Pos(Box<FieldElementExpression<I, T>>),
    FunctionCall(FunctionCallExpression<I, T, Self>),
    Member(MemberExpression<I, T, Self>),
    Select(SelectExpression<I, T, Self>),
    Element(ElementExpression<I, T, Self>),
}
impl<I, T> Add for FieldElementExpression<I, T> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        FieldElementExpression::Add(box self, box other)
    }
}

impl<I, T> Sub for FieldElementExpression<I, T> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        FieldElementExpression::Sub(box self, box other)
    }
}

impl<I, T> Mul for FieldElementExpression<I, T> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        FieldElementExpression::Mult(box self, box other)
    }
}

impl<I, T> Div for FieldElementExpression<I, T> {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        FieldElementExpression::Div(box self, box other)
    }
}

impl<I, T> FieldElementExpression<I, T> {
    pub fn pow(self, other: UExpression<I, T>) -> Self {
        FieldElementExpression::Pow(box self, box other)
    }
}

impl<I, T> From<T> for FieldElementExpression<I, T> {
    fn from(n: T) -> Self {
        FieldElementExpression::Number(n)
    }
}

/// An expression of type `bool`
#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub enum BooleanExpression<I, T> {
    Block(BlockExpression<I, T, Self>),
    Identifier(IdentifierExpression<I, Self>),
    Value(bool),
    FieldLt(
        Box<FieldElementExpression<I, T>>,
        Box<FieldElementExpression<I, T>>,
    ),
    FieldLe(
        Box<FieldElementExpression<I, T>>,
        Box<FieldElementExpression<I, T>>,
    ),
    FieldGe(
        Box<FieldElementExpression<I, T>>,
        Box<FieldElementExpression<I, T>>,
    ),
    FieldGt(
        Box<FieldElementExpression<I, T>>,
        Box<FieldElementExpression<I, T>>,
    ),
    UintLt(Box<UExpression<I, T>>, Box<UExpression<I, T>>),
    UintLe(Box<UExpression<I, T>>, Box<UExpression<I, T>>),
    UintGe(Box<UExpression<I, T>>, Box<UExpression<I, T>>),
    UintGt(Box<UExpression<I, T>>, Box<UExpression<I, T>>),
    FieldEq(EqExpression<FieldElementExpression<I, T>>),
    BoolEq(EqExpression<BooleanExpression<I, T>>),
    ArrayEq(EqExpression<ArrayExpression<I, T>>),
    StructEq(EqExpression<StructExpression<I, T>>),
    TupleEq(EqExpression<TupleExpression<I, T>>),
    UintEq(EqExpression<UExpression<I, T>>),
    Or(Box<BooleanExpression<I, T>>, Box<BooleanExpression<I, T>>),
    And(Box<BooleanExpression<I, T>>, Box<BooleanExpression<I, T>>),
    Not(Box<BooleanExpression<I, T>>),
    Conditional(ConditionalExpression<I, T, Self>),
    Member(MemberExpression<I, T, Self>),
    FunctionCall(FunctionCallExpression<I, T, Self>),
    Select(SelectExpression<I, T, Self>),
    Element(ElementExpression<I, T, Self>),
}

impl<I, T> From<bool> for BooleanExpression<I, T> {
    fn from(b: bool) -> Self {
        BooleanExpression::Value(b)
    }
}

/// An expression of type `array`
/// # Remarks
/// * Contrary to basic types which are represented as enums, we wrap an enum `ArrayExpressionInner` in a struct in order to keep track of the type (content and size)
/// of the array. Only using an enum would require generics, which would propagate up to TypedExpression which we want to keep simple, hence this "runtime"
/// type checking
#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct ArrayExpression<I, T> {
    pub ty: Box<ArrayType<I, T>>,
    pub inner: ArrayExpressionInner<I, T>,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, PartialOrd, Ord)]
pub struct ArrayValue<I, T>(pub Vec<TypedExpressionOrSpread<I, T>>);

impl<I, T> From<Vec<TypedExpressionOrSpread<I, T>>> for ArrayValue<I, T> {
    fn from(array: Vec<TypedExpressionOrSpread<I, T>>) -> Self {
        Self(array)
    }
}

impl<I, T> IntoIterator for ArrayValue<I, T> {
    type Item = TypedExpressionOrSpread<I, T>;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<I: IdTrait, T: Field> ArrayValue<I, T> {
    fn expression_at_aux<
        U: Select<I, T> + From<TypedExpression<I, T>> + Into<TypedExpression<I, T>>,
    >(
        v: TypedExpressionOrSpread<I, T>,
    ) -> Vec<Option<U>> {
        match v {
            TypedExpressionOrSpread::Expression(e) => vec![Some(e.into())],
            TypedExpressionOrSpread::Spread(s) => match s.array.size().into_inner() {
                UExpressionInner::Value(size) => {
                    let array_ty = s.array.ty().clone();

                    match s.array.into_inner() {
                        ArrayExpressionInner::Value(v) => {
                            v.into_iter().flat_map(Self::expression_at_aux).collect()
                        }
                        a => (0..size)
                            .map(|i| {
                                Some(U::select(
                                    a.clone()
                                        .annotate(*array_ty.ty.clone(), *array_ty.size.clone()),
                                    i as u32,
                                ))
                            })
                            .collect(),
                    }
                }
                _ => vec![None],
            },
        }
    }

    pub fn expression_at<
        U: Select<I, T> + From<TypedExpression<I, T>> + Into<TypedExpression<I, T>>,
    >(
        &self,
        index: usize,
    ) -> Option<U> {
        self.0
            .iter()
            .flat_map(|v| Self::expression_at_aux(v.clone()))
            .take_while(|e| e.is_some())
            .map(|e| e.unwrap())
            .nth(index)
    }
}

impl<I, T> ArrayValue<I, T> {
    fn iter(&self) -> std::slice::Iter<TypedExpressionOrSpread<I, T>> {
        self.0.iter()
    }
}

impl<I, T> std::iter::FromIterator<TypedExpressionOrSpread<I, T>> for ArrayValue<I, T> {
    fn from_iter<J: IntoIterator<Item = TypedExpressionOrSpread<I, T>>>(iter: J) -> Self {
        Self(iter.into_iter().collect())
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub enum ArrayExpressionInner<I, T> {
    Block(BlockExpression<I, T, ArrayExpression<I, T>>),
    Identifier(IdentifierExpression<I, ArrayExpression<I, T>>),
    Value(ArrayValue<I, T>),
    FunctionCall(FunctionCallExpression<I, T, ArrayExpression<I, T>>),
    Conditional(ConditionalExpression<I, T, ArrayExpression<I, T>>),
    Member(MemberExpression<I, T, ArrayExpression<I, T>>),
    Select(SelectExpression<I, T, ArrayExpression<I, T>>),
    Element(ElementExpression<I, T, ArrayExpression<I, T>>),
    Slice(
        Box<ArrayExpression<I, T>>,
        Box<UExpression<I, T>>,
        Box<UExpression<I, T>>,
    ),
    Repeat(Box<TypedExpression<I, T>>, Box<UExpression<I, T>>),
}

impl<I, T> ArrayExpressionInner<I, T> {
    pub fn annotate<S: Into<UExpression<I, T>>>(
        self,
        ty: Type<I, T>,
        size: S,
    ) -> ArrayExpression<I, T> {
        ArrayExpression {
            ty: box (ty, size.into()).into(),
            inner: self,
        }
    }
}

impl<I: Clone, T: Clone> ArrayExpression<I, T> {
    pub fn inner_type(&self) -> &Type<I, T> {
        &self.ty.ty
    }

    pub fn size(&self) -> UExpression<I, T> {
        *self.ty.size.clone()
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct StructExpression<I, T> {
    ty: StructType<I, T>,
    inner: StructExpressionInner<I, T>,
}

impl<I, T> StructExpression<I, T> {
    pub fn ty(&self) -> &StructType<I, T> {
        &self.ty
    }

    pub fn as_inner(&self) -> &StructExpressionInner<I, T> {
        &self.inner
    }

    pub fn as_inner_mut(&mut self) -> &mut StructExpressionInner<I, T> {
        &mut self.inner
    }

    pub fn into_inner(self) -> StructExpressionInner<I, T> {
        self.inner
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub enum StructExpressionInner<I, T> {
    Block(BlockExpression<I, T, StructExpression<I, T>>),
    Identifier(IdentifierExpression<I, StructExpression<I, T>>),
    Value(Vec<TypedExpression<I, T>>),
    FunctionCall(FunctionCallExpression<I, T, StructExpression<I, T>>),
    Conditional(ConditionalExpression<I, T, StructExpression<I, T>>),
    Member(MemberExpression<I, T, StructExpression<I, T>>),
    Select(SelectExpression<I, T, StructExpression<I, T>>),
    Element(ElementExpression<I, T, StructExpression<I, T>>),
}

impl<I, T> StructExpressionInner<I, T> {
    pub fn annotate(self, ty: StructType<I, T>) -> StructExpression<I, T> {
        StructExpression { ty, inner: self }
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct TupleExpression<I, T> {
    ty: TupleType<I, T>,
    inner: TupleExpressionInner<I, T>,
}

impl<I, T> TupleExpression<I, T> {
    pub fn ty(&self) -> &TupleType<I, T> {
        &self.ty
    }

    pub fn as_inner(&self) -> &TupleExpressionInner<I, T> {
        &self.inner
    }

    pub fn as_inner_mut(&mut self) -> &mut TupleExpressionInner<I, T> {
        &mut self.inner
    }

    pub fn into_inner(self) -> TupleExpressionInner<I, T> {
        self.inner
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub enum TupleExpressionInner<I, T> {
    Block(BlockExpression<I, T, TupleExpression<I, T>>),
    Identifier(IdentifierExpression<I, TupleExpression<I, T>>),
    Value(Vec<TypedExpression<I, T>>),
    FunctionCall(FunctionCallExpression<I, T, TupleExpression<I, T>>),
    Conditional(ConditionalExpression<I, T, TupleExpression<I, T>>),
    Member(MemberExpression<I, T, TupleExpression<I, T>>),
    Select(SelectExpression<I, T, TupleExpression<I, T>>),
    Element(ElementExpression<I, T, TupleExpression<I, T>>),
}

impl<I, T> TupleExpressionInner<I, T> {
    pub fn annotate(self, ty: TupleType<I, T>) -> TupleExpression<I, T> {
        TupleExpression { ty, inner: self }
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for TupleExpression<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.inner {
            TupleExpressionInner::Block(ref block) => write!(f, "{}", block),
            TupleExpressionInner::Identifier(ref var) => write!(f, "{}", var),
            TupleExpressionInner::Value(ref values) => {
                write!(f, "(")?;
                match values.len() {
                    1 => write!(f, "{},", values[0]),
                    _ => write!(
                        f,
                        "{}",
                        values
                            .iter()
                            .map(|v| v.to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                }?;
                write!(f, ")")
            }
            TupleExpressionInner::FunctionCall(ref function_call) => {
                write!(f, "{}", function_call)
            }
            TupleExpressionInner::Conditional(ref c) => write!(f, "{}", c),
            TupleExpressionInner::Member(ref m) => write!(f, "{}", m),
            TupleExpressionInner::Select(ref select) => write!(f, "{}", select),
            TupleExpressionInner::Element(ref element) => write!(f, "{}", element),
        }
    }
}

// Downcasts
// Due to the fact that we keep TypedExpression simple, we end up with ArrayExpressionInner::Value whose elements are any TypedExpression, but we enforce by
// construction that these elements are of the type declared in the corresponding ArrayExpression. As we know this by construction, we can downcast the TypedExpression to the correct type
// ArrayExpression { type: Type::FieldElement, size: 42, inner: [TypedExpression::FieldElement(FieldElementExpression), ...]} <- the fact that inner only contains field elements is not enforced by the rust type system
impl<I, T> From<TypedExpression<I, T>> for FieldElementExpression<I, T> {
    fn from(te: TypedExpression<I, T>) -> FieldElementExpression<I, T> {
        match te {
            TypedExpression::FieldElement(e) => e,
            _ => unreachable!("downcast failed"),
        }
    }
}

impl<I, T> From<TypedExpression<I, T>> for BooleanExpression<I, T> {
    fn from(te: TypedExpression<I, T>) -> BooleanExpression<I, T> {
        match te {
            TypedExpression::Boolean(e) => e,
            _ => unreachable!("downcast failed"),
        }
    }
}

impl<I, T> From<TypedExpression<I, T>> for UExpression<I, T> {
    fn from(te: TypedExpression<I, T>) -> UExpression<I, T> {
        match te {
            TypedExpression::Uint(e) => e,
            _ => unreachable!("downcast failed"),
        }
    }
}

impl<I, T> From<TypedExpression<I, T>> for ArrayExpression<I, T> {
    fn from(te: TypedExpression<I, T>) -> ArrayExpression<I, T> {
        match te {
            TypedExpression::Array(e) => e,
            _ => unreachable!("downcast failed"),
        }
    }
}

impl<I, T> From<TypedExpression<I, T>> for IntExpression<I, T> {
    fn from(te: TypedExpression<I, T>) -> IntExpression<I, T> {
        match te {
            TypedExpression::Int(e) => e,
            _ => unreachable!("downcast failed"),
        }
    }
}

impl<I, T> From<TypedExpression<I, T>> for StructExpression<I, T> {
    fn from(te: TypedExpression<I, T>) -> StructExpression<I, T> {
        match te {
            TypedExpression::Struct(e) => e,
            _ => unreachable!("downcast failed"),
        }
    }
}

impl<I, T> From<TypedExpression<I, T>> for TupleExpression<I, T> {
    fn from(te: TypedExpression<I, T>) -> TupleExpression<I, T> {
        match te {
            TypedExpression::Tuple(e) => e,
            _ => unreachable!("downcast failed"),
        }
    }
}

impl<I, T> From<TypedConstant<I, T>> for FieldElementExpression<I, T> {
    fn from(tc: TypedConstant<I, T>) -> FieldElementExpression<I, T> {
        tc.expression.into()
    }
}

impl<I, T> From<TypedConstant<I, T>> for BooleanExpression<I, T> {
    fn from(tc: TypedConstant<I, T>) -> BooleanExpression<I, T> {
        tc.expression.into()
    }
}

impl<I, T> From<TypedConstant<I, T>> for UExpression<I, T> {
    fn from(tc: TypedConstant<I, T>) -> UExpression<I, T> {
        tc.expression.into()
    }
}

impl<I, T> From<TypedConstant<I, T>> for ArrayExpression<I, T> {
    fn from(tc: TypedConstant<I, T>) -> ArrayExpression<I, T> {
        tc.expression.into()
    }
}

impl<I, T> From<TypedConstant<I, T>> for StructExpression<I, T> {
    fn from(tc: TypedConstant<I, T>) -> StructExpression<I, T> {
        tc.expression.into()
    }
}

impl<I, T> From<TypedConstant<I, T>> for TupleExpression<I, T> {
    fn from(tc: TypedConstant<I, T>) -> TupleExpression<I, T> {
        tc.expression.into()
    }
}

impl<I, T> From<TypedConstant<I, T>> for IntExpression<I, T> {
    fn from(tc: TypedConstant<I, T>) -> IntExpression<I, T> {
        tc.expression.into()
    }
}

impl<I: fmt::Display, T: fmt::Display, E: fmt::Display> fmt::Display for BlockExpression<I, T, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{{\n{}\n}}",
            self.statements
                .iter()
                .map(|s| s.to_string())
                .chain(std::iter::once(self.value.to_string()))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for FieldElementExpression<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FieldElementExpression::Block(ref block) => write!(f, "{}", block),
            FieldElementExpression::Number(ref i) => write!(f, "{}f", i),
            FieldElementExpression::Identifier(ref var) => write!(f, "{}", var),
            FieldElementExpression::Add(ref lhs, ref rhs) => write!(f, "({} + {})", lhs, rhs),
            FieldElementExpression::Sub(ref lhs, ref rhs) => write!(f, "({} - {})", lhs, rhs),
            FieldElementExpression::Mult(ref lhs, ref rhs) => write!(f, "({} * {})", lhs, rhs),
            FieldElementExpression::Div(ref lhs, ref rhs) => write!(f, "({} / {})", lhs, rhs),
            FieldElementExpression::Pow(ref lhs, ref rhs) => write!(f, "{}**{}", lhs, rhs),
            FieldElementExpression::Neg(ref e) => write!(f, "(-{})", e),
            FieldElementExpression::Pos(ref e) => write!(f, "(+{})", e),
            FieldElementExpression::Conditional(ref c) => write!(f, "{}", c),
            FieldElementExpression::FunctionCall(ref function_call) => {
                write!(f, "{}", function_call)
            }
            FieldElementExpression::Member(ref m) => write!(f, "{}", m),
            FieldElementExpression::Select(ref select) => write!(f, "{}", select),
            FieldElementExpression::Element(ref element) => write!(f, "{}", element),
        }
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for UExpression<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.inner {
            UExpressionInner::Block(ref block) => write!(f, "{}", block,),
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
            UExpressionInner::Select(ref select) => write!(f, "{}", select),
            UExpressionInner::FunctionCall(ref function_call) => write!(f, "{}", function_call),
            UExpressionInner::Conditional(ref c) => write!(f, "{}", c),
            UExpressionInner::Member(ref m) => write!(f, "{}", m),
            UExpressionInner::Element(ref element) => write!(f, "{}", element),
        }
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for BooleanExpression<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            BooleanExpression::Block(ref block) => write!(f, "{}", block,),
            BooleanExpression::Identifier(ref var) => write!(f, "{}", var),
            BooleanExpression::FieldLt(ref lhs, ref rhs) => write!(f, "({} < {})", lhs, rhs),
            BooleanExpression::FieldLe(ref lhs, ref rhs) => write!(f, "({} <= {})", lhs, rhs),
            BooleanExpression::FieldGe(ref lhs, ref rhs) => write!(f, "({} >= {})", lhs, rhs),
            BooleanExpression::FieldGt(ref lhs, ref rhs) => write!(f, "({} > {})", lhs, rhs),
            BooleanExpression::UintLt(ref lhs, ref rhs) => write!(f, "({} < {})", lhs, rhs),
            BooleanExpression::UintLe(ref lhs, ref rhs) => write!(f, "({} <= {})", lhs, rhs),
            BooleanExpression::UintGe(ref lhs, ref rhs) => write!(f, "({} >= {})", lhs, rhs),
            BooleanExpression::UintGt(ref lhs, ref rhs) => write!(f, "({} > {})", lhs, rhs),
            BooleanExpression::FieldEq(ref e) => write!(f, "{}", e),
            BooleanExpression::BoolEq(ref e) => write!(f, "{}", e),
            BooleanExpression::ArrayEq(ref e) => write!(f, "{}", e),
            BooleanExpression::StructEq(ref e) => write!(f, "{}", e),
            BooleanExpression::TupleEq(ref e) => write!(f, "{}", e),
            BooleanExpression::UintEq(ref e) => write!(f, "{}", e),
            BooleanExpression::Or(ref lhs, ref rhs) => write!(f, "({} || {})", lhs, rhs),
            BooleanExpression::And(ref lhs, ref rhs) => write!(f, "({} && {})", lhs, rhs),
            BooleanExpression::Not(ref exp) => write!(f, "!{}", exp),
            BooleanExpression::Value(b) => write!(f, "{}", b),
            BooleanExpression::FunctionCall(ref function_call) => write!(f, "{}", function_call),
            BooleanExpression::Conditional(ref c) => write!(f, "{}", c),
            BooleanExpression::Member(ref m) => write!(f, "{}", m),
            BooleanExpression::Select(ref select) => write!(f, "{}", select),
            BooleanExpression::Element(ref element) => write!(f, "{}", element),
        }
    }
}

impl<I: fmt::Display, T: fmt::Display> fmt::Display for ArrayExpressionInner<I, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ArrayExpressionInner::Block(ref block) => write!(f, "{}", block,),
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
            ArrayExpressionInner::FunctionCall(ref function_call) => write!(f, "{}", function_call),
            ArrayExpressionInner::Conditional(ref c) => write!(f, "{}", c),
            ArrayExpressionInner::Member(ref m) => write!(f, "{}", m),
            ArrayExpressionInner::Select(ref select) => write!(f, "{}", select),
            ArrayExpressionInner::Slice(ref a, ref from, ref to) => {
                write!(f, "{}[{}..{}]", a, from, to)
            }
            ArrayExpressionInner::Repeat(ref e, ref count) => {
                write!(f, "[{}; {}]", e, count)
            }
            ArrayExpressionInner::Element(ref element) => write!(f, "{}", element),
        }
    }
}

// Variable to TypedExpression conversion

impl<I: IdTrait, T: Field> From<Variable<I, T>> for TypedExpression<I, T> {
    fn from(v: Variable<I, T>) -> Self {
        match v.get_type() {
            Type::FieldElement => FieldElementExpression::identifier(v.id).into(),
            Type::Boolean => BooleanExpression::identifier(v.id).into(),
            Type::Array(ty) => ArrayExpression::identifier(v.id)
                .annotate(*ty.ty, *ty.size)
                .into(),
            Type::Struct(ty) => StructExpression::identifier(v.id).annotate(ty).into(),
            Type::Tuple(ty) => TupleExpression::identifier(v.id).annotate(ty).into(),
            Type::Uint(w) => UExpression::identifier(v.id).annotate(w).into(),
            Type::Int => unreachable!(),
        }
    }
}

// Common behaviour across expressions

pub trait Expr<I, T>: fmt::Display + From<TypedExpression<I, T>> {
    type Inner;
    type Ty: Clone + IntoType<UExpression<I, T>>;
    type ConcreteTy: Clone + IntoType<u32>;

    fn ty(&self) -> &Self::Ty;

    fn into_inner(self) -> Self::Inner;

    fn as_inner(&self) -> &Self::Inner;

    fn as_inner_mut(&mut self) -> &mut Self::Inner;
}

impl<I: IdTrait, T: Field> Expr<I, T> for FieldElementExpression<I, T> {
    type Inner = Self;
    type Ty = Type<I, T>;
    type ConcreteTy = ConcreteType;

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

impl<I: IdTrait, T: Field> Expr<I, T> for BooleanExpression<I, T> {
    type Inner = Self;
    type Ty = Type<I, T>;
    type ConcreteTy = ConcreteType;

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

impl<I: IdTrait, T: Field> Expr<I, T> for UExpression<I, T> {
    type Inner = UExpressionInner<I, T>;
    type Ty = UBitwidth;
    type ConcreteTy = UBitwidth;

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

impl<I: IdTrait, T: Field> Expr<I, T> for StructExpression<I, T> {
    type Inner = StructExpressionInner<I, T>;
    type Ty = StructType<I, T>;
    type ConcreteTy = ConcreteStructType;

    fn ty(&self) -> &Self::Ty {
        &self.ty
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

impl<I: IdTrait, T: Field> Expr<I, T> for ArrayExpression<I, T> {
    type Inner = ArrayExpressionInner<I, T>;
    type Ty = ArrayType<I, T>;
    type ConcreteTy = ConcreteArrayType;

    fn ty(&self) -> &Self::Ty {
        &self.ty
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

impl<I: IdTrait, T: Field> Expr<I, T> for TupleExpression<I, T> {
    type Inner = TupleExpressionInner<I, T>;
    type Ty = TupleType<I, T>;
    type ConcreteTy = ConcreteTupleType;

    fn ty(&self) -> &Self::Ty {
        &self.ty
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

impl<I: IdTrait, T: Field> Expr<I, T> for IntExpression<I, T> {
    type Inner = Self;
    type Ty = Type<I, T>;
    type ConcreteTy = ConcreteType;

    fn ty(&self) -> &Self::Ty {
        &Type::Int
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

// Enums types to enable returning e.g a member expression OR another type of expression of this type

pub enum FunctionCallOrExpression<I, T, E: Expr<I, T>> {
    FunctionCall(FunctionCallExpression<I, T, E>),
    Expression(E::Inner),
}
pub enum SelectOrExpression<I, T, E: Expr<I, T>> {
    Select(SelectExpression<I, T, E>),
    Expression(E::Inner),
}

pub enum EqOrBoolean<I, T, E> {
    Eq(EqExpression<E>),
    Boolean(BooleanExpression<I, T>),
}

pub enum MemberOrExpression<I, T, E: Expr<I, T>> {
    Member(MemberExpression<I, T, E>),
    Expression(E::Inner),
}

pub enum IdentifierOrExpression<I, T, E: Expr<I, T>> {
    Identifier(IdentifierExpression<I, E>),
    Expression(E::Inner),
}

pub enum ElementOrExpression<I, T, E: Expr<I, T>> {
    Element(ElementExpression<I, T, E>),
    Expression(E::Inner),
}

pub enum ConditionalOrExpression<I, T, E: Expr<I, T>> {
    Conditional(ConditionalExpression<I, T, E>),
    Expression(E::Inner),
}

pub trait Conditional<I, T> {
    fn conditional(
        condition: BooleanExpression<I, T>,
        consequence: Self,
        alternative: Self,
        kind: ConditionalKind,
    ) -> Self;
}

impl<I, T> Conditional<I, T> for FieldElementExpression<I, T> {
    fn conditional(
        condition: BooleanExpression<I, T>,
        consequence: Self,
        alternative: Self,
        kind: ConditionalKind,
    ) -> Self {
        FieldElementExpression::Conditional(ConditionalExpression::new(
            condition,
            consequence,
            alternative,
            kind,
        ))
    }
}

impl<I, T> Conditional<I, T> for IntExpression<I, T> {
    fn conditional(
        condition: BooleanExpression<I, T>,
        consequence: Self,
        alternative: Self,
        kind: ConditionalKind,
    ) -> Self {
        IntExpression::Conditional(ConditionalExpression::new(
            condition,
            consequence,
            alternative,
            kind,
        ))
    }
}

impl<I, T> Conditional<I, T> for BooleanExpression<I, T> {
    fn conditional(
        condition: BooleanExpression<I, T>,
        consequence: Self,
        alternative: Self,
        kind: ConditionalKind,
    ) -> Self {
        BooleanExpression::Conditional(ConditionalExpression::new(
            condition,
            consequence,
            alternative,
            kind,
        ))
    }
}

impl<I, T> Conditional<I, T> for UExpression<I, T> {
    fn conditional(
        condition: BooleanExpression<I, T>,
        consequence: Self,
        alternative: Self,
        kind: ConditionalKind,
    ) -> Self {
        let bitwidth = consequence.bitwidth;

        UExpressionInner::Conditional(ConditionalExpression::new(
            condition,
            consequence,
            alternative,
            kind,
        ))
        .annotate(bitwidth)
    }
}

impl<I: Clone, T: Clone> Conditional<I, T> for ArrayExpression<I, T> {
    fn conditional(
        condition: BooleanExpression<I, T>,
        consequence: Self,
        alternative: Self,
        kind: ConditionalKind,
    ) -> Self {
        let ty = consequence.inner_type().clone();
        let size = consequence.size();
        ArrayExpressionInner::Conditional(ConditionalExpression::new(
            condition,
            consequence,
            alternative,
            kind,
        ))
        .annotate(ty, size)
    }
}

impl<I: Clone, T: Clone> Conditional<I, T> for StructExpression<I, T> {
    fn conditional(
        condition: BooleanExpression<I, T>,
        consequence: Self,
        alternative: Self,
        kind: ConditionalKind,
    ) -> Self {
        let ty = consequence.ty().clone();
        StructExpressionInner::Conditional(ConditionalExpression::new(
            condition,
            consequence,
            alternative,
            kind,
        ))
        .annotate(ty)
    }
}

impl<I: Clone, T: Clone> Conditional<I, T> for TupleExpression<I, T> {
    fn conditional(
        condition: BooleanExpression<I, T>,
        consequence: Self,
        alternative: Self,
        kind: ConditionalKind,
    ) -> Self {
        let ty = consequence.ty().clone();
        TupleExpressionInner::Conditional(ConditionalExpression::new(
            condition,
            consequence,
            alternative,
            kind,
        ))
        .annotate(ty)
    }
}

pub trait Select<I, T> {
    fn select<J: Into<UExpression<I, T>>>(array: ArrayExpression<I, T>, index: J) -> Self;
}

impl<I, T> Select<I, T> for FieldElementExpression<I, T> {
    fn select<J: Into<UExpression<I, T>>>(array: ArrayExpression<I, T>, index: J) -> Self {
        FieldElementExpression::Select(SelectExpression::new(array, index.into()))
    }
}

impl<I, T> Select<I, T> for IntExpression<I, T> {
    fn select<J: Into<UExpression<I, T>>>(array: ArrayExpression<I, T>, index: J) -> Self {
        IntExpression::Select(SelectExpression::new(array, index.into()))
    }
}

impl<I, T> Select<I, T> for BooleanExpression<I, T> {
    fn select<J: Into<UExpression<I, T>>>(array: ArrayExpression<I, T>, index: J) -> Self {
        BooleanExpression::Select(SelectExpression::new(array, index.into()))
    }
}

impl<I: IdTrait, T: Field> Select<I, T> for TypedExpression<I, T> {
    fn select<J: Into<UExpression<I, T>>>(array: ArrayExpression<I, T>, index: J) -> Self {
        match *array.ty().ty {
            Type::Array(..) => ArrayExpression::select(array, index).into(),
            Type::Struct(..) => StructExpression::select(array, index).into(),
            Type::Tuple(..) => TupleExpression::select(array, index).into(),
            Type::FieldElement => FieldElementExpression::select(array, index).into(),
            Type::Boolean => BooleanExpression::select(array, index).into(),
            Type::Int => IntExpression::select(array, index).into(),
            Type::Uint(..) => UExpression::select(array, index).into(),
        }
    }
}

impl<I: Clone, T: Clone> Select<I, T> for UExpression<I, T> {
    fn select<J: Into<UExpression<I, T>>>(array: ArrayExpression<I, T>, index: J) -> Self {
        let bitwidth = match array.inner_type().clone() {
            Type::Uint(bitwidth) => bitwidth,
            _ => unreachable!(),
        };

        UExpressionInner::Select(SelectExpression::new(array, index.into())).annotate(bitwidth)
    }
}

impl<I: Clone, T: Clone> Select<I, T> for ArrayExpression<I, T> {
    fn select<J: Into<UExpression<I, T>>>(array: ArrayExpression<I, T>, index: J) -> Self {
        let (ty, size) = match array.inner_type() {
            Type::Array(array_type) => (array_type.ty.clone(), array_type.size.clone()),
            _ => unreachable!(),
        };

        ArrayExpressionInner::Select(SelectExpression::new(array, index.into()))
            .annotate(*ty, *size)
    }
}

impl<I: Clone, T: Clone> Select<I, T> for StructExpression<I, T> {
    fn select<J: Into<UExpression<I, T>>>(array: ArrayExpression<I, T>, index: J) -> Self {
        let members = match array.inner_type().clone() {
            Type::Struct(members) => members,
            _ => unreachable!(),
        };

        StructExpressionInner::Select(SelectExpression::new(array, index.into())).annotate(members)
    }
}

impl<I: Clone, T: Clone> Select<I, T> for TupleExpression<I, T> {
    fn select<J: Into<UExpression<I, T>>>(array: ArrayExpression<I, T>, index: J) -> Self {
        let elements = match array.inner_type().clone() {
            Type::Tuple(elements) => elements,
            _ => unreachable!(),
        };

        TupleExpressionInner::Select(SelectExpression::new(array, index.into())).annotate(elements)
    }
}

pub trait Member<I, T>: Sized {
    fn member(s: StructExpression<I, T>, id: MemberId) -> Self;
}

impl<I, T> Member<I, T> for FieldElementExpression<I, T> {
    fn member(s: StructExpression<I, T>, id: MemberId) -> Self {
        FieldElementExpression::Member(MemberExpression::new(s, id))
    }
}

impl<I, T> Member<I, T> for BooleanExpression<I, T> {
    fn member(s: StructExpression<I, T>, id: MemberId) -> Self {
        BooleanExpression::Member(MemberExpression::new(s, id))
    }
}

impl<I: Clone, T: Clone> Member<I, T> for UExpression<I, T> {
    fn member(s: StructExpression<I, T>, id: MemberId) -> Self {
        let ty = s.ty().members.iter().find(|member| id == member.id);
        let bitwidth = match ty {
            Some(crate::typed::types::StructMember {
                ty: box Type::Uint(bitwidth),
                ..
            }) => *bitwidth,
            _ => unreachable!(),
        };
        UExpressionInner::Member(MemberExpression::new(s, id)).annotate(bitwidth)
    }
}

impl<I: Clone, T: Clone> Member<I, T> for ArrayExpression<I, T> {
    fn member(s: StructExpression<I, T>, id: MemberId) -> Self {
        let ty = s.ty().members.iter().find(|member| id == member.id);
        let (ty, size) = match ty {
            Some(crate::typed::types::StructMember {
                ty: box Type::Array(array_ty),
                ..
            }) => (*array_ty.ty.clone(), array_ty.size.clone()),
            _ => unreachable!(),
        };
        ArrayExpressionInner::Member(MemberExpression::new(s, id)).annotate(ty, *size)
    }
}

impl<I: Clone, T: Clone> Member<I, T> for StructExpression<I, T> {
    fn member(s: StructExpression<I, T>, id: MemberId) -> Self {
        let ty = s.ty().members.iter().find(|member| id == member.id);
        let struct_ty = match ty {
            Some(crate::typed::types::StructMember {
                ty: box Type::Struct(struct_ty),
                ..
            }) => struct_ty.clone(),
            _ => unreachable!(),
        };
        StructExpressionInner::Member(MemberExpression::new(s, id)).annotate(struct_ty)
    }
}

impl<I: Clone, T: Clone> Member<I, T> for TupleExpression<I, T> {
    fn member(s: StructExpression<I, T>, id: MemberId) -> Self {
        let ty = s.ty().members.iter().find(|member| id == member.id);
        let tuple_ty = match ty {
            Some(crate::typed::types::StructMember {
                ty: box Type::Tuple(tuple_ty),
                ..
            }) => tuple_ty.clone(),
            _ => unreachable!(),
        };
        TupleExpressionInner::Member(MemberExpression::new(s, id)).annotate(tuple_ty)
    }
}

pub trait Element<I, T>: Sized {
    fn element(s: TupleExpression<I, T>, id: u32) -> Self;
}

impl<I, T> Element<I, T> for FieldElementExpression<I, T> {
    fn element(s: TupleExpression<I, T>, id: u32) -> Self {
        FieldElementExpression::Element(ElementExpression::new(s, id))
    }
}

impl<I, T> Element<I, T> for BooleanExpression<I, T> {
    fn element(s: TupleExpression<I, T>, id: u32) -> Self {
        BooleanExpression::Element(ElementExpression::new(s, id))
    }
}

impl<I: Clone, T: Clone> Element<I, T> for UExpression<I, T> {
    fn element(s: TupleExpression<I, T>, id: u32) -> Self {
        let ty = &s.ty().elements[id as usize];
        let bitwidth = match ty {
            Type::Uint(bitwidth) => *bitwidth,
            _ => unreachable!(),
        };
        UExpressionInner::Element(ElementExpression::new(s, id)).annotate(bitwidth)
    }
}

impl<I: Clone, T: Clone> Element<I, T> for ArrayExpression<I, T> {
    fn element(s: TupleExpression<I, T>, id: u32) -> Self {
        let ty = &s.ty().elements[id as usize];
        let (ty, size) = match ty {
            Type::Array(array_ty) => (*array_ty.ty.clone(), array_ty.size.clone()),
            _ => unreachable!(),
        };
        ArrayExpressionInner::Element(ElementExpression::new(s, id)).annotate(ty, *size)
    }
}

impl<I: Clone, T: Clone> Element<I, T> for StructExpression<I, T> {
    fn element(s: TupleExpression<I, T>, id: u32) -> Self {
        let ty = &s.ty().elements[id as usize];
        let struct_ty = match ty {
            Type::Struct(struct_ty) => struct_ty.clone(),
            _ => unreachable!(),
        };
        StructExpressionInner::Element(ElementExpression::new(s, id)).annotate(struct_ty)
    }
}

impl<I: Clone, T: Clone> Element<I, T> for TupleExpression<I, T> {
    fn element(s: TupleExpression<I, T>, id: u32) -> Self {
        let ty = &s.ty().elements[id as usize];
        let tuple_ty = match ty {
            Type::Tuple(tuple_ty) => tuple_ty.clone(),
            _ => unreachable!(),
        };
        TupleExpressionInner::Element(ElementExpression::new(s, id)).annotate(tuple_ty)
    }
}

pub trait Id<I, T>: Expr<I, T> {
    fn identifier(id: Identifier<I>) -> Self::Inner;
}

impl<I: IdTrait, T: Field> Id<I, T> for FieldElementExpression<I, T> {
    fn identifier(id: Identifier<I>) -> Self::Inner {
        FieldElementExpression::Identifier(IdentifierExpression::new(id))
    }
}

impl<I: IdTrait, T: Field> Id<I, T> for BooleanExpression<I, T> {
    fn identifier(id: Identifier<I>) -> Self::Inner {
        BooleanExpression::Identifier(IdentifierExpression::new(id))
    }
}

impl<I: IdTrait, T: Field> Id<I, T> for UExpression<I, T> {
    fn identifier(id: Identifier<I>) -> Self::Inner {
        UExpressionInner::Identifier(IdentifierExpression::new(id))
    }
}

impl<I: IdTrait, T: Field> Id<I, T> for ArrayExpression<I, T> {
    fn identifier(id: Identifier<I>) -> Self::Inner {
        ArrayExpressionInner::Identifier(IdentifierExpression::new(id))
    }
}

impl<I: IdTrait, T: Field> Id<I, T> for StructExpression<I, T> {
    fn identifier(id: Identifier<I>) -> Self::Inner {
        StructExpressionInner::Identifier(IdentifierExpression::new(id))
    }
}

impl<I: IdTrait, T: Field> Id<I, T> for TupleExpression<I, T> {
    fn identifier(id: Identifier<I>) -> Self::Inner {
        TupleExpressionInner::Identifier(IdentifierExpression::new(id))
    }
}

pub trait FunctionCall<I, T>: Expr<I, T> {
    fn function_call(
        key: DeclarationFunctionKey<I, T>,
        generics: Vec<Option<UExpression<I, T>>>,
        arguments: Vec<TypedExpression<I, T>>,
    ) -> Self::Inner;
}

impl<I: IdTrait, T: Field> FunctionCall<I, T> for FieldElementExpression<I, T> {
    fn function_call(
        key: DeclarationFunctionKey<I, T>,
        generics: Vec<Option<UExpression<I, T>>>,
        arguments: Vec<TypedExpression<I, T>>,
    ) -> Self::Inner {
        FieldElementExpression::FunctionCall(FunctionCallExpression::new(key, generics, arguments))
    }
}

impl<I: IdTrait, T: Field> FunctionCall<I, T> for BooleanExpression<I, T> {
    fn function_call(
        key: DeclarationFunctionKey<I, T>,
        generics: Vec<Option<UExpression<I, T>>>,
        arguments: Vec<TypedExpression<I, T>>,
    ) -> Self::Inner {
        BooleanExpression::FunctionCall(FunctionCallExpression::new(key, generics, arguments))
    }
}

impl<I: IdTrait, T: Field> FunctionCall<I, T> for UExpression<I, T> {
    fn function_call(
        key: DeclarationFunctionKey<I, T>,
        generics: Vec<Option<UExpression<I, T>>>,
        arguments: Vec<TypedExpression<I, T>>,
    ) -> Self::Inner {
        UExpressionInner::FunctionCall(FunctionCallExpression::new(key, generics, arguments))
    }
}

impl<I: IdTrait, T: Field> FunctionCall<I, T> for ArrayExpression<I, T> {
    fn function_call(
        key: DeclarationFunctionKey<I, T>,
        generics: Vec<Option<UExpression<I, T>>>,
        arguments: Vec<TypedExpression<I, T>>,
    ) -> Self::Inner {
        ArrayExpressionInner::FunctionCall(FunctionCallExpression::new(key, generics, arguments))
    }
}

impl<I: IdTrait, T: Field> FunctionCall<I, T> for TupleExpression<I, T> {
    fn function_call(
        key: DeclarationFunctionKey<I, T>,
        generics: Vec<Option<UExpression<I, T>>>,
        arguments: Vec<TypedExpression<I, T>>,
    ) -> Self::Inner {
        TupleExpressionInner::FunctionCall(FunctionCallExpression::new(key, generics, arguments))
    }
}

impl<I: IdTrait, T: Field> FunctionCall<I, T> for StructExpression<I, T> {
    fn function_call(
        key: DeclarationFunctionKey<I, T>,
        generics: Vec<Option<UExpression<I, T>>>,
        arguments: Vec<TypedExpression<I, T>>,
    ) -> Self::Inner {
        StructExpressionInner::FunctionCall(FunctionCallExpression::new(key, generics, arguments))
    }
}

pub trait Block<I, T> {
    fn block(statements: Vec<TypedStatement<I, T>>, value: Self) -> Self;
}

impl<I: IdTrait, T: Field> Block<I, T> for FieldElementExpression<I, T> {
    fn block(statements: Vec<TypedStatement<I, T>>, value: Self) -> Self {
        FieldElementExpression::Block(BlockExpression::new(statements, value))
    }
}

impl<I: IdTrait, T: Field> Block<I, T> for BooleanExpression<I, T> {
    fn block(statements: Vec<TypedStatement<I, T>>, value: Self) -> Self {
        BooleanExpression::Block(BlockExpression::new(statements, value))
    }
}

impl<I: IdTrait, T: Field> Block<I, T> for UExpression<I, T> {
    fn block(statements: Vec<TypedStatement<I, T>>, value: Self) -> Self {
        let bitwidth = value.bitwidth();
        UExpressionInner::Block(BlockExpression::new(statements, value)).annotate(bitwidth)
    }
}

impl<I: IdTrait, T: Field> Block<I, T> for ArrayExpression<I, T> {
    fn block(statements: Vec<TypedStatement<I, T>>, value: Self) -> Self {
        let array_ty = value.ty().clone();
        ArrayExpressionInner::Block(BlockExpression::new(statements, value))
            .annotate(*array_ty.ty, *array_ty.size)
    }
}

impl<I: IdTrait, T: Field> Block<I, T> for TupleExpression<I, T> {
    fn block(statements: Vec<TypedStatement<I, T>>, value: Self) -> Self {
        let tuple_ty = value.ty().clone();
        TupleExpressionInner::Block(BlockExpression::new(statements, value)).annotate(tuple_ty)
    }
}

impl<I: IdTrait, T: Field> Block<I, T> for StructExpression<I, T> {
    fn block(statements: Vec<TypedStatement<I, T>>, value: Self) -> Self {
        let struct_ty = value.ty().clone();

        StructExpressionInner::Block(BlockExpression::new(statements, value)).annotate(struct_ty)
    }
}

pub trait Constant: Sized {
    // return whether this is constant
    fn is_constant(&self) -> bool;

    // canonicalize an expression *that we know to be constant*
    // for example for [0; 3] -> [0, 0, 0], [...[1], 2] -> [1, 2], etc
    fn into_canonical_constant(self) -> Self {
        self
    }
}

impl<I: IdTrait, T: Field> Constant for FieldElementExpression<I, T> {
    fn is_constant(&self) -> bool {
        matches!(self, FieldElementExpression::Number(..))
    }
}

impl<I: IdTrait, T: Field> Constant for BooleanExpression<I, T> {
    fn is_constant(&self) -> bool {
        matches!(self, BooleanExpression::Value(..))
    }
}

impl<I: IdTrait, T: Field> Constant for UExpression<I, T> {
    fn is_constant(&self) -> bool {
        matches!(self.as_inner(), UExpressionInner::Value(..))
    }
}

impl<I: IdTrait, T: Field> Constant for ArrayExpression<I, T> {
    fn is_constant(&self) -> bool {
        match self.as_inner() {
            ArrayExpressionInner::Value(v) => v.0.iter().all(|e| match e {
                TypedExpressionOrSpread::Expression(e) => e.is_constant(),
                TypedExpressionOrSpread::Spread(s) => s.array.is_constant(),
            }),
            ArrayExpressionInner::Slice(box a, box from, box to) => {
                from.is_constant() && to.is_constant() && a.is_constant()
            }
            ArrayExpressionInner::Repeat(box e, box count) => {
                count.is_constant() && e.is_constant()
            }
            _ => false,
        }
    }

    fn into_canonical_constant(self) -> Self {
        fn into_canonical_constant_aux<I: IdTrait, T: Field>(
            e: TypedExpressionOrSpread<I, T>,
        ) -> Vec<TypedExpression<I, T>> {
            match e {
                TypedExpressionOrSpread::Expression(e) => vec![e],
                TypedExpressionOrSpread::Spread(s) => match s.array.into_inner() {
                    ArrayExpressionInner::Value(v) => v
                        .into_iter()
                        .flat_map(into_canonical_constant_aux)
                        .collect(),
                    ArrayExpressionInner::Slice(box v, box from, box to) => {
                        let from = match from.into_inner() {
                            UExpressionInner::Value(v) => v,
                            _ => unreachable!(),
                        };

                        let to = match to.into_inner() {
                            UExpressionInner::Value(v) => v,
                            _ => unreachable!(),
                        };

                        let v = match v.into_inner() {
                            ArrayExpressionInner::Value(v) => v,
                            _ => unreachable!(),
                        };

                        v.into_iter()
                            .flat_map(into_canonical_constant_aux)
                            .skip(from as usize)
                            .take(to as usize - from as usize)
                            .collect()
                    }
                    ArrayExpressionInner::Repeat(box e, box count) => {
                        let count = match count.into_inner() {
                            UExpressionInner::Value(count) => count,
                            _ => unreachable!(),
                        };

                        vec![e; count as usize]
                    }
                    a => unreachable!("{}", a),
                },
            }
        }

        let array_ty = self.ty().clone();

        match self.into_inner() {
            ArrayExpressionInner::Value(v) => ArrayExpressionInner::Value(
                v.into_iter()
                    .flat_map(into_canonical_constant_aux)
                    .map(|e| e.into())
                    .collect::<Vec<_>>()
                    .into(),
            )
            .annotate(*array_ty.ty, *array_ty.size),
            ArrayExpressionInner::Slice(box a, box from, box to) => {
                let from = match from.into_inner() {
                    UExpressionInner::Value(from) => from as usize,
                    _ => unreachable!("should be a uint value"),
                };

                let to = match to.into_inner() {
                    UExpressionInner::Value(to) => to as usize,
                    _ => unreachable!("should be a uint value"),
                };

                let v = match a.into_inner() {
                    ArrayExpressionInner::Value(v) => v,
                    _ => unreachable!("should be an array value"),
                };

                ArrayExpressionInner::Value(
                    v.into_iter()
                        .flat_map(into_canonical_constant_aux)
                        .map(|e| e.into())
                        .skip(from)
                        .take(to - from)
                        .collect::<Vec<_>>()
                        .into(),
                )
                .annotate(*array_ty.ty, *array_ty.size)
            }
            ArrayExpressionInner::Repeat(box e, box count) => {
                let count = match count.into_inner() {
                    UExpressionInner::Value(from) => from as usize,
                    _ => unreachable!("should be a uint value"),
                };

                let e = e.into_canonical_constant();

                ArrayExpressionInner::Value(
                    vec![TypedExpressionOrSpread::Expression(e); count].into(),
                )
                .annotate(*array_ty.ty, *array_ty.size)
            }
            _ => unreachable!(),
        }
    }
}

impl<I: IdTrait, T: Field> Constant for StructExpression<I, T> {
    fn is_constant(&self) -> bool {
        match self.as_inner() {
            StructExpressionInner::Value(v) => v.iter().all(|e| e.is_constant()),
            _ => false,
        }
    }

    fn into_canonical_constant(self) -> Self {
        let struct_ty = self.ty().clone();

        match self.into_inner() {
            StructExpressionInner::Value(expressions) => StructExpressionInner::Value(
                expressions
                    .into_iter()
                    .map(|e| e.into_canonical_constant())
                    .collect(),
            )
            .annotate(struct_ty),
            _ => unreachable!(),
        }
    }
}

impl<I: IdTrait, T: Field> Constant for TupleExpression<I, T> {
    fn is_constant(&self) -> bool {
        match self.as_inner() {
            TupleExpressionInner::Value(v) => v.iter().all(|e| e.is_constant()),
            _ => false,
        }
    }

    fn into_canonical_constant(self) -> Self {
        let tuple_ty = self.ty().clone();

        match self.into_inner() {
            TupleExpressionInner::Value(expressions) => TupleExpressionInner::Value(
                expressions
                    .into_iter()
                    .map(|e| e.into_canonical_constant())
                    .collect(),
            )
            .annotate(tuple_ty),
            _ => unreachable!(),
        }
    }
}

impl<I: IdTrait, T: Field> Constant for TypedExpression<I, T> {
    fn is_constant(&self) -> bool {
        match self {
            TypedExpression::FieldElement(e) => e.is_constant(),
            TypedExpression::Boolean(e) => e.is_constant(),
            TypedExpression::Array(e) => e.is_constant(),
            TypedExpression::Struct(e) => e.is_constant(),
            TypedExpression::Tuple(e) => e.is_constant(),
            TypedExpression::Uint(e) => e.is_constant(),
            _ => unreachable!(),
        }
    }

    fn into_canonical_constant(self) -> Self {
        match self {
            TypedExpression::FieldElement(e) => e.into_canonical_constant().into(),
            TypedExpression::Boolean(e) => e.into_canonical_constant().into(),
            TypedExpression::Array(e) => e.into_canonical_constant().into(),
            TypedExpression::Struct(e) => e.into_canonical_constant().into(),
            TypedExpression::Tuple(e) => e.into_canonical_constant().into(),
            TypedExpression::Uint(e) => e.into_canonical_constant().into(),
            _ => unreachable!(),
        }
    }
}
