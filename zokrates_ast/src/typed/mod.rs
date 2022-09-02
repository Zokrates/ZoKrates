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
pub mod variable;

pub use self::identifier::{CoreIdentifier, ShadowedIdentifier, SourceIdentifier};
pub use self::parameter::{DeclarationParameter, GParameter};
pub use self::types::{
    CanonicalConstantIdentifier, ConcreteFunctionKey, ConcreteSignature, ConcreteTupleType,
    ConcreteType, ConstantIdentifier, DeclarationArrayType, DeclarationConstant,
    DeclarationFunctionKey, DeclarationSignature, DeclarationStructType, DeclarationType,
    GArrayType, GStructType, GType, GenericIdentifier, Signature, StructType, TupleType, Type,
    UBitwidth,
};

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
pub type TypedModules<'ast, T> = BTreeMap<OwnedTypedModuleId, TypedModule<'ast, T>>;

/// A collection of `TypedFunctionSymbol`s
/// # Remarks
/// * It is the role of the semantic checker to make sure there are no duplicates for a given `FunctionKey`
///   in a given `TypedModule`, hence the use of a BTreeMap
pub type TypedFunctionSymbols<'ast, T> =
    BTreeMap<DeclarationFunctionKey<'ast, T>, TypedFunctionSymbol<'ast, T>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypedConstantSymbol<'ast, T> {
    Here(TypedConstant<'ast, T>),
    There(CanonicalConstantIdentifier<'ast>),
}

/// A collection of `TypedConstantSymbol`s
/// It is still ordered, as we inline the constants in the order they are declared
pub type TypedConstantSymbols<'ast, T> = Vec<(
    CanonicalConstantIdentifier<'ast>,
    TypedConstantSymbol<'ast, T>,
)>;

/// A typed program as a collection of modules, one of them being the main
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct TypedProgram<'ast, T> {
    pub modules: TypedModules<'ast, T>,
    pub main: OwnedTypedModuleId,
}

impl<'ast, T: Field> TypedProgram<'ast, T> {
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
                            DeclarationConstant<'ast, T>,
                            UExpression<'ast, T>,
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
                types::try_from_g_type::<DeclarationConstant<'ast, T>, UExpression<'ast, T>>(
                    *main.signature.output.clone(),
                )
                .unwrap(),
            )
            .unwrap(),
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

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct TypedFunctionSymbolDeclaration<'ast, T> {
    pub key: DeclarationFunctionKey<'ast, T>,
    pub symbol: TypedFunctionSymbol<'ast, T>,
}

impl<'ast, T> TypedFunctionSymbolDeclaration<'ast, T> {
    pub fn new(key: DeclarationFunctionKey<'ast, T>, symbol: TypedFunctionSymbol<'ast, T>) -> Self {
        TypedFunctionSymbolDeclaration { key, symbol }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct TypedConstantSymbolDeclaration<'ast, T> {
    pub id: CanonicalConstantIdentifier<'ast>,
    pub symbol: TypedConstantSymbol<'ast, T>,
}

impl<'ast, T> TypedConstantSymbolDeclaration<'ast, T> {
    pub fn new(
        id: CanonicalConstantIdentifier<'ast>,
        symbol: TypedConstantSymbol<'ast, T>,
    ) -> Self {
        TypedConstantSymbolDeclaration { id, symbol }
    }
}

#[allow(clippy::large_enum_variant)]
#[derive(PartialEq, Eq, Debug, Clone)]
pub enum TypedSymbolDeclaration<'ast, T> {
    Function(TypedFunctionSymbolDeclaration<'ast, T>),
    Constant(TypedConstantSymbolDeclaration<'ast, T>),
}

impl<'ast, T> From<TypedFunctionSymbolDeclaration<'ast, T>> for TypedSymbolDeclaration<'ast, T> {
    fn from(d: TypedFunctionSymbolDeclaration<'ast, T>) -> Self {
        Self::Function(d)
    }
}

impl<'ast, T> From<TypedConstantSymbolDeclaration<'ast, T>> for TypedSymbolDeclaration<'ast, T> {
    fn from(d: TypedConstantSymbolDeclaration<'ast, T>) -> Self {
        Self::Constant(d)
    }
}

impl<'ast, T: fmt::Display> fmt::Display for TypedSymbolDeclaration<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TypedSymbolDeclaration::Function(fun) => write!(f, "{}", fun),
            TypedSymbolDeclaration::Constant(c) => write!(f, "{}", c),
        }
    }
}

pub type TypedSymbolDeclarations<'ast, T> = Vec<TypedSymbolDeclaration<'ast, T>>;

/// A typed module as a collection of functions. Types have been resolved during semantic checking.
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct TypedModule<'ast, T> {
    pub symbols: TypedSymbolDeclarations<'ast, T>,
}

impl<'ast, T> TypedModule<'ast, T> {
    pub fn functions_iter(&self) -> impl Iterator<Item = &TypedFunctionSymbolDeclaration<'ast, T>> {
        self.symbols.iter().filter_map(|s| match s {
            TypedSymbolDeclaration::Function(d) => Some(d),
            _ => None,
        })
    }

    pub fn into_functions_iter(
        self,
    ) -> impl Iterator<Item = TypedFunctionSymbolDeclaration<'ast, T>> {
        self.symbols.into_iter().filter_map(|s| match s {
            TypedSymbolDeclaration::Function(d) => Some(d),
            _ => None,
        })
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TypedFunctionSymbol<'ast, T> {
    Here(TypedFunction<'ast, T>),
    There(DeclarationFunctionKey<'ast, T>),
    Flat(FlatEmbed),
}

impl<'ast, T: Field> TypedFunctionSymbol<'ast, T> {
    pub fn signature<'a>(
        &'a self,
        modules: &'a TypedModules<'ast, T>,
    ) -> DeclarationSignature<'ast, T> {
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

impl<'ast, T: fmt::Display> fmt::Display for TypedConstantSymbolDeclaration<'ast, T> {
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

impl<'ast, T: fmt::Display> fmt::Display for TypedFunctionSymbolDeclaration<'ast, T> {
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

impl<'ast, T: fmt::Display> fmt::Display for TypedModule<'ast, T> {
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
pub struct TypedFunction<'ast, T> {
    /// Arguments of the function
    pub arguments: Vec<DeclarationParameter<'ast, T>>,
    /// Vector of statements that are executed when running the function
    pub statements: Vec<TypedStatement<'ast, T>>,
    /// function signature
    pub signature: DeclarationSignature<'ast, T>,
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
pub struct TypedConstant<'ast, T> {
    pub expression: TypedExpression<'ast, T>,
    pub ty: DeclarationType<'ast, T>,
}

impl<'ast, T> TypedConstant<'ast, T> {
    pub fn new(expression: TypedExpression<'ast, T>, ty: DeclarationType<'ast, T>) -> Self {
        TypedConstant { expression, ty }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for TypedConstant<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.expression)
    }
}

impl<'ast, T: Field> Typed<'ast, T> for TypedConstant<'ast, T> {
    fn get_type(&self) -> Type<'ast, T> {
        self.expression.get_type()
    }
}

/// Something we can assign to.
#[allow(clippy::large_enum_variant)]
#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub enum TypedAssignee<'ast, T> {
    Identifier(Variable<'ast, T>),
    Select(Box<TypedAssignee<'ast, T>>, Box<UExpression<'ast, T>>),
    Member(Box<TypedAssignee<'ast, T>>, MemberId),
    Element(Box<TypedAssignee<'ast, T>>, u32),
}

#[derive(Clone, PartialEq, Hash, Eq, Debug, PartialOrd, Ord)]
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

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
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

impl<'ast, T> From<TypedExpressionOrSpread<'ast, T>> for TypedExpression<'ast, T> {
    fn from(e: TypedExpressionOrSpread<'ast, T>) -> TypedExpression<'ast, T> {
        if let TypedExpressionOrSpread::Expression(e) = e {
            e
        } else {
            unreachable!("downcast failed")
        }
    }
}

impl<'ast, T> From<IntExpression<'ast, T>> for TypedExpressionOrSpread<'ast, T> {
    fn from(e: IntExpression<'ast, T>) -> Self {
        TypedExpressionOrSpread::Expression(e.into())
    }
}

impl<'ast, T> From<FieldElementExpression<'ast, T>> for TypedExpressionOrSpread<'ast, T> {
    fn from(e: FieldElementExpression<'ast, T>) -> Self {
        TypedExpressionOrSpread::Expression(e.into())
    }
}

impl<'ast, T> From<BooleanExpression<'ast, T>> for TypedExpressionOrSpread<'ast, T> {
    fn from(e: BooleanExpression<'ast, T>) -> Self {
        TypedExpressionOrSpread::Expression(e.into())
    }
}

impl<'ast, T> From<UExpression<'ast, T>> for TypedExpressionOrSpread<'ast, T> {
    fn from(e: UExpression<'ast, T>) -> Self {
        TypedExpressionOrSpread::Expression(e.into())
    }
}

impl<'ast, T> From<ArrayExpression<'ast, T>> for TypedExpressionOrSpread<'ast, T> {
    fn from(e: ArrayExpression<'ast, T>) -> Self {
        TypedExpressionOrSpread::Expression(e.into())
    }
}

impl<'ast, T> From<StructExpression<'ast, T>> for TypedExpressionOrSpread<'ast, T> {
    fn from(e: StructExpression<'ast, T>) -> Self {
        TypedExpressionOrSpread::Expression(e.into())
    }
}

impl<'ast, T> From<TupleExpression<'ast, T>> for TypedExpressionOrSpread<'ast, T> {
    fn from(e: TupleExpression<'ast, T>) -> Self {
        TypedExpressionOrSpread::Expression(e.into())
    }
}

impl<'ast, T> From<TypedExpression<'ast, T>> for TypedExpressionOrSpread<'ast, T> {
    fn from(e: TypedExpression<'ast, T>) -> Self {
        TypedExpressionOrSpread::Expression(e)
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

impl<'ast, T: fmt::Display> fmt::Display for TypedAssignee<'ast, T> {
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
pub struct EmbedCall<'ast, T> {
    pub embed: FlatEmbed,
    pub generics: Vec<u32>,
    pub arguments: Vec<TypedExpression<'ast, T>>,
}

impl<'ast, T> EmbedCall<'ast, T> {
    pub fn new(
        embed: FlatEmbed,
        generics: Vec<u32>,
        arguments: Vec<TypedExpression<'ast, T>>,
    ) -> Self {
        Self {
            embed,
            generics,
            arguments,
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for EmbedCall<'ast, T> {
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
pub enum DefinitionRhs<'ast, T> {
    Expression(TypedExpression<'ast, T>),
    EmbedCall(EmbedCall<'ast, T>),
}

impl<'ast, T> From<TypedExpression<'ast, T>> for DefinitionRhs<'ast, T> {
    fn from(e: TypedExpression<'ast, T>) -> Self {
        Self::Expression(e)
    }
}

impl<'ast, T> From<EmbedCall<'ast, T>> for DefinitionRhs<'ast, T> {
    fn from(c: EmbedCall<'ast, T>) -> Self {
        Self::EmbedCall(c)
    }
}

impl<'ast, T: fmt::Display> fmt::Display for DefinitionRhs<'ast, T> {
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
pub enum TypedStatement<'ast, T> {
    Return(TypedExpression<'ast, T>),
    Definition(TypedAssignee<'ast, T>, DefinitionRhs<'ast, T>),
    Assertion(BooleanExpression<'ast, T>, RuntimeError),
    For(
        Variable<'ast, T>,
        UExpression<'ast, T>,
        UExpression<'ast, T>,
        Vec<TypedStatement<'ast, T>>,
    ),
    Log(FormatString, Vec<TypedExpression<'ast, T>>),
    // Aux
    PushCallLog(
        DeclarationFunctionKey<'ast, T>,
        ConcreteGenericsAssignment<'ast>,
    ),
    PopCallLog,
}

impl<'ast, T> TypedStatement<'ast, T> {
    pub fn definition(a: TypedAssignee<'ast, T>, e: TypedExpression<'ast, T>) -> Self {
        Self::Definition(a, e.into())
    }

    pub fn embed_call_definition(a: TypedAssignee<'ast, T>, c: EmbedCall<'ast, T>) -> Self {
        Self::Definition(a, c.into())
    }
}

impl<'ast, T: fmt::Display> TypedStatement<'ast, T> {
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

impl<'ast, T: fmt::Display> fmt::Display for TypedStatement<'ast, T> {
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

pub trait Typed<'ast, T> {
    fn get_type(&self) -> Type<'ast, T>;
}

/// A typed expression
#[allow(clippy::large_enum_variant)]
#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub enum TypedExpression<'ast, T> {
    Boolean(BooleanExpression<'ast, T>),
    FieldElement(FieldElementExpression<'ast, T>),
    Uint(UExpression<'ast, T>),
    Array(ArrayExpression<'ast, T>),
    Struct(StructExpression<'ast, T>),
    Tuple(TupleExpression<'ast, T>),
    Int(IntExpression<'ast, T>),
}

impl<'ast, T> TypedExpression<'ast, T> {
    pub fn empty_tuple() -> TypedExpression<'ast, T> {
        TypedExpression::Tuple(TupleExpressionInner::Value(vec![]).annotate(TupleType::new(vec![])))
    }
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

impl<'ast, T> From<TupleExpression<'ast, T>> for TypedExpression<'ast, T> {
    fn from(e: TupleExpression<'ast, T>) -> TypedExpression<T> {
        TypedExpression::Tuple(e)
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
            TypedExpression::Tuple(ref t) => write!(f, "{}", t),
            TypedExpression::Int(ref s) => write!(f, "{}", s),
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for ArrayExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.inner)
    }
}

impl<'ast, T: fmt::Display> fmt::Display for StructExpression<'ast, T> {
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

impl<'ast, T: Clone> Typed<'ast, T> for TypedExpression<'ast, T> {
    fn get_type(&self) -> Type<'ast, T> {
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

impl<'ast, T: Clone> Typed<'ast, T> for ArrayExpression<'ast, T> {
    fn get_type(&self) -> Type<'ast, T> {
        Type::array(*self.ty.clone())
    }
}

impl<'ast, T: Clone> Typed<'ast, T> for TupleExpression<'ast, T> {
    fn get_type(&self) -> Type<'ast, T> {
        Type::tuple(self.ty.clone())
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
pub struct BlockExpression<'ast, T, E> {
    pub statements: Vec<TypedStatement<'ast, T>>,
    pub value: Box<E>,
}

impl<'ast, T, E> BlockExpression<'ast, T, E> {
    pub fn new(statements: Vec<TypedStatement<'ast, T>>, value: E) -> Self {
        BlockExpression {
            statements,
            value: box value,
        }
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct MemberExpression<'ast, T, E> {
    pub struc: Box<StructExpression<'ast, T>>,
    pub id: MemberId,
    ty: PhantomData<E>,
}

impl<'ast, T, E> MemberExpression<'ast, T, E> {
    pub fn new(struc: StructExpression<'ast, T>, id: MemberId) -> Self {
        MemberExpression {
            struc: box struc,
            id,
            ty: PhantomData,
        }
    }
}

impl<'ast, T: fmt::Display, E> fmt::Display for MemberExpression<'ast, T, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}.{}", self.struc, self.id)
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct SelectExpression<'ast, T, E> {
    pub array: Box<ArrayExpression<'ast, T>>,
    pub index: Box<UExpression<'ast, T>>,
    ty: PhantomData<E>,
}

impl<'ast, T, E> SelectExpression<'ast, T, E> {
    pub fn new(array: ArrayExpression<'ast, T>, index: UExpression<'ast, T>) -> Self {
        SelectExpression {
            array: box array,
            index: box index,
            ty: PhantomData,
        }
    }
}

impl<'ast, T: fmt::Display, E> fmt::Display for SelectExpression<'ast, T, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}[{}]", self.array, self.index)
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct ElementExpression<'ast, T, E> {
    pub tuple: Box<TupleExpression<'ast, T>>,
    pub index: u32,
    ty: PhantomData<E>,
}

impl<'ast, T, E> ElementExpression<'ast, T, E> {
    pub fn new(tuple: TupleExpression<'ast, T>, index: u32) -> Self {
        ElementExpression {
            tuple: box tuple,
            index,
            ty: PhantomData,
        }
    }
}

impl<'ast, T: fmt::Display, E> fmt::Display for ElementExpression<'ast, T, E> {
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
pub struct ConditionalExpression<'ast, T, E> {
    pub condition: Box<BooleanExpression<'ast, T>>,
    pub consequence: Box<E>,
    pub alternative: Box<E>,
    pub kind: ConditionalKind,
}

impl<'ast, T, E> ConditionalExpression<'ast, T, E> {
    pub fn new(
        condition: BooleanExpression<'ast, T>,
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

impl<'ast, T: fmt::Display, E: fmt::Display> fmt::Display for ConditionalExpression<'ast, T, E> {
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
pub struct FunctionCallExpression<'ast, T, E> {
    pub function_key: DeclarationFunctionKey<'ast, T>,
    pub generics: Vec<Option<UExpression<'ast, T>>>,
    pub arguments: Vec<TypedExpression<'ast, T>>,
    ty: PhantomData<E>,
}

impl<'ast, T, E> FunctionCallExpression<'ast, T, E> {
    pub fn new(
        function_key: DeclarationFunctionKey<'ast, T>,
        generics: Vec<Option<UExpression<'ast, T>>>,
        arguments: Vec<TypedExpression<'ast, T>>,
    ) -> Self {
        FunctionCallExpression {
            function_key,
            generics,
            arguments,
            ty: PhantomData,
        }
    }
}

impl<'ast, T: fmt::Display, E> fmt::Display for FunctionCallExpression<'ast, T, E> {
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
pub enum FieldElementExpression<'ast, T> {
    Block(BlockExpression<'ast, T, Self>),
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
    Conditional(ConditionalExpression<'ast, T, Self>),
    Neg(Box<FieldElementExpression<'ast, T>>),
    Pos(Box<FieldElementExpression<'ast, T>>),
    FunctionCall(FunctionCallExpression<'ast, T, Self>),
    Member(MemberExpression<'ast, T, Self>),
    Select(SelectExpression<'ast, T, Self>),
    Element(ElementExpression<'ast, T, Self>),
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
#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub enum BooleanExpression<'ast, T> {
    Block(BlockExpression<'ast, T, Self>),
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
    FieldEq(EqExpression<FieldElementExpression<'ast, T>>),
    BoolEq(EqExpression<BooleanExpression<'ast, T>>),
    ArrayEq(EqExpression<ArrayExpression<'ast, T>>),
    StructEq(EqExpression<StructExpression<'ast, T>>),
    TupleEq(EqExpression<TupleExpression<'ast, T>>),
    UintEq(EqExpression<UExpression<'ast, T>>),
    Or(
        Box<BooleanExpression<'ast, T>>,
        Box<BooleanExpression<'ast, T>>,
    ),
    And(
        Box<BooleanExpression<'ast, T>>,
        Box<BooleanExpression<'ast, T>>,
    ),
    Not(Box<BooleanExpression<'ast, T>>),
    Conditional(ConditionalExpression<'ast, T, Self>),
    Member(MemberExpression<'ast, T, Self>),
    FunctionCall(FunctionCallExpression<'ast, T, Self>),
    Select(SelectExpression<'ast, T, Self>),
    Element(ElementExpression<'ast, T, Self>),
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
#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct ArrayExpression<'ast, T> {
    pub ty: Box<ArrayType<'ast, T>>,
    pub inner: ArrayExpressionInner<'ast, T>,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, PartialOrd, Ord)]
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

impl<'ast, T: Field> ArrayValue<'ast, T> {
    fn expression_at_aux<
        U: Select<'ast, T> + From<TypedExpression<'ast, T>> + Into<TypedExpression<'ast, T>>,
    >(
        v: TypedExpressionOrSpread<'ast, T>,
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
        U: Select<'ast, T> + From<TypedExpression<'ast, T>> + Into<TypedExpression<'ast, T>>,
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

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub enum ArrayExpressionInner<'ast, T> {
    Block(BlockExpression<'ast, T, ArrayExpression<'ast, T>>),
    Identifier(Identifier<'ast>),
    Value(ArrayValue<'ast, T>),
    FunctionCall(FunctionCallExpression<'ast, T, ArrayExpression<'ast, T>>),
    Conditional(ConditionalExpression<'ast, T, ArrayExpression<'ast, T>>),
    Member(MemberExpression<'ast, T, ArrayExpression<'ast, T>>),
    Select(SelectExpression<'ast, T, ArrayExpression<'ast, T>>),
    Element(ElementExpression<'ast, T, ArrayExpression<'ast, T>>),
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
        *self.ty.size.clone()
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct StructExpression<'ast, T> {
    ty: StructType<'ast, T>,
    inner: StructExpressionInner<'ast, T>,
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

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub enum StructExpressionInner<'ast, T> {
    Block(BlockExpression<'ast, T, StructExpression<'ast, T>>),
    Identifier(Identifier<'ast>),
    Value(Vec<TypedExpression<'ast, T>>),
    FunctionCall(FunctionCallExpression<'ast, T, StructExpression<'ast, T>>),
    Conditional(ConditionalExpression<'ast, T, StructExpression<'ast, T>>),
    Member(MemberExpression<'ast, T, StructExpression<'ast, T>>),
    Select(SelectExpression<'ast, T, StructExpression<'ast, T>>),
    Element(ElementExpression<'ast, T, StructExpression<'ast, T>>),
}

impl<'ast, T> StructExpressionInner<'ast, T> {
    pub fn annotate(self, ty: StructType<'ast, T>) -> StructExpression<'ast, T> {
        StructExpression { ty, inner: self }
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct TupleExpression<'ast, T> {
    ty: TupleType<'ast, T>,
    inner: TupleExpressionInner<'ast, T>,
}

impl<'ast, T> TupleExpression<'ast, T> {
    pub fn ty(&self) -> &TupleType<'ast, T> {
        &self.ty
    }

    pub fn as_inner(&self) -> &TupleExpressionInner<'ast, T> {
        &self.inner
    }

    pub fn as_inner_mut(&mut self) -> &mut TupleExpressionInner<'ast, T> {
        &mut self.inner
    }

    pub fn into_inner(self) -> TupleExpressionInner<'ast, T> {
        self.inner
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub enum TupleExpressionInner<'ast, T> {
    Block(BlockExpression<'ast, T, TupleExpression<'ast, T>>),
    Identifier(Identifier<'ast>),
    Value(Vec<TypedExpression<'ast, T>>),
    FunctionCall(FunctionCallExpression<'ast, T, TupleExpression<'ast, T>>),
    Conditional(ConditionalExpression<'ast, T, TupleExpression<'ast, T>>),
    Member(MemberExpression<'ast, T, TupleExpression<'ast, T>>),
    Select(SelectExpression<'ast, T, TupleExpression<'ast, T>>),
    Element(ElementExpression<'ast, T, TupleExpression<'ast, T>>),
}

impl<'ast, T> TupleExpressionInner<'ast, T> {
    pub fn annotate(self, ty: TupleType<'ast, T>) -> TupleExpression<'ast, T> {
        TupleExpression { ty, inner: self }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for TupleExpression<'ast, T> {
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
impl<'ast, T> From<TypedExpression<'ast, T>> for FieldElementExpression<'ast, T> {
    fn from(te: TypedExpression<'ast, T>) -> FieldElementExpression<'ast, T> {
        match te {
            TypedExpression::FieldElement(e) => e,
            _ => unreachable!("downcast failed"),
        }
    }
}

impl<'ast, T> From<TypedExpression<'ast, T>> for BooleanExpression<'ast, T> {
    fn from(te: TypedExpression<'ast, T>) -> BooleanExpression<'ast, T> {
        match te {
            TypedExpression::Boolean(e) => e,
            _ => unreachable!("downcast failed"),
        }
    }
}

impl<'ast, T> From<TypedExpression<'ast, T>> for UExpression<'ast, T> {
    fn from(te: TypedExpression<'ast, T>) -> UExpression<'ast, T> {
        match te {
            TypedExpression::Uint(e) => e,
            _ => unreachable!("downcast failed"),
        }
    }
}

impl<'ast, T> From<TypedExpression<'ast, T>> for ArrayExpression<'ast, T> {
    fn from(te: TypedExpression<'ast, T>) -> ArrayExpression<'ast, T> {
        match te {
            TypedExpression::Array(e) => e,
            _ => unreachable!("downcast failed"),
        }
    }
}

impl<'ast, T> From<TypedExpression<'ast, T>> for IntExpression<'ast, T> {
    fn from(te: TypedExpression<'ast, T>) -> IntExpression<'ast, T> {
        match te {
            TypedExpression::Int(e) => e,
            _ => unreachable!("downcast failed"),
        }
    }
}

impl<'ast, T> From<TypedExpression<'ast, T>> for StructExpression<'ast, T> {
    fn from(te: TypedExpression<'ast, T>) -> StructExpression<'ast, T> {
        match te {
            TypedExpression::Struct(e) => e,
            _ => unreachable!("downcast failed"),
        }
    }
}

impl<'ast, T> From<TypedExpression<'ast, T>> for TupleExpression<'ast, T> {
    fn from(te: TypedExpression<'ast, T>) -> TupleExpression<'ast, T> {
        match te {
            TypedExpression::Tuple(e) => e,
            _ => unreachable!("downcast failed"),
        }
    }
}

impl<'ast, T> From<TypedConstant<'ast, T>> for FieldElementExpression<'ast, T> {
    fn from(tc: TypedConstant<'ast, T>) -> FieldElementExpression<'ast, T> {
        tc.expression.into()
    }
}

impl<'ast, T> From<TypedConstant<'ast, T>> for BooleanExpression<'ast, T> {
    fn from(tc: TypedConstant<'ast, T>) -> BooleanExpression<'ast, T> {
        tc.expression.into()
    }
}

impl<'ast, T> From<TypedConstant<'ast, T>> for UExpression<'ast, T> {
    fn from(tc: TypedConstant<'ast, T>) -> UExpression<'ast, T> {
        tc.expression.into()
    }
}

impl<'ast, T> From<TypedConstant<'ast, T>> for ArrayExpression<'ast, T> {
    fn from(tc: TypedConstant<'ast, T>) -> ArrayExpression<'ast, T> {
        tc.expression.into()
    }
}

impl<'ast, T> From<TypedConstant<'ast, T>> for StructExpression<'ast, T> {
    fn from(tc: TypedConstant<'ast, T>) -> StructExpression<'ast, T> {
        tc.expression.into()
    }
}

impl<'ast, T> From<TypedConstant<'ast, T>> for TupleExpression<'ast, T> {
    fn from(tc: TypedConstant<'ast, T>) -> TupleExpression<'ast, T> {
        tc.expression.into()
    }
}

impl<'ast, T> From<TypedConstant<'ast, T>> for IntExpression<'ast, T> {
    fn from(tc: TypedConstant<'ast, T>) -> IntExpression<'ast, T> {
        tc.expression.into()
    }
}

impl<'ast, T: fmt::Display, E: fmt::Display> fmt::Display for BlockExpression<'ast, T, E> {
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

impl<'ast, T: fmt::Display> fmt::Display for FieldElementExpression<'ast, T> {
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

impl<'ast, T: fmt::Display> fmt::Display for UExpression<'ast, T> {
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

impl<'ast, T: fmt::Display> fmt::Display for BooleanExpression<'ast, T> {
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

impl<'ast, T: fmt::Display> fmt::Display for ArrayExpressionInner<'ast, T> {
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

impl<'ast, T: Field> From<Variable<'ast, T>> for TypedExpression<'ast, T> {
    fn from(v: Variable<'ast, T>) -> Self {
        match v.get_type() {
            Type::FieldElement => FieldElementExpression::Identifier(v.id).into(),
            Type::Boolean => BooleanExpression::Identifier(v.id).into(),
            Type::Array(ty) => ArrayExpressionInner::Identifier(v.id)
                .annotate(*ty.ty, *ty.size)
                .into(),
            Type::Struct(ty) => StructExpressionInner::Identifier(v.id).annotate(ty).into(),
            Type::Tuple(ty) => TupleExpressionInner::Identifier(v.id).annotate(ty).into(),
            Type::Uint(w) => UExpressionInner::Identifier(v.id).annotate(w).into(),
            Type::Int => unreachable!(),
        }
    }
}

// Common behaviour across expressions

pub trait Expr<'ast, T>: fmt::Display + From<TypedExpression<'ast, T>> {
    type Inner;
    type Ty: Clone + IntoType<'ast, T>;

    fn ty(&self) -> &Self::Ty;

    fn into_inner(self) -> Self::Inner;

    fn as_inner(&self) -> &Self::Inner;

    fn as_inner_mut(&mut self) -> &mut Self::Inner;
}

impl<'ast, T: Field> Expr<'ast, T> for FieldElementExpression<'ast, T> {
    type Inner = Self;
    type Ty = Type<'ast, T>;

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
    type Ty = Type<'ast, T>;

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

impl<'ast, T: Field> Expr<'ast, T> for StructExpression<'ast, T> {
    type Inner = StructExpressionInner<'ast, T>;
    type Ty = StructType<'ast, T>;

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

impl<'ast, T: Field> Expr<'ast, T> for ArrayExpression<'ast, T> {
    type Inner = ArrayExpressionInner<'ast, T>;
    type Ty = ArrayType<'ast, T>;

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

impl<'ast, T: Field> Expr<'ast, T> for TupleExpression<'ast, T> {
    type Inner = TupleExpressionInner<'ast, T>;
    type Ty = TupleType<'ast, T>;

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

impl<'ast, T: Field> Expr<'ast, T> for IntExpression<'ast, T> {
    type Inner = Self;
    type Ty = Type<'ast, T>;

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

pub enum FunctionCallOrExpression<'ast, T, E: Expr<'ast, T>> {
    FunctionCall(FunctionCallExpression<'ast, T, E>),
    Expression(E::Inner),
}
pub enum SelectOrExpression<'ast, T, E: Expr<'ast, T>> {
    Select(SelectExpression<'ast, T, E>),
    Expression(E::Inner),
}

pub enum EqOrBoolean<'ast, T, E> {
    Eq(EqExpression<E>),
    Boolean(BooleanExpression<'ast, T>),
}

pub enum MemberOrExpression<'ast, T, E: Expr<'ast, T>> {
    Member(MemberExpression<'ast, T, E>),
    Expression(E::Inner),
}

pub enum ElementOrExpression<'ast, T, E: Expr<'ast, T>> {
    Element(ElementExpression<'ast, T, E>),
    Expression(E::Inner),
}

pub enum ConditionalOrExpression<'ast, T, E: Expr<'ast, T>> {
    Conditional(ConditionalExpression<'ast, T, E>),
    Expression(E::Inner),
}

pub trait Conditional<'ast, T> {
    fn conditional(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
        kind: ConditionalKind,
    ) -> Self;
}

impl<'ast, T> Conditional<'ast, T> for FieldElementExpression<'ast, T> {
    fn conditional(
        condition: BooleanExpression<'ast, T>,
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

impl<'ast, T> Conditional<'ast, T> for IntExpression<'ast, T> {
    fn conditional(
        condition: BooleanExpression<'ast, T>,
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

impl<'ast, T> Conditional<'ast, T> for BooleanExpression<'ast, T> {
    fn conditional(
        condition: BooleanExpression<'ast, T>,
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

impl<'ast, T> Conditional<'ast, T> for UExpression<'ast, T> {
    fn conditional(
        condition: BooleanExpression<'ast, T>,
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

impl<'ast, T: Clone> Conditional<'ast, T> for ArrayExpression<'ast, T> {
    fn conditional(
        condition: BooleanExpression<'ast, T>,
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

impl<'ast, T: Clone> Conditional<'ast, T> for StructExpression<'ast, T> {
    fn conditional(
        condition: BooleanExpression<'ast, T>,
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

impl<'ast, T: Clone> Conditional<'ast, T> for TupleExpression<'ast, T> {
    fn conditional(
        condition: BooleanExpression<'ast, T>,
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

pub trait Select<'ast, T> {
    fn select<I: Into<UExpression<'ast, T>>>(array: ArrayExpression<'ast, T>, index: I) -> Self;
}

impl<'ast, T> Select<'ast, T> for FieldElementExpression<'ast, T> {
    fn select<I: Into<UExpression<'ast, T>>>(array: ArrayExpression<'ast, T>, index: I) -> Self {
        FieldElementExpression::Select(SelectExpression::new(array, index.into()))
    }
}

impl<'ast, T> Select<'ast, T> for IntExpression<'ast, T> {
    fn select<I: Into<UExpression<'ast, T>>>(array: ArrayExpression<'ast, T>, index: I) -> Self {
        IntExpression::Select(SelectExpression::new(array, index.into()))
    }
}

impl<'ast, T> Select<'ast, T> for BooleanExpression<'ast, T> {
    fn select<I: Into<UExpression<'ast, T>>>(array: ArrayExpression<'ast, T>, index: I) -> Self {
        BooleanExpression::Select(SelectExpression::new(array, index.into()))
    }
}

impl<'ast, T: Field> Select<'ast, T> for TypedExpression<'ast, T> {
    fn select<I: Into<UExpression<'ast, T>>>(array: ArrayExpression<'ast, T>, index: I) -> Self {
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

impl<'ast, T: Clone> Select<'ast, T> for UExpression<'ast, T> {
    fn select<I: Into<UExpression<'ast, T>>>(array: ArrayExpression<'ast, T>, index: I) -> Self {
        let bitwidth = match array.inner_type().clone() {
            Type::Uint(bitwidth) => bitwidth,
            _ => unreachable!(),
        };

        UExpressionInner::Select(SelectExpression::new(array, index.into())).annotate(bitwidth)
    }
}

impl<'ast, T: Clone> Select<'ast, T> for ArrayExpression<'ast, T> {
    fn select<I: Into<UExpression<'ast, T>>>(array: ArrayExpression<'ast, T>, index: I) -> Self {
        let (ty, size) = match array.inner_type() {
            Type::Array(array_type) => (array_type.ty.clone(), array_type.size.clone()),
            _ => unreachable!(),
        };

        ArrayExpressionInner::Select(SelectExpression::new(array, index.into()))
            .annotate(*ty, *size)
    }
}

impl<'ast, T: Clone> Select<'ast, T> for StructExpression<'ast, T> {
    fn select<I: Into<UExpression<'ast, T>>>(array: ArrayExpression<'ast, T>, index: I) -> Self {
        let members = match array.inner_type().clone() {
            Type::Struct(members) => members,
            _ => unreachable!(),
        };

        StructExpressionInner::Select(SelectExpression::new(array, index.into())).annotate(members)
    }
}

impl<'ast, T: Clone> Select<'ast, T> for TupleExpression<'ast, T> {
    fn select<I: Into<UExpression<'ast, T>>>(array: ArrayExpression<'ast, T>, index: I) -> Self {
        let elements = match array.inner_type().clone() {
            Type::Tuple(elements) => elements,
            _ => unreachable!(),
        };

        TupleExpressionInner::Select(SelectExpression::new(array, index.into())).annotate(elements)
    }
}

pub trait Member<'ast, T>: Sized {
    fn member(s: StructExpression<'ast, T>, id: MemberId) -> Self;
}

impl<'ast, T> Member<'ast, T> for FieldElementExpression<'ast, T> {
    fn member(s: StructExpression<'ast, T>, id: MemberId) -> Self {
        FieldElementExpression::Member(MemberExpression::new(s, id))
    }
}

impl<'ast, T> Member<'ast, T> for BooleanExpression<'ast, T> {
    fn member(s: StructExpression<'ast, T>, id: MemberId) -> Self {
        BooleanExpression::Member(MemberExpression::new(s, id))
    }
}

impl<'ast, T: Clone> Member<'ast, T> for UExpression<'ast, T> {
    fn member(s: StructExpression<'ast, T>, id: MemberId) -> Self {
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

impl<'ast, T: Clone> Member<'ast, T> for ArrayExpression<'ast, T> {
    fn member(s: StructExpression<'ast, T>, id: MemberId) -> Self {
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

impl<'ast, T: Clone> Member<'ast, T> for StructExpression<'ast, T> {
    fn member(s: StructExpression<'ast, T>, id: MemberId) -> Self {
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

impl<'ast, T: Clone> Member<'ast, T> for TupleExpression<'ast, T> {
    fn member(s: StructExpression<'ast, T>, id: MemberId) -> Self {
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

pub trait Element<'ast, T>: Sized {
    fn element(s: TupleExpression<'ast, T>, id: u32) -> Self;
}

impl<'ast, T> Element<'ast, T> for FieldElementExpression<'ast, T> {
    fn element(s: TupleExpression<'ast, T>, id: u32) -> Self {
        FieldElementExpression::Element(ElementExpression::new(s, id))
    }
}

impl<'ast, T> Element<'ast, T> for BooleanExpression<'ast, T> {
    fn element(s: TupleExpression<'ast, T>, id: u32) -> Self {
        BooleanExpression::Element(ElementExpression::new(s, id))
    }
}

impl<'ast, T: Clone> Element<'ast, T> for UExpression<'ast, T> {
    fn element(s: TupleExpression<'ast, T>, id: u32) -> Self {
        let ty = &s.ty().elements[id as usize];
        let bitwidth = match ty {
            Type::Uint(bitwidth) => *bitwidth,
            _ => unreachable!(),
        };
        UExpressionInner::Element(ElementExpression::new(s, id)).annotate(bitwidth)
    }
}

impl<'ast, T: Clone> Element<'ast, T> for ArrayExpression<'ast, T> {
    fn element(s: TupleExpression<'ast, T>, id: u32) -> Self {
        let ty = &s.ty().elements[id as usize];
        let (ty, size) = match ty {
            Type::Array(array_ty) => (*array_ty.ty.clone(), array_ty.size.clone()),
            _ => unreachable!(),
        };
        ArrayExpressionInner::Element(ElementExpression::new(s, id)).annotate(ty, *size)
    }
}

impl<'ast, T: Clone> Element<'ast, T> for StructExpression<'ast, T> {
    fn element(s: TupleExpression<'ast, T>, id: u32) -> Self {
        let ty = &s.ty().elements[id as usize];
        let struct_ty = match ty {
            Type::Struct(struct_ty) => struct_ty.clone(),
            _ => unreachable!(),
        };
        StructExpressionInner::Element(ElementExpression::new(s, id)).annotate(struct_ty)
    }
}

impl<'ast, T: Clone> Element<'ast, T> for TupleExpression<'ast, T> {
    fn element(s: TupleExpression<'ast, T>, id: u32) -> Self {
        let ty = &s.ty().elements[id as usize];
        let tuple_ty = match ty {
            Type::Tuple(tuple_ty) => tuple_ty.clone(),
            _ => unreachable!(),
        };
        TupleExpressionInner::Element(ElementExpression::new(s, id)).annotate(tuple_ty)
    }
}

pub trait Id<'ast, T>: Expr<'ast, T> {
    fn identifier(id: Identifier<'ast>) -> Self::Inner;
}

impl<'ast, T: Field> Id<'ast, T> for FieldElementExpression<'ast, T> {
    fn identifier(id: Identifier<'ast>) -> Self::Inner {
        FieldElementExpression::Identifier(id)
    }
}

impl<'ast, T: Field> Id<'ast, T> for BooleanExpression<'ast, T> {
    fn identifier(id: Identifier<'ast>) -> Self::Inner {
        BooleanExpression::Identifier(id)
    }
}

impl<'ast, T: Field> Id<'ast, T> for UExpression<'ast, T> {
    fn identifier(id: Identifier<'ast>) -> Self::Inner {
        UExpressionInner::Identifier(id)
    }
}

impl<'ast, T: Field> Id<'ast, T> for ArrayExpression<'ast, T> {
    fn identifier(id: Identifier<'ast>) -> Self::Inner {
        ArrayExpressionInner::Identifier(id)
    }
}

impl<'ast, T: Field> Id<'ast, T> for StructExpression<'ast, T> {
    fn identifier(id: Identifier<'ast>) -> Self::Inner {
        StructExpressionInner::Identifier(id)
    }
}

impl<'ast, T: Field> Id<'ast, T> for TupleExpression<'ast, T> {
    fn identifier(id: Identifier<'ast>) -> Self::Inner {
        TupleExpressionInner::Identifier(id)
    }
}

pub trait FunctionCall<'ast, T>: Expr<'ast, T> {
    fn function_call(
        key: DeclarationFunctionKey<'ast, T>,
        generics: Vec<Option<UExpression<'ast, T>>>,
        arguments: Vec<TypedExpression<'ast, T>>,
    ) -> Self::Inner;
}

impl<'ast, T: Field> FunctionCall<'ast, T> for FieldElementExpression<'ast, T> {
    fn function_call(
        key: DeclarationFunctionKey<'ast, T>,
        generics: Vec<Option<UExpression<'ast, T>>>,
        arguments: Vec<TypedExpression<'ast, T>>,
    ) -> Self::Inner {
        FieldElementExpression::FunctionCall(FunctionCallExpression::new(key, generics, arguments))
    }
}

impl<'ast, T: Field> FunctionCall<'ast, T> for BooleanExpression<'ast, T> {
    fn function_call(
        key: DeclarationFunctionKey<'ast, T>,
        generics: Vec<Option<UExpression<'ast, T>>>,
        arguments: Vec<TypedExpression<'ast, T>>,
    ) -> Self::Inner {
        BooleanExpression::FunctionCall(FunctionCallExpression::new(key, generics, arguments))
    }
}

impl<'ast, T: Field> FunctionCall<'ast, T> for UExpression<'ast, T> {
    fn function_call(
        key: DeclarationFunctionKey<'ast, T>,
        generics: Vec<Option<UExpression<'ast, T>>>,
        arguments: Vec<TypedExpression<'ast, T>>,
    ) -> Self::Inner {
        UExpressionInner::FunctionCall(FunctionCallExpression::new(key, generics, arguments))
    }
}

impl<'ast, T: Field> FunctionCall<'ast, T> for ArrayExpression<'ast, T> {
    fn function_call(
        key: DeclarationFunctionKey<'ast, T>,
        generics: Vec<Option<UExpression<'ast, T>>>,
        arguments: Vec<TypedExpression<'ast, T>>,
    ) -> Self::Inner {
        ArrayExpressionInner::FunctionCall(FunctionCallExpression::new(key, generics, arguments))
    }
}

impl<'ast, T: Field> FunctionCall<'ast, T> for TupleExpression<'ast, T> {
    fn function_call(
        key: DeclarationFunctionKey<'ast, T>,
        generics: Vec<Option<UExpression<'ast, T>>>,
        arguments: Vec<TypedExpression<'ast, T>>,
    ) -> Self::Inner {
        TupleExpressionInner::FunctionCall(FunctionCallExpression::new(key, generics, arguments))
    }
}

impl<'ast, T: Field> FunctionCall<'ast, T> for StructExpression<'ast, T> {
    fn function_call(
        key: DeclarationFunctionKey<'ast, T>,
        generics: Vec<Option<UExpression<'ast, T>>>,
        arguments: Vec<TypedExpression<'ast, T>>,
    ) -> Self::Inner {
        StructExpressionInner::FunctionCall(FunctionCallExpression::new(key, generics, arguments))
    }
}

pub trait Block<'ast, T> {
    fn block(statements: Vec<TypedStatement<'ast, T>>, value: Self) -> Self;
}

impl<'ast, T: Field> Block<'ast, T> for FieldElementExpression<'ast, T> {
    fn block(statements: Vec<TypedStatement<'ast, T>>, value: Self) -> Self {
        FieldElementExpression::Block(BlockExpression::new(statements, value))
    }
}

impl<'ast, T: Field> Block<'ast, T> for BooleanExpression<'ast, T> {
    fn block(statements: Vec<TypedStatement<'ast, T>>, value: Self) -> Self {
        BooleanExpression::Block(BlockExpression::new(statements, value))
    }
}

impl<'ast, T: Field> Block<'ast, T> for UExpression<'ast, T> {
    fn block(statements: Vec<TypedStatement<'ast, T>>, value: Self) -> Self {
        let bitwidth = value.bitwidth();
        UExpressionInner::Block(BlockExpression::new(statements, value)).annotate(bitwidth)
    }
}

impl<'ast, T: Field> Block<'ast, T> for ArrayExpression<'ast, T> {
    fn block(statements: Vec<TypedStatement<'ast, T>>, value: Self) -> Self {
        let array_ty = value.ty().clone();
        ArrayExpressionInner::Block(BlockExpression::new(statements, value))
            .annotate(*array_ty.ty, *array_ty.size)
    }
}

impl<'ast, T: Field> Block<'ast, T> for TupleExpression<'ast, T> {
    fn block(statements: Vec<TypedStatement<'ast, T>>, value: Self) -> Self {
        let tuple_ty = value.ty().clone();
        TupleExpressionInner::Block(BlockExpression::new(statements, value)).annotate(tuple_ty)
    }
}

impl<'ast, T: Field> Block<'ast, T> for StructExpression<'ast, T> {
    fn block(statements: Vec<TypedStatement<'ast, T>>, value: Self) -> Self {
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

impl<'ast, T: Field> Constant for FieldElementExpression<'ast, T> {
    fn is_constant(&self) -> bool {
        matches!(self, FieldElementExpression::Number(..))
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

impl<'ast, T: Field> Constant for ArrayExpression<'ast, T> {
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
        fn into_canonical_constant_aux<T: Field>(
            e: TypedExpressionOrSpread<T>,
        ) -> Vec<TypedExpression<T>> {
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

impl<'ast, T: Field> Constant for StructExpression<'ast, T> {
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

impl<'ast, T: Field> Constant for TupleExpression<'ast, T> {
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

impl<'ast, T: Field> Constant for TypedExpression<'ast, T> {
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
