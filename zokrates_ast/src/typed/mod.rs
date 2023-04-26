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
pub mod utils;
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
use self::types::{ConcreteArrayType, ConcreteStructType};

use crate::common::expressions::{
    self, BinaryExpression, BooleanValueExpression, FieldValueExpression, UnaryExpression,
    ValueExpression,
};
use crate::common::{self, ModuleMap, Span, Value, WithSpan};
pub use crate::common::{ModuleId, OwnedModuleId};
use crate::typed::types::IntoType;

pub use self::variable::{ConcreteVariable, DeclarationVariable, GVariable, Variable};
use std::marker::PhantomData;
use std::ops::Deref;

pub use crate::typed::integer::IntExpression;
pub use crate::typed::uint::{bitwidth, UExpression, UExpressionInner, UMetadata};

use crate::common::{operators::*, FlatEmbed, FormatString, SourceMetadata};

use std::collections::BTreeMap;
use std::convert::{TryFrom, TryInto};
use std::fmt;

pub use crate::typed::types::{ArrayType, FunctionKey, MemberId};

use derivative::Derivative;
use num_bigint::BigUint;
use zokrates_field::Field;

pub use self::folder::Folder;
use crate::typed::abi::{Abi, AbiInput};

pub use self::identifier::Identifier;

/// A collection of `TypedModule`s
pub type TypedModules<'ast, T> = BTreeMap<OwnedModuleId, TypedModule<'ast, T>>;

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
#[derive(PartialEq, Eq, Debug, Clone, Default)]
pub struct TypedProgram<'ast, T> {
    pub module_map: ModuleMap,
    pub modules: TypedModules<'ast, T>,
    pub main: OwnedModuleId,
}

pub type IdentifierOrExpression<'ast, T, E> =
    expressions::IdentifierOrExpression<Identifier<'ast>, E, <E as Expr<'ast, T>>::Inner>;

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
                        >(p.id.ty.clone())
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

        for s in &self.statements {
            writeln!(f, "{}", s)?;
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

impl<'ast, T> TypedAssignee<'ast, T> {
    pub fn select(self, index: UExpression<'ast, T>) -> Self {
        Self::Select(Box::new(self), Box::new(index))
    }

    pub fn member(self, member: MemberId) -> Self {
        Self::Member(Box::new(self), member)
    }

    pub fn element(self, index: u32) -> Self {
        Self::Element(Box::new(self), index)
    }
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
            TypedExpressionOrSpread::Expression(ref e) => write!(f, "{}", e),
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

#[derive(Debug, Clone, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub enum RuntimeError {
    SourceAssertion(SourceMetadata),
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
            DefinitionRhs::Expression(ref e) => write!(f, "{}", e),
        }
    }
}

pub type DefinitionStatement<'ast, T> =
    common::statements::DefinitionStatement<TypedAssignee<'ast, T>, DefinitionRhs<'ast, T>>;
pub type AssertionStatement<'ast, T> =
    common::statements::AssertionStatement<BooleanExpression<'ast, T>, RuntimeError>;
pub type ReturnStatement<'ast, T> = common::statements::ReturnStatement<TypedExpression<'ast, T>>;
pub type LogStatement<'ast, T> = common::statements::LogStatement<TypedExpression<'ast, T>>;

#[derive(Derivative)]
#[derivative(PartialOrd, PartialEq, Eq, Hash, Ord)]
#[derive(Clone, Debug)]
pub struct ForStatement<'ast, T> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub var: Variable<'ast, T>,
    pub from: UExpression<'ast, T>,
    pub to: UExpression<'ast, T>,
    pub statements: Vec<TypedStatement<'ast, T>>,
}

impl<'ast, T> ForStatement<'ast, T> {
    fn new(
        var: Variable<'ast, T>,
        from: UExpression<'ast, T>,
        to: UExpression<'ast, T>,
        statements: Vec<TypedStatement<'ast, T>>,
    ) -> Self {
        Self {
            span: None,
            var,
            from,
            to,
            statements,
        }
    }
}

impl<'ast, T> WithSpan for ForStatement<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        Self { span, ..self }
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

#[derive(Derivative)]
#[derivative(PartialOrd, PartialEq, Eq, Hash, Ord)]
#[derive(Clone, Debug)]
pub struct AssemblyBlockStatement<'ast, T> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub inner: Vec<TypedAssemblyStatement<'ast, T>>,
}

impl<'ast, T> AssemblyBlockStatement<'ast, T> {
    pub fn new(inner: Vec<TypedAssemblyStatement<'ast, T>>) -> Self {
        Self { span: None, inner }
    }
}

pub type AssemblyConstraint<'ast, T> =
    crate::common::statements::AssemblyConstraint<FieldElementExpression<'ast, T>>;
pub type AssemblyAssignment<'ast, T> =
    crate::common::statements::AssemblyAssignment<TypedAssignee<'ast, T>, TypedExpression<'ast, T>>;

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub enum TypedAssemblyStatement<'ast, T> {
    Assignment(AssemblyAssignment<'ast, T>),
    Constraint(AssemblyConstraint<'ast, T>),
}

impl<'ast, T> WithSpan for TypedAssemblyStatement<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        match self {
            TypedAssemblyStatement::Assignment(s) => {
                TypedAssemblyStatement::Assignment(s.span(span))
            }
            TypedAssemblyStatement::Constraint(s) => {
                TypedAssemblyStatement::Constraint(s.span(span))
            }
        }
    }

    fn get_span(&self) -> Option<Span> {
        match self {
            TypedAssemblyStatement::Assignment(s) => s.get_span(),
            TypedAssemblyStatement::Constraint(s) => s.get_span(),
        }
    }
}

impl<'ast, T> TypedAssemblyStatement<'ast, T> {
    pub fn assignment(
        assignee: TypedAssignee<'ast, T>,
        expression: TypedExpression<'ast, T>,
    ) -> Self {
        TypedAssemblyStatement::Assignment(AssemblyAssignment::new(assignee, expression))
    }

    pub fn constraint(
        left: FieldElementExpression<'ast, T>,
        right: FieldElementExpression<'ast, T>,
        metadata: SourceMetadata,
    ) -> Self {
        TypedAssemblyStatement::Constraint(AssemblyConstraint::new(left, right, metadata))
    }
}

impl<'ast, T: fmt::Display> fmt::Display for TypedAssemblyStatement<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedAssemblyStatement::Assignment(ref s) => {
                write!(f, "{} <-- {};", s.assignee, s.expression)
            }
            TypedAssemblyStatement::Constraint(ref s) => {
                write!(f, "{}", s)
            }
        }
    }
}

impl<'ast, T> WithSpan for AssemblyBlockStatement<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        Self { span, ..self }
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

/// A statement in a `TypedFunction`
#[allow(clippy::large_enum_variant)]
#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub enum TypedStatement<'ast, T> {
    Return(ReturnStatement<'ast, T>),
    Definition(DefinitionStatement<'ast, T>),
    Assertion(AssertionStatement<'ast, T>),
    For(ForStatement<'ast, T>),
    Log(LogStatement<'ast, T>),
    Assembly(AssemblyBlockStatement<'ast, T>),
}

impl<'ast, T> WithSpan for TypedStatement<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        use TypedStatement::*;

        match self {
            Return(e) => Return(e.span(span)),
            Definition(e) => Definition(e.span(span)),
            Assertion(e) => Assertion(e.span(span)),
            For(e) => For(e.span(span)),
            Log(e) => Log(e.span(span)),
            Assembly(e) => Assembly(e.span(span)),
        }
    }

    fn get_span(&self) -> Option<Span> {
        use TypedStatement::*;

        match self {
            Return(e) => e.get_span(),
            Definition(e) => e.get_span(),
            Assertion(e) => e.get_span(),
            For(e) => e.get_span(),
            Log(e) => e.get_span(),
            Assembly(e) => e.get_span(),
        }
    }
}

impl<'ast, T> TypedStatement<'ast, T> {
    pub fn definition(a: TypedAssignee<'ast, T>, e: TypedExpression<'ast, T>) -> Self {
        Self::Definition(DefinitionStatement::new(a, e.into()))
    }

    pub fn for_(
        var: Variable<'ast, T>,
        from: UExpression<'ast, T>,
        to: UExpression<'ast, T>,
        statements: Vec<TypedStatement<'ast, T>>,
    ) -> Self {
        Self::For(ForStatement::new(var, from, to, statements))
    }

    pub fn assertion(e: BooleanExpression<'ast, T>, error: RuntimeError) -> Self {
        Self::Assertion(AssertionStatement::new(e, error))
    }

    pub fn ret(e: TypedExpression<'ast, T>) -> Self {
        Self::Return(ReturnStatement::new(e))
    }

    pub fn embed_call_definition(a: TypedAssignee<'ast, T>, c: EmbedCall<'ast, T>) -> Self {
        Self::Definition(DefinitionStatement::new(a, c.into()))
    }

    pub fn log(format_string: FormatString, expressions: Vec<TypedExpression<'ast, T>>) -> Self {
        Self::Log(LogStatement::new(format_string, expressions))
    }
}

impl<'ast, T: fmt::Display> fmt::Display for TypedStatement<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedStatement::Return(ref s) => {
                write!(f, "{}", s)
            }
            TypedStatement::Definition(ref s) => write!(f, "{}", s),
            TypedStatement::Assertion(ref s) => {
                write!(f, "assert({}", s.expression)?;
                match s.error {
                    RuntimeError::SourceAssertion(ref metadata) => match &metadata.message {
                        Some(m) => write!(f, ", \"{}\");", m),
                        None => write!(f, ");"),
                    },
                    ref error => write!(f, "); // {}", error),
                }
            }
            TypedStatement::For(ref s) => {
                writeln!(f, "for {} in {}..{} {{", s.var, s.from, s.to)?;
                for l in &s.statements {
                    writeln!(f, "\t\t{}", l)?;
                }
                write!(f, "\t}}")
            }
            TypedStatement::Log(ref s) => write!(f, "{}", s),
            TypedStatement::Assembly(ref s) => {
                writeln!(f, "asm {{")?;
                for s in &s.inner {
                    writeln!(f, "\t\t{}", s)?;
                }
                write!(f, "\t}}")
            }
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

impl<'ast, T: Field> TypedExpression<'ast, T> {
    pub fn empty_tuple() -> TypedExpression<'ast, T> {
        TypedExpression::Tuple(TupleExpression::value(vec![]).annotate(TupleType::new(vec![])))
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

#[derive(Derivative)]
#[derivative(PartialOrd, PartialEq, Eq, Hash, Ord)]
#[derive(Clone, Debug)]
pub struct BlockExpression<'ast, T, E> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub statements: Vec<TypedStatement<'ast, T>>,
    pub value: Box<E>,
}

impl<'ast, T, E> BlockExpression<'ast, T, E> {
    pub fn new(statements: Vec<TypedStatement<'ast, T>>, value: E) -> Self {
        BlockExpression {
            span: None,
            statements,
            value: Box::new(value),
        }
    }
}

#[derive(Derivative)]
#[derivative(PartialOrd, PartialEq, Eq, Hash, Ord)]
#[derive(Clone, Debug)]
pub struct SliceExpression<'ast, T> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub array: Box<ArrayExpression<'ast, T>>,
    pub from: Box<UExpression<'ast, T>>,
    pub to: Box<UExpression<'ast, T>>,
}

impl<'ast, T> SliceExpression<'ast, T> {
    pub fn new(
        array: ArrayExpression<'ast, T>,
        from: UExpression<'ast, T>,
        to: UExpression<'ast, T>,
    ) -> Self {
        SliceExpression {
            span: None,
            array: Box::new(array),
            from: Box::new(from),
            to: Box::new(to),
        }
    }
}

impl<'ast, T> WithSpan for SliceExpression<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        Self { span, ..self }
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

impl<'ast, T: fmt::Display> fmt::Display for SliceExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}[{}..{}]", self.array, self.from, self.to)
    }
}

#[derive(Derivative)]
#[derivative(PartialOrd, PartialEq, Eq, Hash, Ord)]
#[derive(Clone, Debug)]
pub struct RepeatExpression<'ast, T> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub count: Box<UExpression<'ast, T>>,
    pub e: Box<TypedExpression<'ast, T>>,
}

impl<'ast, T> RepeatExpression<'ast, T> {
    pub fn new(e: TypedExpression<'ast, T>, count: UExpression<'ast, T>) -> Self {
        RepeatExpression {
            span: None,
            e: Box::new(e),
            count: Box::new(count),
        }
    }
}

impl<'ast, T> WithSpan for RepeatExpression<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        Self { span, ..self }
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

impl<'ast, T: fmt::Display> fmt::Display for RepeatExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}; {}]", self.e, self.count)
    }
}

pub type IdentifierExpression<'ast, E> = expressions::IdentifierExpression<Identifier<'ast>, E>;

#[derive(Derivative)]
#[derivative(PartialOrd, PartialEq, Eq, Hash, Ord)]
#[derive(Clone, Debug)]
pub struct MemberExpression<'ast, T, E> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub struc: Box<StructExpression<'ast, T>>,
    pub id: MemberId,
    ty: PhantomData<E>,
}

impl<'ast, T, E> MemberExpression<'ast, T, E> {
    pub fn new(struc: StructExpression<'ast, T>, id: MemberId) -> Self {
        MemberExpression {
            span: None,
            struc: Box::new(struc),
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

#[derive(Derivative)]
#[derivative(PartialOrd, PartialEq, Eq, Hash, Ord)]
#[derive(Clone, Debug)]
pub struct SelectExpression<'ast, T, E> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub array: Box<ArrayExpression<'ast, T>>,
    pub index: Box<UExpression<'ast, T>>,
    ty: PhantomData<E>,
}

impl<'ast, T, E> SelectExpression<'ast, T, E> {
    pub fn new(array: ArrayExpression<'ast, T>, index: UExpression<'ast, T>) -> Self {
        SelectExpression {
            span: None,
            array: Box::new(array),
            index: Box::new(index),
            ty: PhantomData,
        }
    }
}

impl<'ast, T: fmt::Display, E> fmt::Display for SelectExpression<'ast, T, E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}[{}]", self.array, self.index)
    }
}

#[derive(Derivative)]
#[derivative(PartialOrd, PartialEq, Eq, Hash, Ord)]
#[derive(Clone, Debug)]
pub struct ElementExpression<'ast, T, E> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub tuple: Box<TupleExpression<'ast, T>>,
    pub index: u32,
    ty: PhantomData<E>,
}

impl<'ast, T, E> ElementExpression<'ast, T, E> {
    pub fn new(tuple: TupleExpression<'ast, T>, index: u32) -> Self {
        ElementExpression {
            span: None,
            tuple: Box::new(tuple),
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

#[derive(Derivative)]
#[derivative(PartialOrd, PartialEq, Eq, Hash, Ord)]
#[derive(Clone, Debug)]
pub struct ConditionalExpression<'ast, T, E> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
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
            span: None,
            condition: Box::new(condition),
            consequence: Box::new(consequence),
            alternative: Box::new(alternative),
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

#[derive(Derivative)]
#[derivative(PartialOrd, PartialEq, Eq, Hash, Ord)]
#[derive(Clone, Debug)]
pub struct FunctionCallExpression<'ast, T, E> {
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
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
            span: None,
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
    Value(FieldValueExpression<T>),
    Identifier(IdentifierExpression<'ast, Self>),
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
    Conditional(ConditionalExpression<'ast, T, Self>),
    Neg(UnaryExpression<OpNeg, Self, Self>),
    Pos(UnaryExpression<OpPos, Self, Self>),
    FunctionCall(FunctionCallExpression<'ast, T, Self>),
    Member(MemberExpression<'ast, T, Self>),
    Select(SelectExpression<'ast, T, Self>),
    Element(ElementExpression<'ast, T, Self>),
}

impl<'ast, T: Field> From<TypedAssignee<'ast, T>> for TupleExpression<'ast, T> {
    fn from(assignee: TypedAssignee<'ast, T>) -> Self {
        match assignee {
            TypedAssignee::Identifier(v) => {
                let inner = TupleExpression::identifier(v.id);
                match v.ty {
                    GType::Tuple(tuple_ty) => inner.annotate(tuple_ty),
                    _ => unreachable!(),
                }
            }
            TypedAssignee::Select(a, index) => TupleExpression::select((*a).into(), *index),
            TypedAssignee::Member(a, id) => TupleExpression::member((*a).into(), id),
            TypedAssignee::Element(a, index) => TupleExpression::element((*a).into(), index),
        }
    }
}

impl<'ast, T: Field> From<TypedAssignee<'ast, T>> for StructExpression<'ast, T> {
    fn from(assignee: TypedAssignee<'ast, T>) -> Self {
        match assignee {
            TypedAssignee::Identifier(v) => {
                let inner = StructExpression::identifier(v.id);
                match v.ty {
                    GType::Struct(struct_ty) => inner.annotate(struct_ty),
                    _ => unreachable!(),
                }
            }
            TypedAssignee::Select(a, index) => StructExpression::select((*a).into(), *index),
            TypedAssignee::Member(a, id) => StructExpression::member((*a).into(), id),
            TypedAssignee::Element(a, index) => StructExpression::element((*a).into(), index),
        }
    }
}

impl<'ast, T: Field> From<TypedAssignee<'ast, T>> for ArrayExpression<'ast, T> {
    fn from(assignee: TypedAssignee<'ast, T>) -> Self {
        match assignee {
            TypedAssignee::Identifier(v) => {
                let inner = ArrayExpression::identifier(v.id);
                match v.ty {
                    GType::Array(array_ty) => inner.annotate(array_ty),
                    _ => unreachable!(),
                }
            }
            TypedAssignee::Select(a, index) => ArrayExpression::select((*a).into(), *index),
            TypedAssignee::Member(a, id) => ArrayExpression::member((*a).into(), id),
            TypedAssignee::Element(a, index) => ArrayExpression::element((*a).into(), index),
        }
    }
}

impl<'ast, T: Field> From<TypedAssignee<'ast, T>> for FieldElementExpression<'ast, T> {
    fn from(assignee: TypedAssignee<'ast, T>) -> Self {
        match assignee {
            TypedAssignee::Identifier(v) => FieldElementExpression::identifier(v.id),
            TypedAssignee::Element(a, index) => FieldElementExpression::element((*a).into(), index),
            TypedAssignee::Member(a, id) => FieldElementExpression::member((*a).into(), id),
            TypedAssignee::Select(a, index) => FieldElementExpression::select((*a).into(), *index),
        }
    }
}

impl<'ast, T> std::ops::Add for FieldElementExpression<'ast, T> {
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

impl<'ast, T> std::ops::Neg for FieldElementExpression<'ast, T> {
    type Output = Self;

    fn neg(self) -> Self {
        FieldElementExpression::Neg(UnaryExpression::new(self))
    }
}

impl<'ast, T: Field> FieldElementExpression<'ast, T> {
    pub fn pow(self, other: UExpression<'ast, T>) -> Self {
        FieldElementExpression::Pow(BinaryExpression::new(self, other))
    }

    pub fn pos(self) -> Self {
        FieldElementExpression::Pos(UnaryExpression::new(self))
    }

    pub fn left_shift(self, by: UExpression<'ast, T>) -> Self {
        FieldElementExpression::LeftShift(BinaryExpression::new(self, by))
    }

    pub fn right_shift(self, by: UExpression<'ast, T>) -> Self {
        FieldElementExpression::RightShift(BinaryExpression::new(self, by))
    }
}

impl<'ast, T: Clone> From<T> for FieldElementExpression<'ast, T> {
    fn from(n: T) -> Self {
        FieldElementExpression::Value(ValueExpression::new(n))
    }
}

/// An expression of type `bool`
#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub enum BooleanExpression<'ast, T> {
    Block(BlockExpression<'ast, T, Self>),
    Identifier(IdentifierExpression<'ast, Self>),
    Value(BooleanValueExpression),
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
    UintLt(BinaryExpression<OpLt, UExpression<'ast, T>, UExpression<'ast, T>, Self>),
    UintLe(BinaryExpression<OpLe, UExpression<'ast, T>, UExpression<'ast, T>, Self>),
    FieldEq(
        BinaryExpression<
            OpEq,
            FieldElementExpression<'ast, T>,
            FieldElementExpression<'ast, T>,
            Self,
        >,
    ),
    BoolEq(BinaryExpression<OpEq, BooleanExpression<'ast, T>, BooleanExpression<'ast, T>, Self>),
    ArrayEq(BinaryExpression<OpEq, ArrayExpression<'ast, T>, ArrayExpression<'ast, T>, Self>),
    StructEq(BinaryExpression<OpEq, StructExpression<'ast, T>, StructExpression<'ast, T>, Self>),
    TupleEq(BinaryExpression<OpEq, TupleExpression<'ast, T>, TupleExpression<'ast, T>, Self>),
    UintEq(BinaryExpression<OpEq, UExpression<'ast, T>, UExpression<'ast, T>, Self>),
    Or(BinaryExpression<OpOr, BooleanExpression<'ast, T>, BooleanExpression<'ast, T>, Self>),
    And(BinaryExpression<OpAnd, BooleanExpression<'ast, T>, BooleanExpression<'ast, T>, Self>),
    Not(UnaryExpression<OpNot, Self, Self>),
    Conditional(ConditionalExpression<'ast, T, Self>),
    Member(MemberExpression<'ast, T, Self>),
    FunctionCall(FunctionCallExpression<'ast, T, Self>),
    Select(SelectExpression<'ast, T, Self>),
    Element(ElementExpression<'ast, T, Self>),
}

impl<'ast, T> From<bool> for BooleanExpression<'ast, T> {
    fn from(b: bool) -> Self {
        BooleanExpression::Value(ValueExpression::new(b))
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

    pub fn struct_eq(left: StructExpression<'ast, T>, right: StructExpression<'ast, T>) -> Self {
        Self::StructEq(BinaryExpression::new(left, right))
    }

    pub fn array_eq(left: ArrayExpression<'ast, T>, right: ArrayExpression<'ast, T>) -> Self {
        Self::ArrayEq(BinaryExpression::new(left, right))
    }

    pub fn tuple_eq(left: TupleExpression<'ast, T>, right: TupleExpression<'ast, T>) -> Self {
        Self::TupleEq(BinaryExpression::new(left, right))
    }

    pub fn uint_lt(left: UExpression<'ast, T>, right: UExpression<'ast, T>) -> Self {
        Self::UintLt(BinaryExpression::new(left, right))
    }

    pub fn uint_le(left: UExpression<'ast, T>, right: UExpression<'ast, T>) -> Self {
        Self::UintLe(BinaryExpression::new(left, right))
    }

    pub fn uint_gt(left: UExpression<'ast, T>, right: UExpression<'ast, T>) -> Self {
        Self::UintLt(BinaryExpression::new(right, left))
    }

    pub fn uint_ge(left: UExpression<'ast, T>, right: UExpression<'ast, T>) -> Self {
        Self::UintLe(BinaryExpression::new(right, left))
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

    pub fn field_gt(
        left: FieldElementExpression<'ast, T>,
        right: FieldElementExpression<'ast, T>,
    ) -> Self {
        Self::FieldLt(BinaryExpression::new(right, left))
    }

    pub fn field_ge(
        left: FieldElementExpression<'ast, T>,
        right: FieldElementExpression<'ast, T>,
    ) -> Self {
        Self::FieldLe(BinaryExpression::new(right, left))
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

type ArrayValueExpression<'ast, T> = ValueExpression<Vec<TypedExpressionOrSpread<'ast, T>>>;

impl<'ast, T> IntoIterator for ArrayValueExpression<'ast, T> {
    type Item = TypedExpressionOrSpread<'ast, T>;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.value.into_iter()
    }
}

impl<'ast, T> Deref for ArrayValueExpression<'ast, T> {
    type Target = [TypedExpressionOrSpread<'ast, T>];

    fn deref(&self) -> &Self::Target {
        &self.value[..]
    }
}

impl<'ast, T> std::iter::FromIterator<TypedExpressionOrSpread<'ast, T>>
    for ArrayValueExpression<'ast, T>
{
    fn from_iter<I: IntoIterator<Item = TypedExpressionOrSpread<'ast, T>>>(iter: I) -> Self {
        Self::new(iter.into_iter().collect())
    }
}

impl<'ast, T: Field> ArrayValueExpression<'ast, T> {
    fn expression_at_aux<
        'a,
        U: Select<'ast, T> + From<TypedExpression<'ast, T>> + Into<TypedExpression<'ast, T>>,
    >(
        v: TypedExpressionOrSpread<'ast, T>,
    ) -> Vec<TypedExpression<'ast, T>> {
        match v {
            TypedExpressionOrSpread::Expression(e) => vec![e],
            TypedExpressionOrSpread::Spread(s) => match s.array.size().into_inner() {
                UExpressionInner::Value(size) => {
                    let array_ty = s.array.ty().clone();

                    match s.array.into_inner() {
                        ArrayExpressionInner::Value(v) => v
                            .value
                            .into_iter()
                            .flat_map(Self::expression_at_aux::<U>)
                            .collect(),
                        a => (0..size.value)
                            .map(|i| {
                                U::select(a.clone().annotate(array_ty.clone()), i as u32).into()
                            })
                            .collect(),
                    }
                }
                _ => unreachable!(),
            },
        }
    }

    pub fn expression_at<
        U: Select<'ast, T> + From<TypedExpression<'ast, T>> + Into<TypedExpression<'ast, T>>,
    >(
        self,
        index: usize,
    ) -> U {
        self.into_iter()
            .flat_map(|v| Self::expression_at_aux::<U>(v))
            .nth(index)
            .unwrap()
            .clone()
            .try_into()
            .unwrap()
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub enum ArrayExpressionInner<'ast, T> {
    Block(BlockExpression<'ast, T, ArrayExpression<'ast, T>>),
    Identifier(IdentifierExpression<'ast, ArrayExpression<'ast, T>>),
    Value(ArrayValueExpression<'ast, T>),
    FunctionCall(FunctionCallExpression<'ast, T, ArrayExpression<'ast, T>>),
    Conditional(ConditionalExpression<'ast, T, ArrayExpression<'ast, T>>),
    Member(MemberExpression<'ast, T, ArrayExpression<'ast, T>>),
    Select(SelectExpression<'ast, T, ArrayExpression<'ast, T>>),
    Element(ElementExpression<'ast, T, ArrayExpression<'ast, T>>),
    Slice(SliceExpression<'ast, T>),
    Repeat(RepeatExpression<'ast, T>),
}

impl<'ast, T> ArrayExpressionInner<'ast, T> {
    pub fn annotate(self, ty: ArrayType<'ast, T>) -> ArrayExpression<'ast, T> {
        ArrayExpression {
            ty: Box::new(ty),
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

    pub fn slice(
        array: ArrayExpression<'ast, T>,
        from: UExpression<'ast, T>,
        to: UExpression<'ast, T>,
    ) -> Self {
        let inner = array.inner_type().clone();
        let size = to.clone() - from.clone();
        let array_ty = ArrayType::new(inner, size);
        ArrayExpressionInner::Slice(SliceExpression::new(array, from, to)).annotate(array_ty)
    }

    pub fn repeat(e: TypedExpression<'ast, T>, count: UExpression<'ast, T>) -> Self {
        let inner = e.get_type().clone();
        let size = count.clone();
        let array_ty = ArrayType::new(inner, size);
        ArrayExpressionInner::Repeat(RepeatExpression::new(e, count)).annotate(array_ty)
    }
}

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub struct StructExpression<'ast, T> {
    ty: StructType<'ast, T>,
    inner: StructExpressionInner<'ast, T>,
}

type StructValueExpression<'ast, T> = ValueExpression<Vec<TypedExpression<'ast, T>>>;

impl<'ast, T> IntoIterator for StructValueExpression<'ast, T> {
    type Item = TypedExpression<'ast, T>;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.value.into_iter()
    }
}

impl<'ast, T> Deref for StructValueExpression<'ast, T> {
    type Target = [TypedExpression<'ast, T>];

    fn deref(&self) -> &Self::Target {
        &self.value[..]
    }
}

impl<'ast, T> std::iter::FromIterator<TypedExpression<'ast, T>> for StructValueExpression<'ast, T> {
    fn from_iter<I: IntoIterator<Item = TypedExpression<'ast, T>>>(iter: I) -> Self {
        Self::new(iter.into_iter().collect())
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

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub enum StructExpressionInner<'ast, T> {
    Block(BlockExpression<'ast, T, StructExpression<'ast, T>>),
    Identifier(IdentifierExpression<'ast, StructExpression<'ast, T>>),
    Value(TupleValueExpression<'ast, T>),
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

type TupleValueExpression<'ast, T> = ValueExpression<Vec<TypedExpression<'ast, T>>>;

#[derive(Clone, PartialEq, Debug, Hash, Eq, PartialOrd, Ord)]
pub enum TupleExpressionInner<'ast, T> {
    Block(BlockExpression<'ast, T, TupleExpression<'ast, T>>),
    Identifier(IdentifierExpression<'ast, TupleExpression<'ast, T>>),
    Value(TupleValueExpression<'ast, T>),
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
                .join("\n"),
        )
    }
}

impl<'ast, T: fmt::Display> fmt::Display for FieldElementExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FieldElementExpression::Block(ref block) => write!(f, "{}", block),
            FieldElementExpression::Value(ref i) => write!(f, "{}f", i),
            FieldElementExpression::Identifier(ref var) => write!(f, "{}", var),
            FieldElementExpression::Add(ref e) => write!(f, "{}", e),
            FieldElementExpression::Sub(ref e) => write!(f, "{}", e),
            FieldElementExpression::Mult(ref e) => write!(f, "{}", e),
            FieldElementExpression::Div(ref e) => write!(f, "{}", e),
            FieldElementExpression::Pow(ref e) => write!(f, "{}", e),
            FieldElementExpression::Neg(ref e) => write!(f, "{}", e),
            FieldElementExpression::Pos(ref e) => write!(f, "{}", e),
            FieldElementExpression::Conditional(ref c) => write!(f, "{}", c),
            FieldElementExpression::And(ref e) => write!(f, "{}", e),
            FieldElementExpression::Or(ref e) => write!(f, "{}", e),
            FieldElementExpression::Xor(ref e) => write!(f, "{}", e),
            FieldElementExpression::LeftShift(ref e) => write!(f, "{}", e),
            FieldElementExpression::RightShift(ref e) => write!(f, "{}", e),
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
            UExpressionInner::Add(ref e) => write!(f, "{}", e),
            UExpressionInner::And(ref e) => write!(f, "{}", e),
            UExpressionInner::Or(ref e) => write!(f, "{}", e),
            UExpressionInner::Xor(ref e) => write!(f, "{}", e),
            UExpressionInner::Sub(ref e) => write!(f, "{}", e),
            UExpressionInner::Mult(ref e) => write!(f, "{}", e),
            UExpressionInner::FloorSub(ref e) => {
                write!(f, "{}", e)
            }
            UExpressionInner::Div(ref e) => write!(f, "{}", e),
            UExpressionInner::Rem(ref e) => write!(f, "{}", e),
            UExpressionInner::RightShift(ref e) => write!(f, "{}", e),
            UExpressionInner::LeftShift(ref e) => write!(f, "{}", e),
            UExpressionInner::Not(ref e) => write!(f, "{}", e),
            UExpressionInner::Neg(ref e) => write!(f, "{}", e),
            UExpressionInner::Pos(ref e) => write!(f, "{}", e),
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
        match &self {
            BooleanExpression::Block(ref block) => write!(f, "{}", block,),
            BooleanExpression::Identifier(ref var) => write!(f, "{}", var),
            BooleanExpression::FieldLt(ref e) => write!(f, "{}", e),
            BooleanExpression::FieldLe(ref e) => write!(f, "{}", e),
            BooleanExpression::UintLt(ref e) => write!(f, "{}", e),
            BooleanExpression::UintLe(ref e) => write!(f, "{}", e),
            BooleanExpression::FieldEq(ref e) => write!(f, "{}", e),
            BooleanExpression::BoolEq(ref e) => write!(f, "{}", e),
            BooleanExpression::ArrayEq(ref e) => write!(f, "{}", e),
            BooleanExpression::StructEq(ref e) => write!(f, "{}", e),
            BooleanExpression::TupleEq(ref e) => write!(f, "{}", e),
            BooleanExpression::UintEq(ref e) => write!(f, "{}", e),
            BooleanExpression::Or(ref e) => write!(f, "{}", e),
            BooleanExpression::And(ref e) => write!(f, "{}", e),
            BooleanExpression::Not(ref exp) => write!(f, "{}", exp),
            BooleanExpression::Value(ref b) => write!(f, "{}", b),
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
            ArrayExpressionInner::Slice(ref e) => write!(f, "{}", e),
            ArrayExpressionInner::Repeat(ref e) => write!(f, "{}", e),
            ArrayExpressionInner::Element(ref element) => write!(f, "{}", element),
        }
    }
}

// Variable to TypedExpression conversion

impl<'ast, T: Field> From<Variable<'ast, T>> for TypedExpression<'ast, T> {
    fn from(v: Variable<'ast, T>) -> Self {
        match v.get_type() {
            Type::FieldElement => FieldElementExpression::identifier(v.id).into(),
            Type::Boolean => BooleanExpression::identifier(v.id).into(),
            Type::Array(ty) => ArrayExpression::identifier(v.id).annotate(ty).into(),
            Type::Struct(ty) => StructExpression::identifier(v.id).annotate(ty).into(),
            Type::Tuple(ty) => TupleExpression::identifier(v.id).annotate(ty).into(),
            Type::Uint(w) => UExpression::identifier(v.id).annotate(w).into(),
            Type::Int => unreachable!(),
        }
    }
}

// TODO: MACROS

impl<'ast, T> WithSpan for TypedExpression<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        use TypedExpression::*;
        match self {
            Boolean(e) => Boolean(e.span(span)),
            FieldElement(e) => FieldElement(e.span(span)),
            Uint(e) => Uint(e.span(span)),
            Array(e) => Array(e.span(span)),
            Struct(e) => Struct(e.span(span)),
            Tuple(e) => Tuple(e.span(span)),
            Int(e) => Int(e.span(span)),
        }
    }

    fn get_span(&self) -> Option<Span> {
        use TypedExpression::*;
        match self {
            Boolean(e) => e.get_span(),
            FieldElement(e) => e.get_span(),
            Uint(e) => e.get_span(),
            Array(e) => e.get_span(),
            Struct(e) => e.get_span(),
            Tuple(e) => e.get_span(),
            Int(e) => e.get_span(),
        }
    }
}

impl<'ast, T> WithSpan for FieldElementExpression<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        use FieldElementExpression::*;
        match self {
            Select(e) => Select(e.span(span)),
            Block(e) => Block(e.span(span)),
            Identifier(e) => Identifier(e.span(span)),
            Conditional(e) => Conditional(e.span(span)),
            FunctionCall(e) => FunctionCall(e.span(span)),
            Member(e) => Member(e.span(span)),
            Element(e) => Element(e.span(span)),
            Add(e) => Add(e.span(span)),
            Value(e) => Value(e.span(span)),
            Mult(e) => Mult(e.span(span)),
            Sub(e) => Sub(e.span(span)),
            Pow(e) => Pow(e.span(span)),
            Div(e) => Div(e.span(span)),
            Pos(e) => Pos(e.span(span)),
            Neg(e) => Neg(e.span(span)),
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
            Block(e) => e.get_span(),
            Identifier(e) => e.get_span(),
            Conditional(e) => e.get_span(),
            FunctionCall(e) => e.get_span(),
            Member(e) => e.get_span(),
            Element(e) => e.get_span(),
            Add(e) => e.get_span(),
            Value(e) => e.get_span(),
            Sub(e) => e.get_span(),
            Mult(e) => e.get_span(),
            Div(e) => e.get_span(),
            Pow(e) => e.get_span(),
            Neg(e) => e.get_span(),
            Pos(e) => e.get_span(),
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
            Block(e) => Block(e.span(span)),
            Identifier(e) => Identifier(e.span(span)),
            Conditional(e) => Conditional(e.span(span)),
            FunctionCall(e) => FunctionCall(e.span(span)),
            Member(e) => Member(e.span(span)),
            Element(e) => Element(e.span(span)),
            Value(e) => Value(e.span(span)),
            FieldLt(e) => FieldLt(e.span(span)),
            FieldLe(e) => FieldLe(e.span(span)),
            UintLt(e) => UintLt(e.span(span)),
            UintLe(e) => UintLe(e.span(span)),
            FieldEq(e) => FieldEq(e.span(span)),
            BoolEq(e) => BoolEq(e.span(span)),
            ArrayEq(e) => ArrayEq(e.span(span)),
            StructEq(e) => StructEq(e.span(span)),
            TupleEq(e) => TupleEq(e.span(span)),
            UintEq(e) => UintEq(e.span(span)),
            Or(e) => Or(e.span(span)),
            And(e) => And(e.span(span)),
            Not(e) => Not(e.span(span)),
        }
    }

    fn get_span(&self) -> Option<Span> {
        use BooleanExpression::*;
        match self {
            Select(e) => e.get_span(),
            Block(e) => e.get_span(),
            Identifier(e) => e.get_span(),
            Conditional(e) => e.get_span(),
            FunctionCall(e) => e.get_span(),
            Member(e) => e.get_span(),
            Element(e) => e.get_span(),
            Value(e) => e.get_span(),
            FieldLt(e) => e.get_span(),
            FieldLe(e) => e.get_span(),
            UintLt(e) => e.get_span(),
            UintLe(e) => e.get_span(),
            FieldEq(e) => e.get_span(),
            BoolEq(e) => e.get_span(),
            ArrayEq(e) => e.get_span(),
            StructEq(e) => e.get_span(),
            TupleEq(e) => e.get_span(),
            UintEq(e) => e.get_span(),
            Or(e) => e.get_span(),
            And(e) => e.get_span(),
            Not(e) => e.get_span(),
        }
    }
}

impl<'ast, T> WithSpan for UExpressionInner<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        use UExpressionInner::*;
        match self {
            Select(e) => Select(e.span(span)),
            Block(e) => Block(e.span(span)),
            Identifier(e) => Identifier(e.span(span)),
            Conditional(e) => Conditional(e.span(span)),
            FunctionCall(e) => FunctionCall(e.span(span)),
            Member(e) => Member(e.span(span)),
            Element(e) => Element(e.span(span)),
            Value(e) => Value(e.span(span)),
            Add(e) => Add(e.span(span)),
            Sub(e) => Sub(e.span(span)),
            FloorSub(e) => FloorSub(e.span(span)),
            Mult(e) => Mult(e.span(span)),
            Div(e) => Div(e.span(span)),
            Rem(e) => Rem(e.span(span)),
            Xor(e) => Xor(e.span(span)),
            And(e) => And(e.span(span)),
            Or(e) => Or(e.span(span)),
            Not(e) => Not(e.span(span)),
            Neg(e) => Neg(e.span(span)),
            Pos(e) => Pos(e.span(span)),
            LeftShift(e) => LeftShift(e.span(span)),
            RightShift(e) => RightShift(e.span(span)),
        }
    }

    fn get_span(&self) -> Option<Span> {
        use UExpressionInner::*;
        match self {
            Select(e) => e.get_span(),
            Block(e) => e.get_span(),
            Identifier(e) => e.get_span(),
            Conditional(e) => e.get_span(),
            FunctionCall(e) => e.get_span(),
            Member(e) => e.get_span(),
            Element(e) => e.get_span(),
            Value(e) => e.get_span(),
            Add(e) => e.get_span(),
            Sub(e) => e.get_span(),
            FloorSub(e) => e.get_span(),
            Mult(e) => e.get_span(),
            Div(e) => e.get_span(),
            Rem(e) => e.get_span(),
            Xor(e) => e.get_span(),
            And(e) => e.get_span(),
            Or(e) => e.get_span(),
            Not(e) => e.get_span(),
            Neg(e) => e.get_span(),
            Pos(e) => e.get_span(),
            LeftShift(e) => e.get_span(),
            RightShift(e) => e.get_span(),
        }
    }
}

impl<'ast, T> WithSpan for ArrayExpressionInner<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        use ArrayExpressionInner::*;
        match self {
            Select(e) => Select(e.span(span)),
            Block(e) => Block(e.span(span)),
            Identifier(e) => Identifier(e.span(span)),
            Conditional(e) => Conditional(e.span(span)),
            FunctionCall(e) => FunctionCall(e.span(span)),
            Member(e) => Member(e.span(span)),
            Element(e) => Element(e.span(span)),
            Value(e) => Value(e.span(span)),
            Slice(e) => Slice(e.span(span)),
            Repeat(e) => Repeat(e.span(span)),
        }
    }

    fn get_span(&self) -> Option<Span> {
        use ArrayExpressionInner::*;
        match self {
            Select(e) => e.get_span(),
            Block(e) => e.get_span(),
            Identifier(e) => e.get_span(),
            Conditional(e) => e.get_span(),
            FunctionCall(e) => e.get_span(),
            Member(e) => e.get_span(),
            Element(e) => e.get_span(),
            Value(e) => e.get_span(),
            Slice(e) => e.get_span(),
            Repeat(e) => e.get_span(),
        }
    }
}

impl<'ast, T> WithSpan for StructExpressionInner<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        use StructExpressionInner::*;
        match self {
            Select(e) => Select(e.span(span)),
            Block(e) => Block(e.span(span)),
            Identifier(e) => Identifier(e.span(span)),
            Conditional(e) => Conditional(e.span(span)),
            FunctionCall(e) => FunctionCall(e.span(span)),
            Member(e) => Member(e.span(span)),
            Element(e) => Element(e.span(span)),
            Value(e) => Value(e.span(span)),
        }
    }

    fn get_span(&self) -> Option<Span> {
        use StructExpressionInner::*;
        match self {
            Select(e) => e.get_span(),
            Block(e) => e.get_span(),
            Identifier(e) => e.get_span(),
            Conditional(e) => e.get_span(),
            FunctionCall(e) => e.get_span(),
            Member(e) => e.get_span(),
            Element(e) => e.get_span(),
            Value(e) => e.get_span(),
        }
    }
}

impl<'ast, T> WithSpan for TupleExpressionInner<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        use TupleExpressionInner::*;
        match self {
            Select(e) => Select(e.span(span)),
            Block(e) => Block(e.span(span)),
            Identifier(e) => Identifier(e.span(span)),
            Conditional(e) => Conditional(e.span(span)),
            FunctionCall(e) => FunctionCall(e.span(span)),
            Member(e) => Member(e.span(span)),
            Element(e) => Element(e.span(span)),
            Value(e) => Value(e.span(span)),
        }
    }

    fn get_span(&self) -> Option<Span> {
        use TupleExpressionInner::*;
        match self {
            Select(e) => e.get_span(),
            Block(e) => e.get_span(),
            Identifier(e) => e.get_span(),
            Conditional(e) => e.get_span(),
            FunctionCall(e) => e.get_span(),
            Member(e) => e.get_span(),
            Element(e) => e.get_span(),
            Value(e) => e.get_span(),
        }
    }
}

impl<'ast, T> WithSpan for IntExpression<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        use IntExpression::*;
        match self {
            Conditional(e) => Conditional(e.span(span)),
            Select(e) => Select(e.span(span)),
            Value(e) => Value(e.span(span)),
            Pos(e) => Pos(e.span(span)),
            Neg(e) => Neg(e.span(span)),
            Not(e) => Not(e.span(span)),
            Add(e) => Add(e.span(span)),
            Sub(e) => Sub(e.span(span)),
            Mult(e) => Mult(e.span(span)),
            Div(e) => Div(e.span(span)),
            Rem(e) => Rem(e.span(span)),
            Pow(e) => Pow(e.span(span)),
            Xor(e) => Xor(e.span(span)),
            And(e) => And(e.span(span)),
            Or(e) => Or(e.span(span)),
            LeftShift(e) => LeftShift(e.span(span)),
            RightShift(e) => RightShift(e.span(span)),
        }
    }

    fn get_span(&self) -> Option<Span> {
        use IntExpression::*;
        match self {
            Conditional(e) => e.get_span(),
            Select(e) => e.get_span(),
            Value(e) => e.get_span(),
            Pos(e) => e.get_span(),
            Neg(e) => e.get_span(),
            Not(e) => e.get_span(),
            Add(e) => e.get_span(),
            Sub(e) => e.get_span(),
            Mult(e) => e.get_span(),
            Div(e) => e.get_span(),
            Rem(e) => e.get_span(),
            Pow(e) => e.get_span(),
            Xor(e) => e.get_span(),
            And(e) => e.get_span(),
            Or(e) => e.get_span(),
            LeftShift(e) => e.get_span(),
            RightShift(e) => e.get_span(),
        }
    }
}

impl<'ast, T> WithSpan for TupleExpression<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        TupleExpression {
            inner: self.inner.span(span),
            ..self
        }
    }

    fn get_span(&self) -> Option<Span> {
        self.inner.get_span()
    }
}

impl<'ast, T> WithSpan for StructExpression<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        StructExpression {
            inner: self.inner.span(span),
            ..self
        }
    }

    fn get_span(&self) -> Option<Span> {
        self.inner.get_span()
    }
}

impl<'ast, T> WithSpan for ArrayExpression<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        ArrayExpression {
            inner: self.inner.span(span),
            ..self
        }
    }

    fn get_span(&self) -> Option<Span> {
        self.inner.get_span()
    }
}

impl<'ast, T> WithSpan for UExpression<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        UExpression {
            inner: self.inner.span(span),
            ..self
        }
    }

    fn get_span(&self) -> Option<Span> {
        self.inner.get_span()
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

impl<E> WithSpan for ValueExpression<E> {
    fn span(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }

    fn get_span(&self) -> Option<Span> {
        self.span
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

impl<'ast, T, E> WithSpan for ElementExpression<'ast, T, E> {
    fn span(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

impl<'ast, T, E> WithSpan for MemberExpression<'ast, T, E> {
    fn span(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

impl<'ast, T, E> WithSpan for FunctionCallExpression<'ast, T, E> {
    fn span(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

impl<'ast, T, E> WithSpan for BlockExpression<'ast, T, E> {
    fn span(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }

    fn get_span(&self) -> Option<Span> {
        self.span
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

impl<'ast, T: Clone> Value for ArrayExpression<'ast, T> {
    type Value = Vec<TypedExpressionOrSpread<'ast, T>>;
}

impl<'ast, T: Clone> Value for StructExpression<'ast, T> {
    type Value = Vec<TypedExpression<'ast, T>>;
}

impl<'ast, T: Clone> Value for TupleExpression<'ast, T> {
    type Value = Vec<TypedExpression<'ast, T>>;
}

impl<'ast, T> Value for IntExpression<'ast, T> {
    type Value = BigUint;
}

// Common behaviour across expressions

pub trait Expr<'ast, T>: Value + WithSpan + fmt::Display + From<TypedExpression<'ast, T>> {
    type Inner: WithSpan;
    type Ty: Clone + IntoType<UExpression<'ast, T>>;
    type ConcreteTy: Clone + IntoType<u32>;

    fn ty(&self) -> &Self::Ty;

    fn into_inner(self) -> Self::Inner;

    fn as_inner(&self) -> &Self::Inner;

    fn as_inner_mut(&mut self) -> &mut Self::Inner;

    fn value(_: Self::Value) -> Self::Inner;
}

impl<'ast, T: fmt::Display + Clone> Expr<'ast, T> for FieldElementExpression<'ast, T> {
    type Inner = Self;
    type Ty = Type<'ast, T>;
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

    fn value(v: <Self as Value>::Value) -> Self::Inner {
        Self::Value(ValueExpression::new(v))
    }
}

impl<'ast, T: fmt::Display + Clone> Expr<'ast, T> for BooleanExpression<'ast, T> {
    type Inner = Self;
    type Ty = Type<'ast, T>;
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

    fn value(v: <Self as Value>::Value) -> Self::Inner {
        Self::Value(ValueExpression::new(v))
    }
}

impl<'ast, T: fmt::Display + Clone> Expr<'ast, T> for UExpression<'ast, T> {
    type Inner = UExpressionInner<'ast, T>;
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

    fn value(v: Self::Value) -> Self::Inner {
        UExpressionInner::Value(ValueExpression::new(v))
    }
}

impl<'ast, T: fmt::Display + Clone> Expr<'ast, T> for StructExpression<'ast, T> {
    type Inner = StructExpressionInner<'ast, T>;
    type Ty = StructType<'ast, T>;
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

    fn value(v: Self::Value) -> Self::Inner {
        StructExpressionInner::Value(ValueExpression::new(v))
    }
}

impl<'ast, T: Clone + fmt::Display> Expr<'ast, T> for ArrayExpression<'ast, T> {
    type Inner = ArrayExpressionInner<'ast, T>;
    type Ty = ArrayType<'ast, T>;
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

    fn value(v: Self::Value) -> Self::Inner {
        ArrayExpressionInner::Value(ValueExpression::new(v))
    }
}

impl<'ast, T: fmt::Display + Clone> Expr<'ast, T> for TupleExpression<'ast, T> {
    type Inner = TupleExpressionInner<'ast, T>;
    type Ty = TupleType<'ast, T>;
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

    fn value(v: Self::Value) -> Self::Inner {
        TupleExpressionInner::Value(ValueExpression::new(v))
    }
}

impl<'ast, T: fmt::Display + Clone> Expr<'ast, T> for IntExpression<'ast, T> {
    type Inner = Self;
    type Ty = Type<'ast, T>;
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

    fn value(v: <integer::IntExpression<'ast, T> as Value>::Value) -> Self {
        IntExpression::Value(ValueExpression::new(v))
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
pub enum MemberOrExpression<'ast, T, E: Expr<'ast, T>> {
    Member(MemberExpression<'ast, T, E>),
    Expression(E::Inner),
}

pub enum RepeatOrExpression<'ast, T> {
    Repeat(RepeatExpression<'ast, T>),
    Expression(ArrayExpressionInner<'ast, T>),
}

pub enum SliceOrExpression<'ast, T> {
    Slice(SliceExpression<'ast, T>),
    Expression(ArrayExpressionInner<'ast, T>),
}

pub enum ElementOrExpression<'ast, T, E: Expr<'ast, T>> {
    Element(ElementExpression<'ast, T, E>),
    Expression(E::Inner),
}

pub enum ConditionalOrExpression<'ast, T, E: Expr<'ast, T>> {
    Conditional(ConditionalExpression<'ast, T, E>),
    Expression(E::Inner),
}

pub trait Basic<'ast, T> {
    type ZirExpressionType: WithSpan + Value + From<crate::zir::ZirExpression<'ast, T>>;
}

impl<'ast, T: Clone> Basic<'ast, T> for FieldElementExpression<'ast, T> {
    type ZirExpressionType = crate::zir::FieldElementExpression<'ast, T>;
}

impl<'ast, T> Basic<'ast, T> for BooleanExpression<'ast, T> {
    type ZirExpressionType = crate::zir::BooleanExpression<'ast, T>;
}

impl<'ast, T> Basic<'ast, T> for UExpression<'ast, T> {
    type ZirExpressionType = crate::zir::UExpression<'ast, T>;
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

impl<'ast, T: Clone + fmt::Display> Conditional<'ast, T> for ArrayExpression<'ast, T> {
    fn conditional(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
        kind: ConditionalKind,
    ) -> Self {
        let ty = consequence.ty().clone();
        ArrayExpressionInner::Conditional(ConditionalExpression::new(
            condition,
            consequence,
            alternative,
            kind,
        ))
        .annotate(ty)
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
        let array_ty = array.inner_type().clone().try_into().unwrap();

        ArrayExpressionInner::Select(SelectExpression::new(array, index.into())).annotate(array_ty)
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
        let ty = *s
            .ty()
            .members
            .iter()
            .find(|member| id == member.id)
            .unwrap()
            .ty
            .clone();
        let bitwidth: UBitwidth = ty.try_into().unwrap();
        UExpressionInner::Member(MemberExpression::new(s, id)).annotate(bitwidth)
    }
}

impl<'ast, T: Clone> Member<'ast, T> for ArrayExpression<'ast, T> {
    fn member(s: StructExpression<'ast, T>, id: MemberId) -> Self {
        let ty = *s
            .ty()
            .members
            .iter()
            .find(|member| id == member.id)
            .unwrap()
            .ty
            .clone();
        let array_ty: ArrayType<'ast, T> = ty.try_into().unwrap();
        ArrayExpressionInner::Member(MemberExpression::new(s, id)).annotate(array_ty)
    }
}

impl<'ast, T: Clone> Member<'ast, T> for StructExpression<'ast, T> {
    fn member(s: StructExpression<'ast, T>, id: MemberId) -> Self {
        let ty = *s
            .ty()
            .members
            .iter()
            .find(|member| id == member.id)
            .unwrap()
            .ty
            .clone();
        let struct_ty = ty.try_into().unwrap();
        StructExpressionInner::Member(MemberExpression::new(s, id)).annotate(struct_ty)
    }
}

impl<'ast, T: Clone> Member<'ast, T> for TupleExpression<'ast, T> {
    fn member(s: StructExpression<'ast, T>, id: MemberId) -> Self {
        let ty = *s
            .ty()
            .members
            .iter()
            .find(|member| id == member.id)
            .unwrap()
            .ty
            .clone();
        let tuple_ty = ty.try_into().unwrap();
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
        let ty = s.ty().elements[id as usize].clone();
        let array_ty = ty.try_into().unwrap();
        ArrayExpressionInner::Element(ElementExpression::new(s, id)).annotate(array_ty)
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

impl<'ast, T: Field> Id<'ast, T> for ArrayExpression<'ast, T> {
    fn identifier(id: Identifier<'ast>) -> Self::Inner {
        ArrayExpressionInner::Identifier(IdentifierExpression::new(id))
    }
}

impl<'ast, T: Field> Id<'ast, T> for StructExpression<'ast, T> {
    fn identifier(id: Identifier<'ast>) -> Self::Inner {
        StructExpressionInner::Identifier(IdentifierExpression::new(id))
    }
}

impl<'ast, T: Field> Id<'ast, T> for TupleExpression<'ast, T> {
    fn identifier(id: Identifier<'ast>) -> Self::Inner {
        TupleExpressionInner::Identifier(IdentifierExpression::new(id))
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
        ArrayExpressionInner::Block(BlockExpression::new(statements, value)).annotate(array_ty)
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

impl<'ast, T: Field> Constant for ArrayExpression<'ast, T> {
    fn is_constant(&self) -> bool {
        match self.as_inner() {
            ArrayExpressionInner::Value(v) => v.iter().all(|e| match e {
                TypedExpressionOrSpread::Expression(e) => e.is_constant(),
                TypedExpressionOrSpread::Spread(s) => s.array.is_constant(),
            }),
            ArrayExpressionInner::Slice(e) => {
                e.from.is_constant() && e.to.is_constant() && e.array.is_constant()
            }
            ArrayExpressionInner::Repeat(e) => e.count.is_constant() && e.e.is_constant(),
            _ => false,
        }
    }

    fn into_canonical_constant(self) -> Self {
        fn into_canonical_constant_aux<T: Field>(
            e: TypedExpressionOrSpread<T>,
        ) -> Vec<TypedExpression<T>> {
            match e {
                TypedExpressionOrSpread::Expression(e) => vec![e.into_canonical_constant()],
                TypedExpressionOrSpread::Spread(s) => match s.array.into_inner() {
                    ArrayExpressionInner::Value(v) => v
                        .into_iter()
                        .flat_map(into_canonical_constant_aux)
                        .collect(),
                    ArrayExpressionInner::Slice(e) => {
                        let from = match e.from.into_inner() {
                            UExpressionInner::Value(v) => v,
                            _ => unreachable!(),
                        };

                        let to = match e.to.into_inner() {
                            UExpressionInner::Value(v) => v,
                            _ => unreachable!(),
                        };

                        let v = match e.array.into_inner() {
                            ArrayExpressionInner::Value(v) => v,
                            _ => unreachable!(),
                        };

                        v.into_iter()
                            .flat_map(into_canonical_constant_aux)
                            .skip(from.value as usize)
                            .take(to.value as usize - from.value as usize)
                            .collect()
                    }
                    ArrayExpressionInner::Repeat(e) => {
                        let count = match e.count.into_inner() {
                            UExpressionInner::Value(count) => count,
                            _ => unreachable!(),
                        };

                        vec![e.e.into_canonical_constant(); count.value as usize]
                    }
                    a => unreachable!("{}", a),
                },
            }
        }

        let array_ty = self.ty().clone();

        match self.into_inner() {
            ArrayExpressionInner::Value(v) => ArrayExpression::value(
                v.into_iter()
                    .flat_map(into_canonical_constant_aux)
                    .map(|e| e.into())
                    .collect::<Vec<_>>(),
            )
            .annotate(array_ty),
            ArrayExpressionInner::Slice(e) => {
                let from = match e.from.into_inner() {
                    UExpressionInner::Value(from) => from.value as usize,
                    _ => unreachable!("should be a uint value"),
                };

                let to = match e.to.into_inner() {
                    UExpressionInner::Value(to) => to.value as usize,
                    _ => unreachable!("should be a uint value"),
                };

                let v = match e.array.into_inner() {
                    ArrayExpressionInner::Value(v) => v,
                    _ => unreachable!("should be an array value"),
                };

                ArrayExpression::value(
                    v.into_iter()
                        .flat_map(into_canonical_constant_aux)
                        .map(|e| e.into())
                        .skip(from)
                        .take(to - from)
                        .collect::<Vec<_>>(),
                )
                .annotate(array_ty)
            }
            ArrayExpressionInner::Repeat(e) => {
                let count = match e.count.into_inner() {
                    UExpressionInner::Value(from) => from.value as usize,
                    _ => unreachable!("should be a uint value"),
                };

                let e = e.e.into_canonical_constant();

                ArrayExpression::value(vec![TypedExpressionOrSpread::Expression(e); count])
                    .annotate(array_ty)
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
            StructExpressionInner::Value(expressions) => StructExpression::value(
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
            TupleExpressionInner::Value(expressions) => TupleExpression::value(
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
