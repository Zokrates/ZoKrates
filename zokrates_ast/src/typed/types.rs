use crate::typed::{
    CoreIdentifier, Identifier, OwnedTypedModuleId, TypedExpression, UExpression, UExpressionInner,
};
use crate::typed::{TryFrom, TryInto};
use serde::{de::Error, ser::SerializeMap, Deserialize, Deserializer, Serialize, Serializer};
use std::collections::BTreeMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};

pub trait IntoType<'ast, T> {
    fn into_type(self) -> Type<'ast, T>;
}

impl<'ast, T> IntoType<'ast, T> for Type<'ast, T> {
    fn into_type(self) -> Type<'ast, T> {
        self
    }
}

impl<'ast, T> IntoType<'ast, T> for StructType<'ast, T> {
    fn into_type(self) -> Type<'ast, T> {
        Type::Struct(self)
    }
}

impl<'ast, T> IntoType<'ast, T> for ArrayType<'ast, T> {
    fn into_type(self) -> Type<'ast, T> {
        Type::Array(self)
    }
}

impl<'ast, T> IntoType<'ast, T> for TupleType<'ast, T> {
    fn into_type(self) -> Type<'ast, T> {
        Type::Tuple(self)
    }
}

impl<'ast, T> IntoType<'ast, T> for UBitwidth {
    fn into_type(self) -> Type<'ast, T> {
        Type::Uint(self)
    }
}

#[derive(Debug, Clone, Eq)]
pub struct GenericIdentifier<'ast> {
    name: Option<&'ast str>,
    index: usize,
}

impl<'ast> From<GenericIdentifier<'ast>> for CoreIdentifier<'ast> {
    fn from(g: GenericIdentifier<'ast>) -> CoreIdentifier<'ast> {
        // generic identifiers are always declared in the function scope, which is shadow 0
        CoreIdentifier::Source(ShadowedIdentifier::shadow(g.name(), 0))
    }
}

impl<'ast> GenericIdentifier<'ast> {
    pub fn without_name() -> Self {
        Self {
            name: None,
            index: 0,
        }
    }

    pub fn with_name(name: &'ast str) -> Self {
        Self {
            name: Some(name),
            index: 0,
        }
    }

    pub fn with_index(mut self, index: usize) -> Self {
        self.index = index;
        self
    }

    pub fn name(&self) -> &'ast str {
        self.name.unwrap()
    }

    pub fn index(&self) -> usize {
        self.index
    }
}

impl<'ast> PartialEq for GenericIdentifier<'ast> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl<'ast> PartialOrd for GenericIdentifier<'ast> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.index.partial_cmp(&other.index)
    }
}

impl<'ast> Ord for GenericIdentifier<'ast> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl<'ast> Hash for GenericIdentifier<'ast> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.index.hash(state);
    }
}

impl<'ast> fmt::Display for GenericIdentifier<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

#[derive(Debug)]
pub struct SpecializationError;

pub type ConstantIdentifier<'ast> = &'ast str;

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct CanonicalConstantIdentifier<'ast> {
    pub module: OwnedTypedModuleId,
    pub id: ConstantIdentifier<'ast>,
}

impl<'ast> fmt::Display for CanonicalConstantIdentifier<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}/{}", self.module.display(), self.id)
    }
}

impl<'ast> CanonicalConstantIdentifier<'ast> {
    pub fn new(id: ConstantIdentifier<'ast>, module: OwnedTypedModuleId) -> Self {
        CanonicalConstantIdentifier { module, id }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DeclarationConstant<'ast, T> {
    Generic(GenericIdentifier<'ast>),
    Concrete(u32),
    Constant(CanonicalConstantIdentifier<'ast>),
    Expression(TypedExpression<'ast, T>),
}

impl<'ast, T> DeclarationConstant<'ast, T> {
    pub fn map<S: From<CanonicalConstantIdentifier<'ast>> + From<u32> + Clone>(
        self,
        generics: &GGenericsAssignment<'ast, S>,
    ) -> Result<S, GenericIdentifier<'ast>> {
        match self {
            DeclarationConstant::Generic(g) => generics.0.get(&g).cloned().ok_or(g),
            DeclarationConstant::Concrete(v) => Ok(v.into()),
            DeclarationConstant::Constant(c) => Ok(c.into()),
            DeclarationConstant::Expression(_) => unreachable!(),
        }
    }

    pub fn map_concrete<S: From<u32> + Clone>(
        self,
        generics: &GGenericsAssignment<'ast, S>,
    ) -> Result<S, GenericIdentifier<'ast>> {
        match self {
            DeclarationConstant::Constant(_) => unreachable!(
                "called map_concrete on a constant, it should have been resolved before"
            ),
            DeclarationConstant::Generic(g) => generics.0.get(&g).cloned().ok_or(g),
            DeclarationConstant::Concrete(v) => Ok(v.into()),
            DeclarationConstant::Expression(_) => unreachable!(),
        }
    }
}

impl<'ast, T: PartialEq> PartialEq<UExpression<'ast, T>> for DeclarationConstant<'ast, T> {
    fn eq(&self, other: &UExpression<'ast, T>) -> bool {
        match (self, other) {
            (
                DeclarationConstant::Concrete(c),
                UExpression {
                    bitwidth: UBitwidth::B32,
                    inner: UExpressionInner::Value(v),
                    ..
                },
            ) => *c == *v as u32,
            (DeclarationConstant::Expression(TypedExpression::Uint(e0)), e1) => e0 == e1,
            (DeclarationConstant::Expression(..), _) => false, // type error
            _ => true,
        }
    }
}

impl<'ast, T: PartialEq> PartialEq<DeclarationConstant<'ast, T>> for UExpression<'ast, T> {
    fn eq(&self, other: &DeclarationConstant<'ast, T>) -> bool {
        other.eq(self)
    }
}

impl<'ast, T> From<u32> for DeclarationConstant<'ast, T> {
    fn from(e: u32) -> Self {
        DeclarationConstant::Concrete(e)
    }
}

impl<'ast, T> From<usize> for DeclarationConstant<'ast, T> {
    fn from(e: usize) -> Self {
        DeclarationConstant::Concrete(e as u32)
    }
}

impl<'ast, T> From<GenericIdentifier<'ast>> for DeclarationConstant<'ast, T> {
    fn from(e: GenericIdentifier<'ast>) -> Self {
        DeclarationConstant::Generic(e)
    }
}

impl<'ast, T: fmt::Display> fmt::Display for DeclarationConstant<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            DeclarationConstant::Generic(i) => write!(f, "{}", i),
            DeclarationConstant::Concrete(v) => write!(f, "{}", v),
            DeclarationConstant::Constant(v) => write!(f, "{}/{}", v.module.display(), v.id),
            DeclarationConstant::Expression(e) => write!(f, "{}", e),
        }
    }
}

impl<'ast, T> From<u32> for UExpression<'ast, T> {
    fn from(i: u32) -> Self {
        UExpressionInner::Value(i as u128).annotate(UBitwidth::B32)
    }
}

impl<'ast, T> From<DeclarationConstant<'ast, T>> for UExpression<'ast, T> {
    fn from(c: DeclarationConstant<'ast, T>) -> Self {
        match c {
            DeclarationConstant::Generic(g) => {
                UExpressionInner::Identifier(CoreIdentifier::from(g).into())
                    .annotate(UBitwidth::B32)
            }
            DeclarationConstant::Concrete(v) => {
                UExpressionInner::Value(v as u128).annotate(UBitwidth::B32)
            }
            DeclarationConstant::Constant(v) => {
                UExpressionInner::Identifier(CoreIdentifier::from(v).into())
                    .annotate(UBitwidth::B32)
            }
            DeclarationConstant::Expression(e) => e.try_into().unwrap(),
        }
    }
}

impl<'ast, T> TryInto<u32> for UExpression<'ast, T> {
    type Error = SpecializationError;

    fn try_into(self) -> Result<u32, Self::Error> {
        assert_eq!(self.bitwidth, UBitwidth::B32);

        match self.into_inner() {
            UExpressionInner::Value(v) => Ok(v as u32),
            _ => Err(SpecializationError),
        }
    }
}

impl<'ast, T> TryInto<usize> for DeclarationConstant<'ast, T> {
    type Error = SpecializationError;

    fn try_into(self) -> Result<usize, Self::Error> {
        match self {
            DeclarationConstant::Concrete(v) => Ok(v as usize),
            _ => Err(SpecializationError),
        }
    }
}

pub type MemberId = String;

#[allow(clippy::derive_hash_xor_eq)]
#[derive(Debug, Clone, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub struct GStructMember<S> {
    #[serde(rename = "name")]
    pub id: MemberId,
    #[serde(flatten)]
    pub ty: Box<GType<S>>,
}

pub type DeclarationStructMember<'ast, T> = GStructMember<DeclarationConstant<'ast, T>>;
pub type ConcreteStructMember = GStructMember<u32>;
pub type StructMember<'ast, T> = GStructMember<UExpression<'ast, T>>;

impl<S, R: PartialEq<S>> PartialEq<GStructMember<S>> for GStructMember<R> {
    fn eq(&self, other: &GStructMember<S>) -> bool {
        self.id == other.id && *self.ty == *other.ty
    }
}

fn try_from_g_struct_member<T: TryInto<U>, U>(
    t: GStructMember<T>,
) -> Result<GStructMember<U>, SpecializationError> {
    Ok(GStructMember {
        id: t.id,
        ty: box try_from_g_type(*t.ty)?,
    })
}

impl<'ast, T> TryFrom<StructMember<'ast, T>> for ConcreteStructMember {
    type Error = SpecializationError;

    fn try_from(t: StructMember<'ast, T>) -> Result<Self, Self::Error> {
        try_from_g_struct_member(t)
    }
}

impl<'ast, T> From<ConcreteStructMember> for StructMember<'ast, T> {
    fn from(t: ConcreteStructMember) -> Self {
        try_from_g_struct_member(t).unwrap()
    }
}

#[allow(clippy::derive_hash_xor_eq)]
#[derive(Clone, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord, Debug)]
pub struct GArrayType<S> {
    pub size: Box<S>,
    #[serde(flatten)]
    pub ty: Box<GType<S>>,
}

pub type DeclarationArrayType<'ast, T> = GArrayType<DeclarationConstant<'ast, T>>;
pub type ConcreteArrayType = GArrayType<u32>;
pub type ArrayType<'ast, T> = GArrayType<UExpression<'ast, T>>;

impl<S, R: PartialEq<S>> PartialEq<GArrayType<S>> for GArrayType<R> {
    fn eq(&self, other: &GArrayType<S>) -> bool {
        *self.ty == *other.ty && *self.size == *other.size
    }
}

impl<S: fmt::Display> fmt::Display for GArrayType<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fn fmt_aux<'a, S: fmt::Display>(
            f: &mut fmt::Formatter,
            t: &'a GArrayType<S>,
            mut acc: Vec<&'a S>,
        ) -> fmt::Result {
            acc.push(&t.size);
            match &*t.ty {
                GType::Array(array_type) => fmt_aux(f, array_type, acc),
                t => {
                    write!(f, "{}", t)?;
                    for i in acc {
                        write!(f, "[{}]", i)?;
                    }
                    write!(f, "")
                }
            }
        }

        let acc = vec![];

        fmt_aux(f, self, acc)
    }
}

fn try_from_g_array_type<T: TryInto<U>, U>(
    t: GArrayType<T>,
) -> Result<GArrayType<U>, SpecializationError> {
    Ok(GArrayType {
        size: box (*t.size).try_into().map_err(|_| SpecializationError)?,
        ty: box try_from_g_type(*t.ty)?,
    })
}

impl<'ast, T> TryFrom<ArrayType<'ast, T>> for ConcreteArrayType {
    type Error = SpecializationError;

    fn try_from(t: ArrayType<'ast, T>) -> Result<Self, Self::Error> {
        try_from_g_array_type(t)
    }
}

impl<'ast, T> From<ConcreteArrayType> for ArrayType<'ast, T> {
    fn from(t: ConcreteArrayType) -> Self {
        try_from_g_array_type(t).unwrap()
    }
}

#[allow(clippy::derive_hash_xor_eq)]
#[derive(Clone, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord, Debug)]
pub struct GTupleType<S> {
    pub elements: Vec<GType<S>>,
}

impl<S> GTupleType<S> {
    pub fn new(elements: Vec<GType<S>>) -> Self {
        GTupleType { elements }
    }
}

pub type DeclarationTupleType<'ast, T> = GTupleType<DeclarationConstant<'ast, T>>;
pub type ConcreteTupleType = GTupleType<u32>;
pub type TupleType<'ast, T> = GTupleType<UExpression<'ast, T>>;

impl<S, R: PartialEq<S>> PartialEq<GTupleType<S>> for GTupleType<R> {
    fn eq(&self, other: &GTupleType<S>) -> bool {
        *self.elements == *other.elements
    }
}

impl<S: fmt::Display> fmt::Display for GTupleType<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(")?;
        match self.elements.len() {
            1 => write!(f, "{},", self.elements[0]),
            _ => write!(
                f,
                "{}",
                self.elements
                    .iter()
                    .map(|v| v.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }?;
        write!(f, ")")
    }
}

fn try_from_g_tuple_type<T: TryInto<U>, U>(
    t: GTupleType<T>,
) -> Result<GTupleType<U>, SpecializationError> {
    Ok(GTupleType {
        elements: t
            .elements
            .into_iter()
            .map(|t| try_from_g_type(t))
            .collect::<Result<_, _>>()?,
    })
}

impl<'ast, T> TryFrom<TupleType<'ast, T>> for ConcreteTupleType {
    type Error = SpecializationError;

    fn try_from(t: TupleType<'ast, T>) -> Result<Self, Self::Error> {
        try_from_g_tuple_type(t)
    }
}

impl<'ast, T> From<ConcreteTupleType> for TupleType<'ast, T> {
    fn from(t: ConcreteTupleType) -> Self {
        try_from_g_tuple_type(t).unwrap()
    }
}

impl<S> TryFrom<GType<S>> for GTupleType<S> {
    type Error = ();

    fn try_from(t: GType<S>) -> Result<Self, Self::Error> {
        if let GType::Tuple(t) = t {
            Ok(t)
        } else {
            Err(())
        }
    }
}

#[derive(Debug, Clone, Hash, Serialize, Deserialize, PartialOrd, Ord, Eq, PartialEq)]
pub struct StructLocation {
    #[serde(skip)]
    pub module: PathBuf,
    pub name: String,
}

impl<'ast, T> From<ConcreteArrayType> for DeclarationArrayType<'ast, T> {
    fn from(t: ConcreteArrayType) -> Self {
        try_from_g_array_type(t).unwrap()
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialOrd, Ord)]
pub struct GStructType<S> {
    #[serde(flatten)]
    pub canonical_location: StructLocation,
    #[serde(skip)]
    pub location: Option<StructLocation>,
    pub generics: Vec<Option<S>>,
    pub members: Vec<GStructMember<S>>,
}

pub type DeclarationStructType<'ast, T> = GStructType<DeclarationConstant<'ast, T>>;
pub type ConcreteStructType = GStructType<u32>;
pub type StructType<'ast, T> = GStructType<UExpression<'ast, T>>;

impl<S, R: PartialEq<S>> PartialEq<GStructType<S>> for GStructType<R> {
    fn eq(&self, other: &GStructType<S>) -> bool {
        self.canonical_location == other.canonical_location
            && self
                .generics
                .iter()
                .zip(other.generics.iter())
                .all(|(a, b)| match (a, b) {
                    (Some(a), Some(b)) => a == b,
                    _ => true,
                })
    }
}

impl<S: Hash> Hash for GStructType<S> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.canonical_location.hash(state);
        self.generics.hash(state);
    }
}

impl<S: Eq> Eq for GStructType<S> {}

fn try_from_g_struct_type<T: TryInto<U>, U>(
    t: GStructType<T>,
) -> Result<GStructType<U>, SpecializationError> {
    Ok(GStructType {
        location: t.location,
        canonical_location: t.canonical_location,
        generics: t
            .generics
            .into_iter()
            .map(|g| match g {
                Some(g) => g.try_into().map(Some).map_err(|_| SpecializationError),
                None => Ok(None),
            })
            .collect::<Result<_, _>>()?,
        members: t
            .members
            .into_iter()
            .map(try_from_g_struct_member)
            .collect::<Result<_, _>>()?,
    })
}

impl<'ast, T> TryFrom<StructType<'ast, T>> for ConcreteStructType {
    type Error = SpecializationError;

    fn try_from(t: StructType<'ast, T>) -> Result<Self, Self::Error> {
        try_from_g_struct_type(t)
    }
}

impl<'ast, T> From<ConcreteStructType> for StructType<'ast, T> {
    fn from(t: ConcreteStructType) -> Self {
        try_from_g_struct_type(t).unwrap()
    }
}

impl<'ast, T> From<ConcreteStructType> for DeclarationStructType<'ast, T> {
    fn from(t: ConcreteStructType) -> Self {
        try_from_g_struct_type(t).unwrap()
    }
}

impl<S> GStructType<S> {
    pub fn new(
        module: PathBuf,
        name: String,
        generics: Vec<Option<S>>,
        members: Vec<GStructMember<S>>,
    ) -> Self {
        GStructType {
            canonical_location: StructLocation { module, name },
            location: None,
            generics,
            members,
        }
    }

    pub fn members_count(&self) -> usize {
        self.members.len()
    }

    pub fn iter(&self) -> std::slice::Iter<GStructMember<S>> {
        self.members.iter()
    }

    fn location(&self) -> &StructLocation {
        self.location.as_ref().unwrap_or(&self.canonical_location)
    }

    pub fn name(&self) -> &str {
        &self.location().name
    }

    pub fn module(&self) -> &Path {
        &self.location().module
    }
}

impl<S> IntoIterator for GStructType<S> {
    type Item = GStructMember<S>;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.members.into_iter()
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord, Hash, Copy)]
pub enum UBitwidth {
    #[serde(rename = "8")]
    B8 = 8,
    #[serde(rename = "16")]
    B16 = 16,
    #[serde(rename = "32")]
    B32 = 32,
    #[serde(rename = "64")]
    B64 = 64,
}

impl UBitwidth {
    pub fn to_usize(self) -> usize {
        self as usize
    }
}

impl From<usize> for UBitwidth {
    fn from(b: usize) -> Self {
        match b {
            8 => UBitwidth::B8,
            16 => UBitwidth::B16,
            32 => UBitwidth::B32,
            64 => UBitwidth::B64,
            _ => unreachable!(),
        }
    }
}

impl fmt::Display for UBitwidth {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_usize())
    }
}

#[allow(clippy::derive_hash_xor_eq)]
#[derive(Clone, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum GType<S> {
    FieldElement,
    Boolean,
    Array(GArrayType<S>),
    Struct(GStructType<S>),
    Tuple(GTupleType<S>),
    Uint(UBitwidth),
    Int,
}

impl<Z: Serialize> Serialize for GType<Z> {
    fn serialize<S>(&self, s: S) -> Result<<S as Serializer>::Ok, <S as Serializer>::Error>
    where
        S: Serializer,
    {
        use serde::ser::Error;

        match self {
            GType::FieldElement => s.serialize_newtype_variant("Type", 0, "type", "field"),
            GType::Boolean => s.serialize_newtype_variant("Type", 1, "type", "bool"),
            GType::Array(array_type) => {
                let mut map = s.serialize_map(Some(2))?;
                map.serialize_entry("type", "array")?;
                map.serialize_entry("components", array_type)?;
                map.end()
            }
            GType::Struct(struct_type) => {
                let mut map = s.serialize_map(Some(2))?;
                map.serialize_entry("type", "struct")?;
                map.serialize_entry("components", struct_type)?;
                map.end()
            }
            GType::Tuple(tuple_type) => {
                let mut map = s.serialize_map(Some(2))?;
                map.serialize_entry("type", "tuple")?;
                map.serialize_entry("components", tuple_type)?;
                map.end()
            }
            GType::Uint(width) => s.serialize_newtype_variant(
                "Type",
                4,
                "type",
                format!("u{}", width.to_usize()).as_str(),
            ),
            GType::Int => Err(S::Error::custom(
                "Cannot serialize Int type as it's not allowed in function signatures".to_string(),
            )),
        }
    }
}

impl<'de, S: Deserialize<'de>> Deserialize<'de> for GType<S> {
    fn deserialize<D>(d: D) -> Result<Self, <D as Deserializer<'de>>::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        #[serde(untagged)]
        enum Components<S> {
            Array(GArrayType<S>),
            Struct(GStructType<S>),
            Tuple(GTupleType<S>),
        }

        #[derive(Deserialize)]
        struct Mapping<S> {
            #[serde(rename = "type")]
            ty: String,
            components: Option<Components<S>>,
        }

        let strict_type =
            |m: Mapping<S>, ty: GType<S>| -> Result<Self, <D as Deserializer<'de>>::Error> {
                match m.components {
                    Some(_) => Err(D::Error::custom(format!(
                        "unexpected `components` field in type {}",
                        m.ty
                    ))),
                    None => Ok(ty),
                }
            };

        let mapping = Mapping::deserialize(d)?;
        match mapping.ty.as_str() {
            "field" => strict_type(mapping, GType::FieldElement),
            "bool" => strict_type(mapping, GType::Boolean),
            "array" => {
                let components = mapping
                    .components
                    .ok_or_else(|| D::Error::custom("missing `components` field".to_string()))?;
                match components {
                    Components::Array(array_type) => Ok(GType::Array(array_type)),
                    _ => Err(D::Error::custom("invalid `components` variant".to_string())),
                }
            }
            "struct" => {
                let components = mapping
                    .components
                    .ok_or_else(|| D::Error::custom("missing `components` field".to_string()))?;
                match components {
                    Components::Struct(struct_type) => Ok(GType::Struct(struct_type)),
                    _ => Err(D::Error::custom("invalid `components` variant".to_string())),
                }
            }
            "tuple" => {
                let components = mapping
                    .components
                    .ok_or_else(|| D::Error::custom("missing `components` field".to_string()))?;
                match components {
                    Components::Tuple(tuple_type) => Ok(GType::Tuple(tuple_type)),
                    _ => Err(D::Error::custom("invalid `components` variant".to_string())),
                }
            }
            "u8" => strict_type(mapping, GType::Uint(UBitwidth::B8)),
            "u16" => strict_type(mapping, GType::Uint(UBitwidth::B16)),
            "u32" => strict_type(mapping, GType::Uint(UBitwidth::B32)),
            "u64" => strict_type(mapping, GType::Uint(UBitwidth::B64)),
            t => Err(D::Error::custom(format!("invalid type `{}`", t))),
        }
    }
}

pub type DeclarationType<'ast, T> = GType<DeclarationConstant<'ast, T>>;
pub type ConcreteType = GType<u32>;
pub type Type<'ast, T> = GType<UExpression<'ast, T>>;

impl<S, R: PartialEq<S>> PartialEq<GType<S>> for GType<R> {
    fn eq(&self, other: &GType<S>) -> bool {
        use self::GType::*;

        match (self, other) {
            (Array(l), Array(r)) => l == r,
            (Struct(l), Struct(r)) => l == r,
            (FieldElement, FieldElement) | (Boolean, Boolean) => true,
            (Uint(l), Uint(r)) => l == r,
            (Tuple(l), Tuple(r)) => l == r,
            _ => false,
        }
    }
}

pub fn try_from_g_type<T: TryInto<U>, U>(t: GType<T>) -> Result<GType<U>, SpecializationError> {
    match t {
        GType::FieldElement => Ok(GType::FieldElement),
        GType::Boolean => Ok(GType::Boolean),
        GType::Int => Ok(GType::Int),
        GType::Uint(bitwidth) => Ok(GType::Uint(bitwidth)),
        GType::Array(array_type) => Ok(GType::Array(try_from_g_array_type(array_type)?)),
        GType::Struct(struct_type) => Ok(GType::Struct(try_from_g_struct_type(struct_type)?)),
        GType::Tuple(tuple_type) => Ok(GType::Tuple(try_from_g_tuple_type(tuple_type)?)),
    }
}

impl<'ast, T> TryFrom<Type<'ast, T>> for ConcreteType {
    type Error = SpecializationError;

    fn try_from(t: Type<'ast, T>) -> Result<Self, Self::Error> {
        try_from_g_type(t)
    }
}

impl<'ast, T> From<ConcreteType> for Type<'ast, T> {
    fn from(t: ConcreteType) -> Self {
        try_from_g_type(t).unwrap()
    }
}

impl<'ast, T> From<ConcreteType> for DeclarationType<'ast, T> {
    fn from(t: ConcreteType) -> Self {
        try_from_g_type(t).unwrap()
    }
}

impl<S, U: Into<S>> From<(GType<S>, U)> for GArrayType<S> {
    fn from(tup: (GType<S>, U)) -> Self {
        GArrayType {
            ty: box tup.0,
            size: box tup.1.into(),
        }
    }
}

impl<S> GArrayType<S> {
    pub fn new<U: Into<S>>(ty: GType<S>, size: U) -> Self {
        GArrayType {
            ty: box ty,
            size: box size.into(),
        }
    }
}

impl<S> GStructMember<S> {
    pub fn new(id: String, ty: GType<S>) -> Self {
        GStructMember {
            id,
            ty: Box::new(ty),
        }
    }
}

impl<S: fmt::Display> fmt::Display for GType<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            GType::FieldElement => write!(f, "field"),
            GType::Boolean => write!(f, "bool"),
            GType::Uint(ref bitwidth) => write!(f, "u{}", bitwidth),
            GType::Int => write!(f, "{{integer}}"),
            GType::Array(ref array_type) => write!(f, "{}", array_type),
            GType::Struct(ref struct_type) => write!(f, "{}", struct_type),
            GType::Tuple(ref tuple_type) => write!(f, "{}", tuple_type),
        }
    }
}

impl<S: fmt::Display> fmt::Display for GStructType<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}{}",
            self.name(),
            if !self.generics.is_empty() {
                format!(
                    "<{}>",
                    self.generics
                        .iter()
                        .map(|g| g
                            .as_ref()
                            .map(|g| g.to_string())
                            .unwrap_or_else(|| '_'.to_string()))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            } else {
                "".to_string()
            }
        )
    }
}

impl<S> GType<S> {
    pub fn array<U: Into<GArrayType<S>>>(array_ty: U) -> Self {
        GType::Array(array_ty.into())
    }

    pub fn tuple<U: Into<GTupleType<S>>>(tuple_ty: U) -> Self {
        GType::Tuple(tuple_ty.into())
    }

    pub fn struc<U: Into<GStructType<S>>>(struct_ty: U) -> Self {
        GType::Struct(struct_ty.into())
    }

    pub fn uint<W: Into<UBitwidth>>(b: W) -> Self {
        GType::Uint(b.into())
    }

    pub fn is_empty_tuple(&self) -> bool {
        matches!(self, GType::Tuple(ty) if ty.elements.is_empty())
    }
}

impl<'ast, T: fmt::Display + PartialEq + fmt::Debug> Type<'ast, T> {
    pub fn can_be_specialized_to(&self, other: &DeclarationType<'ast, T>) -> bool {
        use self::GType::*;

        if other == self {
            true
        } else {
            match (self, other) {
                (Int, FieldElement) | (Int, Uint(..)) => true,
                (Array(l), Array(r)) => match l.ty.can_be_specialized_to(&r.ty) {
                    true => {
                        // check the size if types match
                        match (&l.size.as_inner(), &*r.size) {
                            // compare the sizes for concrete ones
                            (UExpressionInner::Value(v), DeclarationConstant::Concrete(c)) => {
                                (*v as u32) == *c
                            }
                            _ => true,
                        }
                    }
                    _ => false,
                },
                (Struct(l), Struct(r)) => {
                    l.canonical_location == r.canonical_location
                        && l.members
                            .iter()
                            .zip(r.members.iter())
                            .all(|(m, d_m)| m.ty.can_be_specialized_to(&*d_m.ty))
                }
                _ => false,
            }
        }
    }
}

impl ConcreteType {
    // the number of field elements the type maps to
    pub fn get_primitive_count(&self) -> usize {
        match self {
            GType::FieldElement => 1,
            GType::Boolean => 1,
            GType::Uint(_) => 1,
            GType::Array(array_type) => {
                *array_type.size as usize * array_type.ty.get_primitive_count()
            }
            GType::Tuple(tuple_type) => tuple_type
                .elements
                .iter()
                .map(|e| e.get_primitive_count())
                .sum(),
            GType::Int => unreachable!(),
            GType::Struct(struct_type) => struct_type
                .iter()
                .map(|member| member.ty.get_primitive_count())
                .sum(),
        }
    }
}

pub type FunctionIdentifier<'ast> = &'ast str;

#[derive(PartialEq, Eq, Hash, Debug, Clone, PartialOrd, Ord)]
pub struct GFunctionKey<'ast, S> {
    pub module: OwnedTypedModuleId,
    pub id: FunctionIdentifier<'ast>,
    pub signature: GSignature<S>,
}

pub type DeclarationFunctionKey<'ast, T> = GFunctionKey<'ast, DeclarationConstant<'ast, T>>;
pub type ConcreteFunctionKey<'ast> = GFunctionKey<'ast, u32>;
pub type FunctionKey<'ast, T> = GFunctionKey<'ast, UExpression<'ast, T>>;

impl<'ast, S: fmt::Display> fmt::Display for GFunctionKey<'ast, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}/{}{}", self.module.display(), self.id, self.signature)
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, PartialOrd, Ord)]
pub struct GGenericsAssignment<'ast, S>(pub BTreeMap<GenericIdentifier<'ast>, S>);

pub type ConcreteGenericsAssignment<'ast> = GGenericsAssignment<'ast, u32>;
pub type GenericsAssignment<'ast, T> = GGenericsAssignment<'ast, UExpression<'ast, T>>;

impl<'ast, S> Default for GGenericsAssignment<'ast, S> {
    fn default() -> Self {
        GGenericsAssignment(BTreeMap::new())
    }
}

impl<'ast, S: fmt::Display> fmt::Display for GGenericsAssignment<'ast, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            self.0
                .iter()
                .map(|(k, v)| format!("{}: {}", k, v))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl<'ast, T> PartialEq<DeclarationFunctionKey<'ast, T>> for ConcreteFunctionKey<'ast> {
    fn eq(&self, other: &DeclarationFunctionKey<'ast, T>) -> bool {
        self.module == other.module && self.id == other.id && self.signature == other.signature
    }
}

fn try_from_g_function_key<T: TryInto<U>, U>(
    k: GFunctionKey<T>,
) -> Result<GFunctionKey<U>, SpecializationError> {
    Ok(GFunctionKey {
        module: k.module,
        signature: signature::try_from_g_signature(k.signature)?,
        id: k.id,
    })
}

impl<'ast, T> TryFrom<FunctionKey<'ast, T>> for ConcreteFunctionKey<'ast> {
    type Error = SpecializationError;

    fn try_from(k: FunctionKey<'ast, T>) -> Result<Self, Self::Error> {
        try_from_g_function_key(k)
    }
}

impl<'ast, T> From<ConcreteFunctionKey<'ast>> for FunctionKey<'ast, T> {
    fn from(k: ConcreteFunctionKey<'ast>) -> Self {
        try_from_g_function_key(k).unwrap()
    }
}

impl<'ast, T> From<ConcreteFunctionKey<'ast>> for DeclarationFunctionKey<'ast, T> {
    fn from(k: ConcreteFunctionKey<'ast>) -> Self {
        try_from_g_function_key(k).unwrap()
    }
}

impl<'ast, S> GFunctionKey<'ast, S> {
    pub fn with_location<T: Into<OwnedTypedModuleId>, U: Into<FunctionIdentifier<'ast>>>(
        module: T,
        id: U,
    ) -> Self {
        GFunctionKey {
            module: module.into(),
            id: id.into(),
            signature: GSignature::new(),
        }
    }

    pub fn signature(mut self, signature: GSignature<S>) -> Self {
        self.signature = signature;
        self
    }

    pub fn id<U: Into<FunctionIdentifier<'ast>>>(mut self, id: U) -> Self {
        self.id = id.into();
        self
    }

    pub fn module<T: Into<OwnedTypedModuleId>>(mut self, module: T) -> Self {
        self.module = module.into();
        self
    }
}

use std::collections::btree_map::Entry;

// check an optional generic value against the corresponding declaration constant
// if None is provided, return true
// if some value is provided, insert it into the map or check that it doesn't conflict if a value is already thereq
pub fn check_generic<'ast, T, S: Clone + PartialEq + PartialEq<u32>>(
    generic: &DeclarationConstant<'ast, T>,
    value: Option<&S>,
    constants: &mut GGenericsAssignment<'ast, S>,
) -> bool {
    value
        .map(|value| match generic {
            // if the generic is an identifier, we insert into the map, or check if the concrete size
            // matches if this identifier is already in the map
            DeclarationConstant::Generic(id) => match constants.0.entry(id.clone()) {
                Entry::Occupied(e) => *e.get() == *value,
                Entry::Vacant(e) => {
                    e.insert(value.clone());
                    true
                }
            },
            DeclarationConstant::Concrete(generic) => *value == *generic,
            // in the case of a constant, we do not know the value yet, so we optimistically assume it's correct
            // if it does not match, it will be caught during inlining
            DeclarationConstant::Constant(..) => true,
            DeclarationConstant::Expression(e) => match e {
                TypedExpression::Uint(e) => match e.as_inner() {
                    UExpressionInner::Value(v) => *value == *v as u32,
                    _ => true,
                },
                _ => unreachable!(),
            },
        })
        .unwrap_or(true)
}

pub fn check_type<'ast, T, S: Clone + PartialEq + PartialEq<u32>>(
    decl_ty: &DeclarationType<'ast, T>,
    ty: &GType<S>,
    constants: &mut GGenericsAssignment<'ast, S>,
) -> bool {
    match (decl_ty, ty) {
        (DeclarationType::Array(t0), GType::Array(t1)) => {
            // both the inner type and the size must match
            check_type(&t0.ty, &t1.ty, constants)
                && check_generic(&*t0.size, Some(&*t1.size), constants)
        }
        (DeclarationType::FieldElement, GType::FieldElement)
        | (DeclarationType::Boolean, GType::Boolean) => true,
        (DeclarationType::Uint(b0), GType::Uint(b1)) => b0 == b1,
        (DeclarationType::Struct(s0), GType::Struct(s1)) => {
            s0.canonical_location == s1.canonical_location
                && s0
                    .generics
                    .iter()
                    .zip(s1.generics.iter())
                    .all(|(g0, g1)| check_generic(g0.as_ref().unwrap(), g1.as_ref(), constants))
        }
        (DeclarationType::Tuple(s0), GType::Tuple(s1)) => {
            s0.elements.len() == s1.elements.len()
                && s0
                    .elements
                    .iter()
                    .zip(s1.elements.iter())
                    .all(|(t0, t1)| check_type(t0, t1, constants))
        }
        _ => false,
    }
}

impl<'ast, T> From<CanonicalConstantIdentifier<'ast>> for UExpression<'ast, T> {
    fn from(c: CanonicalConstantIdentifier<'ast>) -> Self {
        UExpressionInner::Identifier(Identifier::from(CoreIdentifier::Constant(c)))
            .annotate(UBitwidth::B32)
    }
}

impl<'ast, T> From<CanonicalConstantIdentifier<'ast>> for DeclarationConstant<'ast, T> {
    fn from(c: CanonicalConstantIdentifier<'ast>) -> Self {
        DeclarationConstant::Constant(c)
    }
}

pub fn specialize_declaration_type<
    'ast,
    T: Clone,
    S: Clone + PartialEq + From<u32> + From<CanonicalConstantIdentifier<'ast>>,
>(
    decl_ty: DeclarationType<'ast, T>,
    generics: &GGenericsAssignment<'ast, S>,
) -> Result<GType<S>, GenericIdentifier<'ast>> {
    Ok(match decl_ty {
        DeclarationType::Int => unreachable!(),
        DeclarationType::Array(t0) => {
            let ty = specialize_declaration_type(*t0.ty, generics)?;
            let size = t0.size.map(generics)?;

            GType::Array(GArrayType::new(ty, size))
        }
        DeclarationType::Tuple(t0) => {
            let elements = t0
                .elements
                .into_iter()
                .map(|t| specialize_declaration_type(t, generics))
                .collect::<Result<Vec<_>, _>>()?;

            GType::Tuple(GTupleType { elements })
        }
        DeclarationType::FieldElement => GType::FieldElement,
        DeclarationType::Boolean => GType::Boolean,
        DeclarationType::Uint(b0) => GType::Uint(b0),
        DeclarationType::Struct(s0) => {
            // here we specialize Foo<Generics> {FooDef<InsideGenerics>} with some values for Generics
            // we need to remap these values for InsideGenerics to then visit the members

            let inside_generics = GGenericsAssignment(
                s0.generics
                    .clone()
                    .into_iter()
                    .enumerate()
                    .map(|(index, g)| {
                        (
                            GenericIdentifier::without_name().with_index(index),
                            g.map(|g| g.map(generics).unwrap()).unwrap(),
                        )
                    })
                    .collect(),
            );

            GType::Struct(GStructType {
                members: s0
                    .members
                    .into_iter()
                    .map(|m| {
                        let id = m.id;
                        specialize_declaration_type(*m.ty, &inside_generics)
                            .map(|ty| GStructMember { ty: box ty, id })
                    })
                    .collect::<Result<_, _>>()?,
                generics: s0
                    .generics
                    .into_iter()
                    .map(|g| match g {
                        Some(constant) => constant.map(generics).map(Some),
                        _ => Ok(None),
                    })
                    .collect::<Result<_, _>>()?,
                canonical_location: s0.canonical_location,
                location: s0.location,
            })
        }
    })
}

pub use self::signature::{
    try_from_g_signature, ConcreteSignature, DeclarationSignature, GSignature, Signature,
};

use super::ShadowedIdentifier;

pub mod signature {
    use super::*;
    use std::fmt;

    #[derive(Clone, Serialize, Deserialize, Eq, Debug)]
    pub struct GSignature<S> {
        pub generics: Vec<Option<S>>,
        pub inputs: Vec<GType<S>>,
        pub output: Box<GType<S>>,
    }

    impl<S> Default for GSignature<S> {
        fn default() -> Self {
            Self {
                generics: vec![],
                inputs: vec![],
                output: box GType::Tuple(GTupleType::new(vec![])),
            }
        }
    }

    impl<S: PartialEq> PartialEq for GSignature<S> {
        fn eq(&self, other: &Self) -> bool {
            self.inputs == other.inputs && self.output == other.output
        }
    }

    impl<S: PartialOrd> PartialOrd for GSignature<S> {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            self.inputs
                .partial_cmp(&other.inputs)
                .map(|c| self.output.partial_cmp(&other.output).map(|d| c.then(d)))
                .unwrap()
        }
    }

    impl<S: Ord> Ord for GSignature<S> {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            self.partial_cmp(other).unwrap()
        }
    }

    impl<S: Hash> Hash for GSignature<S> {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            self.inputs.hash(state);
            self.output.hash(state);
        }
    }

    pub type DeclarationSignature<'ast, T> = GSignature<DeclarationConstant<'ast, T>>;
    pub type ConcreteSignature = GSignature<u32>;
    pub type Signature<'ast, T> = GSignature<UExpression<'ast, T>>;

    impl<'ast, T> PartialEq<DeclarationSignature<'ast, T>> for ConcreteSignature {
        fn eq(&self, other: &DeclarationSignature<'ast, T>) -> bool {
            // we keep track of the value of constants in a map, as a given constant can only have one value
            let mut constants = ConcreteGenericsAssignment::default();

            other
                .inputs
                .iter()
                .chain(std::iter::once(&*other.output))
                .zip(self.inputs.iter().chain(std::iter::once(&*self.output)))
                .all(|(decl_ty, ty)| check_type::<T, u32>(decl_ty, ty, &mut constants))
        }
    }

    impl<'ast, T: Clone + PartialEq> DeclarationSignature<'ast, T> {
        pub fn specialize(
            &self,
            values: Vec<Option<u32>>,
            signature: &ConcreteSignature,
        ) -> Result<ConcreteGenericsAssignment<'ast>, SpecializationError> {
            // we keep track of the value of constants in a map, as a given constant can only have one value
            let mut constants = ConcreteGenericsAssignment::default();

            assert_eq!(self.generics.len(), values.len());
            assert_eq!(self.inputs.len(), signature.inputs.len());

            let decl_generics = self.generics.iter().map(|g| match g.clone().unwrap() {
                DeclarationConstant::Generic(g) => g,
                _ => unreachable!(),
            });

            constants.0.extend(
                decl_generics
                    .zip(values.into_iter())
                    .filter_map(|(g, v)| v.map(|v| (g, v))),
            );

            let condition = self
                .inputs
                .iter()
                .chain(std::iter::once(&*self.output))
                .zip(
                    signature
                        .inputs
                        .iter()
                        .chain(std::iter::once(&*signature.output)),
                )
                .all(|(decl_ty, ty)| check_type(decl_ty, ty, &mut constants));

            if constants.0.len() != self.generics.len() {
                return Err(SpecializationError);
            }

            match condition {
                true => Ok(constants),
                false => Err(SpecializationError),
            }
        }

        pub fn get_output_type(
            &self,
            generics: Vec<Option<UExpression<'ast, T>>>,
            inputs: Vec<Type<'ast, T>>,
        ) -> Result<Type<'ast, T>, GenericIdentifier<'ast>> {
            // we keep track of the value of constants in a map, as a given constant can only have one value
            let mut constants = GenericsAssignment::default();

            // initialise the map with the explicitly provided generics
            constants
                .0
                .extend(self.generics.iter().zip(generics).filter_map(|(g, v)| {
                    // only add to the map when there's indeed a generic value being provided
                    v.map(|v| {
                        (
                            match g.clone().unwrap() {
                                DeclarationConstant::Generic(g) => g,
                                _ => unreachable!(),
                            },
                            v,
                        )
                    })
                }));

            // fill the map with the inputs
            let _ = self
                .inputs
                .iter()
                .zip(inputs.iter())
                .all(|(decl_ty, ty)| check_type(decl_ty, ty, &mut constants));

            // get the specialized output
            specialize_declaration_type(*self.output.clone(), &constants)
        }
    }

    pub fn try_from_g_signature<T: TryInto<U>, U>(
        t: GSignature<T>,
    ) -> Result<GSignature<U>, SpecializationError> {
        Ok(GSignature {
            generics: t
                .generics
                .into_iter()
                .map(|g| match g {
                    Some(g) => g.try_into().map(Some).map_err(|_| SpecializationError),
                    None => Ok(None),
                })
                .collect::<Result<_, _>>()?,
            inputs: t
                .inputs
                .into_iter()
                .map(try_from_g_type)
                .collect::<Result<_, _>>()?,
            output: box try_from_g_type(*t.output)?,
        })
    }

    impl<'ast, T> TryFrom<Signature<'ast, T>> for ConcreteSignature {
        type Error = SpecializationError;

        fn try_from(s: Signature<'ast, T>) -> Result<Self, Self::Error> {
            try_from_g_signature(s)
        }
    }

    impl<'ast, T> From<ConcreteSignature> for Signature<'ast, T> {
        fn from(s: ConcreteSignature) -> Self {
            try_from_g_signature(s).unwrap()
        }
    }

    impl<'ast, T> From<ConcreteSignature> for DeclarationSignature<'ast, T> {
        fn from(s: ConcreteSignature) -> Self {
            try_from_g_signature(s).unwrap()
        }
    }

    impl<S: fmt::Display> fmt::Display for GSignature<S> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            if !self.generics.is_empty() {
                write!(
                    f,
                    "<{}>",
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

            write!(f, "(")?;
            for (i, t) in self.inputs.iter().enumerate() {
                write!(f, "{}", t)?;
                if i < self.inputs.len() - 1 {
                    write!(f, ", ")?;
                }
            }
            write!(f, ") -> {}", self.output)
        }
    }

    impl<S> GSignature<S> {
        pub fn new() -> GSignature<S> {
            Self::default()
        }

        pub fn generics(mut self, generics: Vec<Option<S>>) -> Self {
            self.generics = generics;
            self
        }

        pub fn inputs(mut self, inputs: Vec<GType<S>>) -> Self {
            self.inputs = inputs;
            self
        }

        pub fn output(mut self, output: GType<S>) -> Self {
            self.output = Box::new(output);
            self
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use zokrates_field::Bn128Field;

        #[test]
        fn signature() {
            let s = ConcreteSignature::new()
                .inputs(vec![ConcreteType::FieldElement, ConcreteType::Boolean])
                .output(ConcreteType::Boolean);

            assert_eq!(s.to_string(), String::from("(field, bool) -> bool"));
        }

        #[test]
        fn signature_equivalence() {
            // check equivalence of:
            // <P>(field[P])
            // <Q>(field[Q])

            let generic1 = DeclarationSignature::<Bn128Field>::new()
                .generics(vec![Some(
                    GenericIdentifier::with_name("P").with_index(0).into(),
                )])
                .inputs(vec![DeclarationType::array(DeclarationArrayType::new(
                    DeclarationType::FieldElement,
                    GenericIdentifier::with_name("P").with_index(0),
                ))]);
            let generic2 = DeclarationSignature::new()
                .generics(vec![Some(
                    GenericIdentifier::with_name("Q").with_index(0).into(),
                )])
                .inputs(vec![DeclarationType::array(DeclarationArrayType::new(
                    DeclarationType::FieldElement,
                    GenericIdentifier::with_name("Q").with_index(0),
                ))]);

            assert_eq!(generic1, generic2);
            assert_eq!(
                {
                    let mut hasher = std::collections::hash_map::DefaultHasher::new();
                    generic1.hash(&mut hasher);
                    hasher.finish()
                },
                {
                    let mut hasher = std::collections::hash_map::DefaultHasher::new();
                    generic2.hash(&mut hasher);
                    hasher.finish()
                }
            );
            assert_eq!(
                generic1.partial_cmp(&generic2),
                Some(std::cmp::Ordering::Equal)
            );
            assert_eq!(generic1.cmp(&generic2), std::cmp::Ordering::Equal);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn array() {
        let t = ConcreteType::Array(ConcreteArrayType::new(ConcreteType::FieldElement, 42u32));
        assert_eq!(t.get_primitive_count(), 42);
    }

    #[test]
    fn array_display() {
        // field[1][2]
        let t = ConcreteType::Array(ConcreteArrayType::new(
            ConcreteType::Array(ConcreteArrayType::new(ConcreteType::FieldElement, 2u32)),
            1u32,
        ));
        assert_eq!(format!("{}", t), "field[1][2]");
    }
}
