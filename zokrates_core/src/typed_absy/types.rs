use crate::typed_absy::{Identifier, OwnedTypedModuleId, UExpression, UExpressionInner};
use crate::typed_absy::{TryFrom, TryInto};
use serde::{de::Error, ser::SerializeMap, Deserialize, Deserializer, Serialize, Serializer};
use std::collections::BTreeMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};

pub trait IntoTypes<'ast, T> {
    fn into_types(self) -> Types<'ast, T>;
}

impl<'ast, T> IntoTypes<'ast, T> for Type<'ast, T> {
    fn into_types(self) -> Types<'ast, T> {
        Types { inner: vec![self] }
    }
}

impl<'ast, T> IntoTypes<'ast, T> for StructType<'ast, T> {
    fn into_types(self) -> Types<'ast, T> {
        Types {
            inner: vec![Type::Struct(self)],
        }
    }
}

impl<'ast, T> IntoTypes<'ast, T> for ArrayType<'ast, T> {
    fn into_types(self) -> Types<'ast, T> {
        Types {
            inner: vec![Type::Array(self)],
        }
    }
}

impl<'ast, T> IntoTypes<'ast, T> for UBitwidth {
    fn into_types(self) -> Types<'ast, T> {
        Types {
            inner: vec![Type::Uint(self)],
        }
    }
}

impl<'ast, T> IntoTypes<'ast, T> for Types<'ast, T> {
    fn into_types(self) -> Types<'ast, T> {
        self
    }
}

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub struct Types<'ast, T> {
    pub inner: Vec<Type<'ast, T>>,
}

impl<'ast, T> Types<'ast, T> {
    pub fn new(types: Vec<Type<'ast, T>>) -> Self {
        Self { inner: types }
    }
}

#[derive(Debug, Clone, Eq, Ord)]
pub struct GenericIdentifier<'ast> {
    pub name: &'ast str,
    pub index: usize,
}

impl<'ast> GenericIdentifier<'ast> {
    pub fn with_name(name: &'ast str) -> Self {
        Self { name, index: 0 }
    }

    pub fn index(mut self, index: usize) -> Self {
        self.index = index;
        self
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

impl<'ast> Hash for GenericIdentifier<'ast> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.index.hash(state);
    }
}

impl<'ast> fmt::Display for GenericIdentifier<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Debug)]
pub struct SpecializationError;

pub type ConstantIdentifier<'ast> = &'ast str;

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct CanonicalConstantIdentifier<'ast> {
    pub module: OwnedTypedModuleId,
    pub id: ConstantIdentifier<'ast>,
    pub ty: Box<DeclarationType<'ast>>,
}

impl<'ast> CanonicalConstantIdentifier<'ast> {
    pub fn new(
        id: ConstantIdentifier<'ast>,
        module: OwnedTypedModuleId,
        ty: DeclarationType<'ast>,
    ) -> Self {
        CanonicalConstantIdentifier {
            module,
            id,
            ty: box ty,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DeclarationConstant<'ast> {
    Generic(GenericIdentifier<'ast>),
    Concrete(u32),
    Constant(CanonicalConstantIdentifier<'ast>),
}

impl<'ast, T> PartialEq<UExpression<'ast, T>> for DeclarationConstant<'ast> {
    fn eq(&self, other: &UExpression<'ast, T>) -> bool {
        match (self, other.as_inner()) {
            (DeclarationConstant::Concrete(c), UExpressionInner::Value(v)) => *c == *v as u32,
            _ => true,
        }
    }
}

impl<'ast, T> PartialEq<DeclarationConstant<'ast>> for UExpression<'ast, T> {
    fn eq(&self, other: &DeclarationConstant<'ast>) -> bool {
        other.eq(self)
    }
}

impl<'ast> From<u32> for DeclarationConstant<'ast> {
    fn from(e: u32) -> Self {
        DeclarationConstant::Concrete(e)
    }
}

impl<'ast> From<usize> for DeclarationConstant<'ast> {
    fn from(e: usize) -> Self {
        DeclarationConstant::Concrete(e as u32)
    }
}

impl<'ast> From<GenericIdentifier<'ast>> for DeclarationConstant<'ast> {
    fn from(e: GenericIdentifier<'ast>) -> Self {
        DeclarationConstant::Generic(e)
    }
}

impl<'ast> fmt::Display for DeclarationConstant<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            DeclarationConstant::Generic(i) => write!(f, "{}", i),
            DeclarationConstant::Concrete(v) => write!(f, "{}", v),
            DeclarationConstant::Constant(v) => write!(f, "{}/{}", v.module.display(), v.id),
        }
    }
}

impl<'ast, T> From<usize> for UExpression<'ast, T> {
    fn from(i: usize) -> Self {
        UExpressionInner::Value(i as u128).annotate(UBitwidth::B32)
    }
}

impl<'ast, T> From<DeclarationConstant<'ast>> for UExpression<'ast, T> {
    fn from(c: DeclarationConstant<'ast>) -> Self {
        match c {
            DeclarationConstant::Generic(i) => {
                UExpressionInner::Identifier(i.name.into()).annotate(UBitwidth::B32)
            }
            DeclarationConstant::Concrete(v) => {
                UExpressionInner::Value(v as u128).annotate(UBitwidth::B32)
            }
            DeclarationConstant::Constant(v) => {
                UExpressionInner::Identifier(Identifier::from(v.id)).annotate(UBitwidth::B32)
            }
        }
    }
}

impl<'ast, T> TryInto<usize> for UExpression<'ast, T> {
    type Error = SpecializationError;

    fn try_into(self) -> Result<usize, Self::Error> {
        assert_eq!(self.bitwidth, UBitwidth::B32);

        match self.into_inner() {
            UExpressionInner::Value(v) => Ok(v as usize),
            _ => Err(SpecializationError),
        }
    }
}

impl<'ast> TryInto<usize> for DeclarationConstant<'ast> {
    type Error = SpecializationError;

    fn try_into(self) -> Result<usize, Self::Error> {
        match self {
            DeclarationConstant::Concrete(v) => Ok(v as usize),
            _ => Err(SpecializationError),
        }
    }
}

pub type MemberId = String;

#[derive(Debug, Clone, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub struct GStructMember<S> {
    #[serde(rename = "name")]
    pub id: MemberId,
    #[serde(flatten)]
    pub ty: Box<GType<S>>,
}

pub type DeclarationStructMember<'ast> = GStructMember<DeclarationConstant<'ast>>;
pub type ConcreteStructMember = GStructMember<usize>;
pub type StructMember<'ast, T> = GStructMember<UExpression<'ast, T>>;

impl<'ast, S, R: PartialEq<S>> PartialEq<GStructMember<S>> for GStructMember<R> {
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

// impl<'ast> From<ConcreteStructMember> for DeclarationStructMember<'ast> {
//     fn from(t: ConcreteStructMember) -> Self {
//         try_from_g_struct_member(t).unwrap()
//     }
// }

// impl<'ast, T> From<DeclarationStructMember<'ast>> for StructMember<'ast, T> {
//     fn from(t: DeclarationStructMember<'ast>) -> Self {
//         try_from_g_struct_member(t).unwrap()
//     }
// }

#[derive(Clone, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord, Debug)]
pub struct GArrayType<S> {
    pub size: S,
    #[serde(flatten)]
    pub ty: Box<GType<S>>,
}

pub type DeclarationArrayType<'ast> = GArrayType<DeclarationConstant<'ast>>;
pub type ConcreteArrayType = GArrayType<usize>;
pub type ArrayType<'ast, T> = GArrayType<UExpression<'ast, T>>;

impl<'ast, S, R: PartialEq<S>> PartialEq<GArrayType<S>> for GArrayType<R> {
    fn eq(&self, other: &GArrayType<S>) -> bool {
        *self.ty == *other.ty && self.size == other.size
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
                GType::Array(array_type) => fmt_aux(f, &array_type, acc),
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

        fmt_aux(f, &self, acc)
    }
}

fn try_from_g_array_type<T: TryInto<U>, U>(
    t: GArrayType<T>,
) -> Result<GArrayType<U>, SpecializationError> {
    Ok(GArrayType {
        size: t.size.try_into().map_err(|_| SpecializationError)?,
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

#[derive(Debug, Clone, Hash, Serialize, Deserialize, PartialOrd, Ord, Eq, PartialEq)]
pub struct StructLocation {
    #[serde(skip)]
    pub module: PathBuf,
    pub name: String,
}

impl<'ast> From<ConcreteArrayType> for DeclarationArrayType<'ast> {
    fn from(t: ConcreteArrayType) -> Self {
        try_from_g_array_type(t).unwrap()
    }
}

impl<'ast, T> From<DeclarationArrayType<'ast>> for ArrayType<'ast, T> {
    fn from(t: DeclarationArrayType<'ast>) -> Self {
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

pub type DeclarationStructType<'ast> = GStructType<DeclarationConstant<'ast>>;
pub type ConcreteStructType = GStructType<usize>;
pub type StructType<'ast, T> = GStructType<UExpression<'ast, T>>;

impl<'ast, S, R: PartialEq<S>> PartialEq<GStructType<S>> for GStructType<R> {
    fn eq(&self, other: &GStructType<S>) -> bool {
        self.canonical_location == other.canonical_location
            && self
                .generics
                .iter()
                .zip(other.generics.iter())
                .all(|(a, b)| match (a, b) {
                    (Some(a), Some(b)) => a == b,
                    (None, None) => true,
                    _ => false,
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

impl<'ast> From<ConcreteStructType> for DeclarationStructType<'ast> {
    fn from(t: ConcreteStructType) -> Self {
        try_from_g_struct_type(t).unwrap()
    }
}

// impl<'ast, T> From<DeclarationStructType<'ast>> for StructType<'ast, T> {
//     fn from(t: DeclarationStructType<'ast>) -> Self {
//         try_from_g_struct_type(t).unwrap()
//     }
// }

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
        &self.location.as_ref().unwrap_or(&self.canonical_location)
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
        self as u32 as usize
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

#[derive(Clone, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum GType<S> {
    FieldElement,
    Boolean,
    Array(GArrayType<S>),
    Struct(GStructType<S>),
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
            "u8" => strict_type(mapping, GType::Uint(UBitwidth::B8)),
            "u16" => strict_type(mapping, GType::Uint(UBitwidth::B16)),
            "u32" => strict_type(mapping, GType::Uint(UBitwidth::B32)),
            "u64" => strict_type(mapping, GType::Uint(UBitwidth::B64)),
            t => Err(D::Error::custom(format!("invalid type `{}`", t))),
        }
    }
}

pub type DeclarationType<'ast> = GType<DeclarationConstant<'ast>>;
pub type ConcreteType = GType<usize>;
pub type Type<'ast, T> = GType<UExpression<'ast, T>>;

impl<'ast, S, R: PartialEq<S>> PartialEq<GType<S>> for GType<R> {
    fn eq(&self, other: &GType<S>) -> bool {
        use self::GType::*;

        match (self, other) {
            (Array(l), Array(r)) => l == r,
            (Struct(l), Struct(r)) => l == r,
            (FieldElement, FieldElement) | (Boolean, Boolean) => true,
            (Uint(l), Uint(r)) => l == r,
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

impl<'ast> From<ConcreteType> for DeclarationType<'ast> {
    fn from(t: ConcreteType) -> Self {
        try_from_g_type(t).unwrap()
    }
}

impl<S, U: Into<S>> From<(GType<S>, U)> for GArrayType<S> {
    fn from(tup: (GType<S>, U)) -> Self {
        GArrayType {
            ty: box tup.0,
            size: tup.1.into(),
        }
    }
}

impl<S> GArrayType<S> {
    pub fn new<U: Into<S>>(ty: GType<S>, size: U) -> Self {
        GArrayType {
            ty: Box::new(ty),
            size: size.into(),
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

    pub fn struc<U: Into<GStructType<S>>>(struct_ty: U) -> Self {
        GType::Struct(struct_ty.into())
    }

    pub fn uint<W: Into<UBitwidth>>(b: W) -> Self {
        GType::Uint(b.into())
    }
}

impl<'ast, T: fmt::Display + PartialEq + fmt::Debug> Type<'ast, T> {
    pub fn can_be_specialized_to(&self, other: &DeclarationType) -> bool {
        use self::GType::*;

        if other == self {
            true
        } else {
            match (self, other) {
                (Int, FieldElement) | (Int, Uint(..)) => true,
                (Array(l), Array(r)) => match l.ty.can_be_specialized_to(&r.ty) {
                    true => {
                        // check the size if types match
                        match (&l.size.as_inner(), &r.size) {
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
    fn to_slug(&self) -> String {
        match self {
            GType::FieldElement => String::from("f"),
            GType::Int => unreachable!(),
            GType::Boolean => String::from("b"),
            GType::Uint(bitwidth) => format!("u{}", bitwidth),
            GType::Array(array_type) => format!("{}[{}]", array_type.ty.to_slug(), array_type.size),
            GType::Struct(struct_type) => format!(
                "{{{}}}",
                struct_type
                    .iter()
                    .map(|member| format!("{}:{}", member.id, member.ty))
                    .collect::<Vec<_>>()
                    .join(",")
            ),
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
            GType::Array(array_type) => array_type.size * array_type.ty.get_primitive_count(),
            GType::Int => unreachable!(),
            GType::Struct(struct_type) => struct_type
                .iter()
                .map(|member| member.ty.get_primitive_count())
                .sum(),
        }
    }
}

pub type FunctionIdentifier<'ast> = &'ast str;

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct GFunctionKey<'ast, S> {
    pub module: OwnedTypedModuleId,
    pub id: FunctionIdentifier<'ast>,
    pub signature: GSignature<S>,
}

pub type DeclarationFunctionKey<'ast> = GFunctionKey<'ast, DeclarationConstant<'ast>>;
pub type ConcreteFunctionKey<'ast> = GFunctionKey<'ast, usize>;
pub type FunctionKey<'ast, T> = GFunctionKey<'ast, UExpression<'ast, T>>;

impl<'ast, S: fmt::Display> fmt::Display for GFunctionKey<'ast, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}/{}{}", self.module.display(), self.id, self.signature)
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct GGenericsAssignment<'ast, S>(pub BTreeMap<GenericIdentifier<'ast>, S>);

pub type ConcreteGenericsAssignment<'ast> = GGenericsAssignment<'ast, usize>;
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

impl<'ast> PartialEq<DeclarationFunctionKey<'ast>> for ConcreteFunctionKey<'ast> {
    fn eq(&self, other: &DeclarationFunctionKey<'ast>) -> bool {
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

impl<'ast> From<ConcreteFunctionKey<'ast>> for DeclarationFunctionKey<'ast> {
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

impl<'ast> ConcreteFunctionKey<'ast> {
    pub fn to_slug(&self) -> String {
        format!(
            "{}/{}_{}",
            self.module.display(),
            self.id,
            self.signature.to_slug()
        )
    }
}

use std::collections::btree_map::Entry;

pub fn check_type<'ast, S: Clone + PartialEq + PartialEq<usize>>(
    decl_ty: &DeclarationType<'ast>,
    ty: &GType<S>,
    constants: &mut GGenericsAssignment<'ast, S>,
) -> bool {
    match (decl_ty, ty) {
        (DeclarationType::Array(t0), GType::Array(t1)) => {
            let s1 = t1.size.clone();

            // both the inner type and the size must match
            check_type(&t0.ty, &t1.ty, constants)
                && match &t0.size {
                    // if the declared size is an identifier, we insert into the map, or check if the concrete size
                    // matches if this identifier is already in the map
                    DeclarationConstant::Generic(id) => match constants.0.entry(id.clone()) {
                        Entry::Occupied(e) => *e.get() == s1,
                        Entry::Vacant(e) => {
                            e.insert(s1);
                            true
                        }
                    },
                    DeclarationConstant::Concrete(s0) => s1 == *s0 as usize,
                    // in the case of a constant, we do not know the value yet, so we optimistically assume it's correct
                    // if it does not match, it will be caught during inlining
                    DeclarationConstant::Constant(..) => true,
                }
        }
        (DeclarationType::FieldElement, GType::FieldElement)
        | (DeclarationType::Boolean, GType::Boolean) => true,
        (DeclarationType::Uint(b0), GType::Uint(b1)) => b0 == b1,
        (DeclarationType::Struct(s0), GType::Struct(s1)) => {
            s0.canonical_location == s1.canonical_location
        }
        _ => false,
    }
}

impl<'ast, T> From<CanonicalConstantIdentifier<'ast>> for UExpression<'ast, T> {
    fn from(_: CanonicalConstantIdentifier<'ast>) -> Self {
        unreachable!("constants should have been removed in constant inlining")
    }
}

impl<'ast> From<CanonicalConstantIdentifier<'ast>> for DeclarationConstant<'ast> {
    fn from(c: CanonicalConstantIdentifier<'ast>) -> Self {
        DeclarationConstant::Constant(c)
    }
}

pub fn specialize_declaration_type<
    'ast,
    S: Clone + PartialEq + From<u32> + fmt::Debug + From<CanonicalConstantIdentifier<'ast>>,
>(
    decl_ty: DeclarationType<'ast>,
    generics: &GGenericsAssignment<'ast, S>,
) -> Result<GType<S>, GenericIdentifier<'ast>> {
    Ok(match decl_ty {
        DeclarationType::Int => unreachable!(),
        DeclarationType::Array(t0) => {
            // let s1 = t1.size.clone();

            let ty = box specialize_declaration_type(*t0.ty, &generics)?;
            let size = match t0.size {
                DeclarationConstant::Generic(s) => generics.0.get(&s).cloned().ok_or(s),
                DeclarationConstant::Concrete(s) => Ok(s.into()),
                DeclarationConstant::Constant(c) => Ok(c.into()),
            }?;

            GType::Array(GArrayType { size, ty })
        }
        DeclarationType::FieldElement => GType::FieldElement,
        DeclarationType::Boolean => GType::Boolean,
        DeclarationType::Uint(b0) => GType::Uint(b0),
        DeclarationType::Struct(s0) => GType::Struct(GStructType {
            members: s0
                .members
                .into_iter()
                .map(|m| {
                    let id = m.id;
                    specialize_declaration_type(*m.ty, generics)
                        .map(|ty| GStructMember { ty: box ty, id })
                })
                .collect::<Result<_, _>>()?,
            generics: s0
                .generics
                .into_iter()
                .map(|g| match g {
                    Some(constant) => match constant {
                        DeclarationConstant::Generic(s) => {
                            generics.0.get(&s).cloned().ok_or(s).map(Some)
                        }
                        DeclarationConstant::Concrete(s) => Ok(Some(s.into())),
                        DeclarationConstant::Constant(..) => {
                            unreachable!(
                                "identifiers should have been removed in constant inlining"
                            )
                        }
                    },
                    _ => Ok(None),
                })
                .collect::<Result<_, _>>()?,
            canonical_location: s0.canonical_location,
            location: s0.location,
        }),
    })
}

pub use self::signature::{
    try_from_g_signature, ConcreteSignature, DeclarationSignature, GSignature, Signature,
};

pub mod signature {
    use super::*;
    use std::fmt;

    #[derive(Clone, Serialize, Deserialize, Eq, Debug)]
    pub struct GSignature<S> {
        pub generics: Vec<Option<S>>,
        pub inputs: Vec<GType<S>>,
        pub outputs: Vec<GType<S>>,
    }

    impl<S: PartialEq> PartialEq for GSignature<S> {
        fn eq(&self, other: &Self) -> bool {
            self.inputs == other.inputs && self.outputs == other.outputs
        }
    }

    impl<S: PartialOrd> PartialOrd for GSignature<S> {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            self.inputs
                .partial_cmp(&other.inputs)
                .map(|c| self.outputs.partial_cmp(&other.outputs).map(|d| c.then(d)))
                .unwrap()
        }
    }

    impl<S: Ord> Ord for GSignature<S> {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            self.partial_cmp(&other).unwrap()
        }
    }

    impl<S: Hash> Hash for GSignature<S> {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            self.inputs.hash(state);
            self.outputs.hash(state);
        }
    }

    impl<S> Default for GSignature<S> {
        fn default() -> Self {
            GSignature {
                generics: vec![],
                inputs: vec![],
                outputs: vec![],
            }
        }
    }

    pub type DeclarationSignature<'ast> = GSignature<DeclarationConstant<'ast>>;
    pub type ConcreteSignature = GSignature<usize>;
    pub type Signature<'ast, T> = GSignature<UExpression<'ast, T>>;

    impl<'ast> PartialEq<DeclarationSignature<'ast>> for ConcreteSignature {
        fn eq(&self, other: &DeclarationSignature<'ast>) -> bool {
            // we keep track of the value of constants in a map, as a given constant can only have one value
            let mut constants = ConcreteGenericsAssignment::default();

            other
                .inputs
                .iter()
                .chain(other.outputs.iter())
                .zip(self.inputs.iter().chain(self.outputs.iter()))
                .all(|(decl_ty, ty)| check_type::<usize>(decl_ty, ty, &mut constants))
        }
    }

    impl<'ast> DeclarationSignature<'ast> {
        pub fn specialize(
            &self,
            values: Vec<Option<u32>>,
            signature: &ConcreteSignature,
        ) -> Result<ConcreteGenericsAssignment<'ast>, SpecializationError> {
            // we keep track of the value of constants in a map, as a given constant can only have one value
            let mut constants = ConcreteGenericsAssignment::default();

            assert_eq!(self.inputs.len(), signature.inputs.len());
            assert_eq!(self.outputs.len(), signature.outputs.len());
            assert_eq!(self.generics.len(), values.len());

            let decl_generics = self.generics.iter().map(|g| match g.clone().unwrap() {
                DeclarationConstant::Generic(g) => g,
                _ => unreachable!(),
            });

            constants.0.extend(
                decl_generics
                    .zip(values.into_iter())
                    .filter_map(|(g, v)| v.map(|v| (g, v as usize))),
            );

            let condition = self
                .inputs
                .iter()
                .chain(self.outputs.iter())
                .zip(signature.inputs.iter().chain(signature.outputs.iter()))
                .all(|(decl_ty, ty)| check_type(decl_ty, ty, &mut constants));

            if constants.0.len() != self.generics.len() {
                return Err(SpecializationError);
            }

            match condition {
                true => Ok(constants),
                false => Err(SpecializationError),
            }
        }

        pub fn get_output_types<T: Clone + PartialEq + fmt::Debug>(
            &self,
            generics: Vec<Option<UExpression<'ast, T>>>,
            inputs: Vec<Type<'ast, T>>,
        ) -> Result<Vec<Type<'ast, T>>, GenericIdentifier<'ast>> {
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

            // get the outputs from the map
            self.outputs
                .clone()
                .into_iter()
                .map(|t| specialize_declaration_type(t, &constants))
                .collect::<Result<_, _>>()
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
            outputs: t
                .outputs
                .into_iter()
                .map(try_from_g_type)
                .collect::<Result<_, _>>()?,
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

    impl<'ast> From<ConcreteSignature> for DeclarationSignature<'ast> {
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
            write!(f, ")")?;
            match self.outputs.len() {
                0 => write!(f, ""),
                1 => write!(f, " -> {}", self.outputs[0]),
                _ => {
                    write!(f, " -> (")?;
                    for (i, t) in self.outputs.iter().enumerate() {
                        write!(f, "{}", t)?;
                        if i < self.outputs.len() - 1 {
                            write!(f, ", ")?;
                        }
                    }
                    write!(f, ")")
                }
            }
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

        pub fn outputs(mut self, outputs: Vec<GType<S>>) -> Self {
            self.outputs = outputs;
            self
        }
    }

    impl ConcreteSignature {
        /// Returns a slug for a signature, with the following encoding:
        /// i{inputs}o{outputs} where {inputs} and {outputs} each encode a list of types.
        /// A list of types is encoded by compressing sequences of the same type like so:
        ///
        /// [field, field, field] -> 3f
        /// [field] -> f
        /// [field, bool, field] -> fbf
        /// [field, field, bool, field] -> 2fbf
        ///
        pub fn to_slug(&self) -> String {
            let to_slug = |types: &[ConcreteType]| {
                let mut res = vec![];
                for t in types {
                    let len = res.len();
                    if len == 0 {
                        res.push((1, t))
                    } else if res[len - 1].1 == t {
                        res[len - 1].0 += 1;
                    } else {
                        res.push((1, t))
                    }
                }
                res.into_iter()
                    .map(|(n, t): (usize, &ConcreteType)| {
                        let mut r = String::new();

                        if n > 1 {
                            r.push_str(&format!("{}", n));
                        }
                        r.push_str(&t.to_slug());
                        r
                    })
                    .fold(String::new(), |mut acc, e| {
                        acc.push_str(&e);
                        acc
                    })
            };

            format!("i{}o{}", to_slug(&self.inputs), to_slug(&self.outputs))
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn signature() {
            let s = ConcreteSignature::new()
                .inputs(vec![ConcreteType::FieldElement, ConcreteType::Boolean])
                .outputs(vec![ConcreteType::Boolean]);

            assert_eq!(s.to_string(), String::from("(field, bool) -> bool"));
        }

        #[test]
        fn signature_equivalence() {
            // check equivalence of:
            // <P>(field[P])
            // <Q>(field[Q])

            let generic1 = DeclarationSignature::new()
                .generics(vec![Some(
                    GenericIdentifier {
                        name: "P",
                        index: 0,
                    }
                    .into(),
                )])
                .inputs(vec![DeclarationType::array(DeclarationArrayType::new(
                    DeclarationType::FieldElement,
                    GenericIdentifier {
                        name: "P",
                        index: 0,
                    },
                ))]);
            let generic2 = DeclarationSignature::new()
                .generics(vec![Some(
                    GenericIdentifier {
                        name: "Q",
                        index: 0,
                    }
                    .into(),
                )])
                .inputs(vec![DeclarationType::array(DeclarationArrayType::new(
                    DeclarationType::FieldElement,
                    GenericIdentifier {
                        name: "Q",
                        index: 0,
                    },
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

        #[test]
        fn slug_0() {
            let s = ConcreteSignature::new().inputs(vec![]).outputs(vec![]);

            assert_eq!(s.to_slug(), String::from("io"));
        }

        #[test]
        fn slug_1() {
            let s = ConcreteSignature::new()
                .inputs(vec![ConcreteType::FieldElement, ConcreteType::Boolean])
                .outputs(vec![
                    ConcreteType::FieldElement,
                    ConcreteType::FieldElement,
                    ConcreteType::Boolean,
                    ConcreteType::FieldElement,
                ]);

            assert_eq!(s.to_slug(), String::from("ifbo2fbf"));
        }

        #[test]
        fn slug_2() {
            let s = ConcreteSignature::new()
                .inputs(vec![
                    ConcreteType::FieldElement,
                    ConcreteType::FieldElement,
                    ConcreteType::FieldElement,
                ])
                .outputs(vec![
                    ConcreteType::FieldElement,
                    ConcreteType::Boolean,
                    ConcreteType::FieldElement,
                ]);

            assert_eq!(s.to_slug(), String::from("i3fofbf"));
        }

        #[test]
        fn array_slug() {
            let s = ConcreteSignature::new()
                .inputs(vec![
                    ConcreteType::array((ConcreteType::FieldElement, 42usize)),
                    ConcreteType::array((ConcreteType::FieldElement, 21usize)),
                ])
                .outputs(vec![]);

            assert_eq!(s.to_slug(), String::from("if[42]f[21]o"));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn array() {
        let t = ConcreteType::Array(ConcreteArrayType::new(ConcreteType::FieldElement, 42usize));
        assert_eq!(t.get_primitive_count(), 42);
    }

    #[test]
    fn array_display() {
        // field[1][2]
        let t = ConcreteType::Array(ConcreteArrayType::new(
            ConcreteType::Array(ConcreteArrayType::new(ConcreteType::FieldElement, 2usize)),
            1usize,
        ));
        assert_eq!(format!("{}", t), "field[1][2]");
    }
}
