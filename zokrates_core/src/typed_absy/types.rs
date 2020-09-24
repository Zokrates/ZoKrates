use std::fmt;
use std::path::PathBuf;

pub type Identifier<'ast> = &'ast str;

pub type MemberId = String;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub struct StructMember {
    #[serde(rename = "name")]
    pub id: MemberId,
    #[serde(flatten)]
    pub ty: Box<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub struct ArrayType {
    pub size: usize,
    #[serde(flatten)]
    pub ty: Box<Type>,
}

#[derive(Debug, Clone, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub struct StructType {
    #[serde(skip)]
    pub module: PathBuf,
    pub name: String,
    pub members: Vec<StructMember>,
}

impl PartialEq for StructType {
    fn eq(&self, other: &Self) -> bool {
        self.members.eq(&other.members)
    }
}

impl Eq for StructType {}

impl StructType {
    pub fn new(module: PathBuf, name: String, members: Vec<StructMember>) -> Self {
        StructType {
            module,
            name,
            members,
        }
    }

    pub fn len(&self) -> usize {
        self.members.len()
    }

    pub fn iter(&self) -> std::slice::Iter<StructMember> {
        self.members.iter()
    }
}

impl IntoIterator for StructType {
    type Item = StructMember;
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
}

impl UBitwidth {
    pub fn to_usize(&self) -> usize {
        *self as u32 as usize
    }
}

impl From<usize> for UBitwidth {
    fn from(b: usize) -> Self {
        match b {
            8 => UBitwidth::B8,
            16 => UBitwidth::B16,
            32 => UBitwidth::B32,
            _ => unreachable!(),
        }
    }
}

impl fmt::Display for UBitwidth {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_usize())
    }
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Type {
    FieldElement,
    Boolean,
    Array(ArrayType),
    Struct(StructType),
    Uint(UBitwidth),
    #[serde(skip_serializing)]
    Int,
}

impl Serialize for Type {
    fn serialize<S>(&self, s: S) -> Result<<S as Serializer>::Ok, <S as Serializer>::Error>
    where
        S: Serializer,
    {
        match self {
            Type::FieldElement => s.serialize_newtype_variant("Type", 0, "type", "field"),
            Type::Boolean => s.serialize_newtype_variant("Type", 1, "type", "bool"),
            Type::Array(array_type) => {
                let mut map = s.serialize_map(Some(2))?;
                map.serialize_entry("type", "array")?;
                map.serialize_entry("components", array_type)?;
                map.end()
            }
            Type::Struct(struct_type) => {
                let mut map = s.serialize_map(Some(2))?;
                map.serialize_entry("type", "struct")?;
                map.serialize_entry("components", struct_type)?;
                map.end()
            }
            Type::Uint(width) => s.serialize_newtype_variant(
                "Type",
                4,
                "type",
                format!("u{}", width.to_usize()).as_str(),
            ),
        }
    }
}

impl<'de> Deserialize<'de> for Type {
    fn deserialize<D>(d: D) -> Result<Self, <D as Deserializer<'de>>::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Debug, Deserialize)]
        #[serde(untagged)]
        enum Components {
            Array(ArrayType),
            Struct(StructType),
        }

        #[derive(Debug, Deserialize)]
        struct Mapping {
            #[serde(rename = "type")]
            ty: String,
            components: Option<Components>,
        }

        let strict_type = |m: Mapping, ty: Type| -> Result<Self, <D as Deserializer<'de>>::Error> {
            match m.components {
                Some(_) => Err(D::Error::custom(format!(
                    "unexpected `components` field for type `{}`",
                    ty
                ))),
                None => Ok(ty),
            }
        };

        let mapping = Mapping::deserialize(d)?;
        match mapping.ty.as_str() {
            "field" => strict_type(mapping, Type::FieldElement),
            "bool" => strict_type(mapping, Type::Boolean),
            "array" => {
                let components = mapping.components.ok_or(D::Error::custom(format_args!(
                    "missing `components` field for type `{}'",
                    mapping.ty
                )))?;
                match components {
                    Components::Array(array_type) => Ok(Type::Array(array_type)),
                    _ => Err(D::Error::custom(format!(
                        "invalid `components` variant for type `{}`",
                        mapping.ty
                    ))),
                }
            }
            "struct" => {
                let components = mapping.components.ok_or(D::Error::custom(format_args!(
                    "missing `components` field for type `{}'",
                    mapping.ty
                )))?;
                match components {
                    Components::Struct(struct_type) => Ok(Type::Struct(struct_type)),
                    _ => Err(D::Error::custom(format!(
                        "invalid `components` variant for type `{}`",
                        mapping.ty
                    ))),
                }
            }
            "u8" => strict_type(mapping, Type::Uint(UBitwidth::B8)),
            "u16" => strict_type(mapping, Type::Uint(UBitwidth::B16)),
            "u32" => strict_type(mapping, Type::Uint(UBitwidth::B32)),
            _ => Err(D::Error::custom(format!("invalid type `{}`", mapping.ty))),
        }
    }
}

impl ArrayType {
    pub fn new(ty: Type, size: usize) -> Self {
        ArrayType {
            ty: Box::new(ty),
            size,
        }
    }
}

impl StructMember {
    pub fn new(id: String, ty: Type) -> Self {
        StructMember {
            id,
            ty: Box::new(ty),
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::FieldElement => write!(f, "field"),
            Type::Boolean => write!(f, "bool"),
            Type::Int => write!(f, "{{integer}}"),
            Type::Uint(ref bitwidth) => write!(f, "u{}", bitwidth),
            Type::Array(ref array_type) => write!(f, "{}[{}]", array_type.ty, array_type.size),
            Type::Struct(ref struct_type) => write!(
                f,
                "{} {{{}}}",
                struct_type.name,
                struct_type
                    .members
                    .iter()
                    .map(|member| format!("{}: {}", member.id, member.ty))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

impl fmt::Debug for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::FieldElement => write!(f, "field"),
            Type::Boolean => write!(f, "bool"),
            Type::Int => write!(f, "{{integer}}"),
            Type::Uint(ref bitwidth) => write!(f, "u{}", bitwidth),
            Type::Array(ref array_type) => write!(f, "{}[{}]", array_type.ty, array_type.size),
            Type::Struct(ref struct_type) => write!(
                f,
                "{} {{{}}}",
                struct_type.name,
                struct_type
                    .members
                    .iter()
                    .map(|member| format!("{}: {}", member.id, member.ty))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

impl Type {
    pub fn array(ty: Type, size: usize) -> Self {
        Type::Array(ArrayType::new(ty, size))
    }

    pub fn struc(struct_ty: StructType) -> Self {
        Type::Struct(struct_ty)
    }

    pub fn uint<W: Into<UBitwidth>>(b: W) -> Self {
        Type::Uint(b.into())
    }

    pub fn can_be_specialized_to(&self, other: &Type) -> bool {
        use self::Type::*;

        if self == other {
            true
        } else {
            match (self, other) {
                (Int, FieldElement) | (Int, Uint(..)) => true,
                (Array(l), Array(r)) => l.size == r.size && l.ty.can_be_specialized_to(&r.ty),
                _ => false,
            }
        }
    }

    fn to_slug(&self) -> String {
        match self {
            Type::FieldElement => String::from("f"),
            Type::Boolean => String::from("b"),
            Type::Int => unreachable!(),
            Type::Uint(bitwidth) => format!("u{}", bitwidth),
            Type::Array(array_type) => format!("{}[{}]", array_type.ty.to_slug(), array_type.size),
            Type::Struct(struct_type) => format!(
                "{{{}}}",
                struct_type
                    .iter()
                    .map(|member| format!("{}:{}", member.id, member.ty))
                    .collect::<Vec<_>>()
                    .join(",")
            ),
        }
    }

    // the number of field elements the type maps to
    pub fn get_primitive_count(&self) -> usize {
        match self {
            Type::Int => unreachable!(),
            Type::FieldElement => 1,
            Type::Boolean => 1,
            Type::Uint(_) => 1,
            Type::Array(array_type) => array_type.size * array_type.ty.get_primitive_count(),
            Type::Struct(struct_type) => struct_type
                .iter()
                .map(|member| member.ty.get_primitive_count())
                .sum(),
        }
    }
}

pub type FunctionIdentifier<'ast> = &'ast str;

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct FunctionKey<'ast> {
    pub id: FunctionIdentifier<'ast>,
    pub signature: Signature,
}

impl<'ast> FunctionKey<'ast> {
    pub fn with_id<S: Into<Identifier<'ast>>>(id: S) -> Self {
        FunctionKey {
            id: id.into(),
            signature: Signature::new(),
        }
    }

    pub fn signature(mut self, signature: Signature) -> Self {
        self.signature = signature;
        self
    }

    pub fn id<S: Into<Identifier<'ast>>>(mut self, id: S) -> Self {
        self.id = id.into();
        self
    }

    pub fn to_slug(&self) -> String {
        format!("{}_{}", self.id, self.signature.to_slug())
    }
}

pub use self::signature::Signature;
use serde::de::Error;
use serde::ser::SerializeMap;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

pub mod signature {
    use super::*;
    use std::fmt;

    #[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Ord, PartialOrd)]
    pub struct Signature {
        pub inputs: Vec<Type>,
        pub outputs: Vec<Type>,
    }

    impl fmt::Debug for Signature {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(
                f,
                "Signature(inputs: {:?}, outputs: {:?})",
                self.inputs, self.outputs
            )
        }
    }

    impl fmt::Display for Signature {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
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

    impl Signature {
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
            let to_slug = |types| {
                let mut res = vec![];
                for t in types {
                    let len = res.len();
                    if len == 0 {
                        res.push((1, t))
                    } else {
                        if res[len - 1].1 == t {
                            res[len - 1].0 += 1;
                        } else {
                            res.push((1, t))
                        }
                    }
                }
                res.into_iter()
                    .map(|(n, t): (usize, &Type)| {
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

        pub fn new() -> Signature {
            Signature {
                inputs: vec![],
                outputs: vec![],
            }
        }

        pub fn inputs(mut self, inputs: Vec<Type>) -> Self {
            self.inputs = inputs;
            self
        }

        pub fn outputs(mut self, outputs: Vec<Type>) -> Self {
            self.outputs = outputs;
            self
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn signature() {
            let s = Signature::new()
                .inputs(vec![Type::FieldElement, Type::Boolean])
                .outputs(vec![Type::Boolean]);

            assert_eq!(s.to_string(), String::from("(field, bool) -> bool"));
        }

        #[test]
        fn slug_0() {
            let s = Signature::new().inputs(vec![]).outputs(vec![]);

            assert_eq!(s.to_slug(), String::from("io"));
        }

        #[test]
        fn slug_1() {
            let s = Signature::new()
                .inputs(vec![Type::FieldElement, Type::Boolean])
                .outputs(vec![
                    Type::FieldElement,
                    Type::FieldElement,
                    Type::Boolean,
                    Type::FieldElement,
                ]);

            assert_eq!(s.to_slug(), String::from("ifbo2fbf"));
        }

        #[test]
        fn slug_2() {
            let s = Signature::new()
                .inputs(vec![
                    Type::FieldElement,
                    Type::FieldElement,
                    Type::FieldElement,
                ])
                .outputs(vec![Type::FieldElement, Type::Boolean, Type::FieldElement]);

            assert_eq!(s.to_slug(), String::from("i3fofbf"));
        }

        #[test]
        fn array_slug() {
            let s = Signature::new()
                .inputs(vec![
                    Type::array(Type::FieldElement, 42),
                    Type::array(Type::FieldElement, 21),
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
        let t = Type::Array(ArrayType::new(Type::FieldElement, 42));
        assert_eq!(t.get_primitive_count(), 42);
    }
}
