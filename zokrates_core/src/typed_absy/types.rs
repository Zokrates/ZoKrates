use std::fmt;
use std::path::PathBuf;
use typed_absy::{TryFrom, TryInto};
use typed_absy::{UExpression, UExpressionInner};

pub type Identifier<'ast> = &'ast str;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Constant<'ast> {
    Generic(Identifier<'ast>),
    Concrete(u32),
}

impl<'ast> From<u32> for Constant<'ast> {
    fn from(e: u32) -> Self {
        Constant::Concrete(e)
    }
}

impl<'ast> From<usize> for Constant<'ast> {
    fn from(e: usize) -> Self {
        Constant::Concrete(e as u32)
    }
}

impl<'ast> From<Identifier<'ast>> for Constant<'ast> {
    fn from(e: Identifier<'ast>) -> Self {
        Constant::Generic(e)
    }
}

impl<'ast> fmt::Display for Constant<'ast> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        unimplemented!()
    }
}

impl<'ast, T> From<usize> for UExpression<'ast, T> {
    fn from(i: usize) -> Self {
        UExpressionInner::Value(i as u128).annotate(UBitwidth::B32)
    }
}

impl<'ast, T> From<Constant<'ast>> for UExpression<'ast, T> {
    fn from(c: Constant<'ast>) -> Self {
        match c {
            Constant::Generic(i) => UExpressionInner::Identifier(i.into()).annotate(UBitwidth::B32),
            Constant::Concrete(v) => UExpressionInner::Value(v as u128).annotate(UBitwidth::B32),
        }
    }
}

impl<'ast, T> TryInto<usize> for UExpression<'ast, T> {
    type Error = ();

    fn try_into(self) -> Result<usize, Self::Error> {
        assert_eq!(self.bitwidth, UBitwidth::B32);

        match self.into_inner() {
            UExpressionInner::Value(v) => Ok(v as usize),
            _ => Err(()),
        }
    }
}

impl<'ast> TryInto<usize> for Constant<'ast> {
    type Error = ();

    fn try_into(self) -> Result<usize, Self::Error> {
        match self {
            Constant::Concrete(v) => Ok(v as usize),
            _ => Err(()),
        }
    }
}

pub type MemberId = String;

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub struct GStructMember<S> {
    #[serde(rename = "name")]
    pub id: MemberId,
    #[serde(flatten)]
    pub ty: Box<GType<S>>,
}

pub type DeclarationStructMember<'ast> = GStructMember<Constant<'ast>>;
pub type ConcreteStructMember = GStructMember<usize>;
pub type StructMember<'ast, T> = GStructMember<UExpression<'ast, T>>;

fn try_from_g_struct_member<T: TryInto<U>, U>(t: GStructMember<T>) -> Result<GStructMember<U>, ()> {
    Ok(GStructMember {
        id: t.id,
        ty: box try_from_g_type(*t.ty)?,
    })
}

impl<'ast, T> TryFrom<StructMember<'ast, T>> for ConcreteStructMember {
    type Error = ();

    fn try_from(t: StructMember<'ast, T>) -> Result<Self, Self::Error> {
        try_from_g_struct_member(t)
    }
}

impl<'ast> TryFrom<DeclarationStructMember<'ast>> for ConcreteStructMember {
    type Error = ();

    fn try_from(t: DeclarationStructMember<'ast>) -> Result<Self, Self::Error> {
        try_from_g_struct_member(t)
    }
}

impl<'ast, T> From<ConcreteStructMember> for StructMember<'ast, T> {
    fn from(t: ConcreteStructMember) -> Self {
        try_from_g_struct_member(t).unwrap()
    }
}

impl<'ast> From<ConcreteStructMember> for DeclarationStructMember<'ast> {
    fn from(t: ConcreteStructMember) -> Self {
        try_from_g_struct_member(t).unwrap()
    }
}

impl<'ast, T> From<DeclarationStructMember<'ast>> for StructMember<'ast, T> {
    fn from(t: DeclarationStructMember<'ast>) -> Self {
        try_from_g_struct_member(t).unwrap()
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub struct GArrayType<S> {
    pub size: S,
    #[serde(flatten)]
    pub ty: Box<GType<S>>,
}

pub type DeclarationArrayType<'ast> = GArrayType<Constant<'ast>>;
pub type ConcreteArrayType = GArrayType<usize>;
pub type ArrayType<'ast, T> = GArrayType<UExpression<'ast, T>>;

fn try_from_g_array_type<T: TryInto<U>, U>(t: GArrayType<T>) -> Result<GArrayType<U>, ()> {
    Ok(GArrayType {
        size: t.size.try_into().map_err(|_| ())?,
        ty: box try_from_g_type(*t.ty)?,
    })
}

impl<'ast, T> TryFrom<ArrayType<'ast, T>> for ConcreteArrayType {
    type Error = ();

    fn try_from(t: ArrayType<'ast, T>) -> Result<Self, Self::Error> {
        try_from_g_array_type(t)
    }
}

impl<'ast> TryFrom<DeclarationArrayType<'ast>> for ConcreteArrayType {
    type Error = ();

    fn try_from(t: DeclarationArrayType<'ast>) -> Result<Self, Self::Error> {
        try_from_g_array_type(t)
    }
}

impl<'ast, T> From<ConcreteArrayType> for ArrayType<'ast, T> {
    fn from(t: ConcreteArrayType) -> Self {
        try_from_g_array_type(t).unwrap()
    }
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

#[derive(Clone, Hash, Serialize, Deserialize, PartialOrd, Ord, PartialEq, Eq)]
pub struct GStructType<S> {
    #[serde(skip)]
    pub module: PathBuf,
    pub name: String,
    pub members: Vec<GStructMember<S>>,
}

pub type DeclarationStructType<'ast> = GStructType<Constant<'ast>>;
pub type ConcreteStructType = GStructType<usize>;
pub type StructType<'ast, T> = GStructType<UExpression<'ast, T>>;

fn try_from_g_struct_type<T: TryInto<U>, U>(t: GStructType<T>) -> Result<GStructType<U>, ()> {
    Ok(GStructType {
        module: t.module,
        name: t.name,
        members: t
            .members
            .into_iter()
            .map(|m| try_from_g_struct_member(m))
            .collect::<Result<_, _>>()?,
    })
}

impl<'ast, T> TryFrom<StructType<'ast, T>> for ConcreteStructType {
    type Error = ();

    fn try_from(t: StructType<'ast, T>) -> Result<Self, Self::Error> {
        try_from_g_struct_type(t)
    }
}

impl<'ast> TryFrom<DeclarationStructType<'ast>> for ConcreteStructType {
    type Error = ();

    fn try_from(t: DeclarationStructType<'ast>) -> Result<Self, Self::Error> {
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

impl<'ast, T> From<DeclarationStructType<'ast>> for StructType<'ast, T> {
    fn from(t: DeclarationStructType<'ast>) -> Self {
        try_from_g_struct_type(t).unwrap()
    }
}

// impl<S> PartialEq for GStructType<S> {
//     fn eq(&self, other: &Self) -> bool {
//         self.members.eq(&other.members)
//     }
// }

// impl<S> Eq for GStructType<S> {}

impl<S> GStructType<S> {
    pub fn new(module: PathBuf, name: String, members: Vec<GStructMember<S>>) -> Self {
        GStructType {
            module,
            name,
            members,
        }
    }

    pub fn len(&self) -> usize {
        self.members.len()
    }

    pub fn iter(&self) -> std::slice::Iter<GStructMember<S>> {
        self.members.iter()
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

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
#[serde(tag = "type", content = "components")]
pub enum GType<S> {
    #[serde(rename = "field")]
    FieldElement,
    #[serde(rename = "bool")]
    Boolean,
    #[serde(rename = "array")]
    Array(GArrayType<S>),
    #[serde(rename = "struct")]
    Struct(GStructType<S>),
    #[serde(rename = "u")]
    Uint(UBitwidth),
}

pub type DeclarationType<'ast> = GType<Constant<'ast>>;
pub type ConcreteType = GType<usize>;
pub type Type<'ast, T> = GType<UExpression<'ast, T>>;

fn try_from_g_type<T: TryInto<U>, U>(t: GType<T>) -> Result<GType<U>, ()> {
    match t {
        GType::FieldElement => Ok(GType::FieldElement),
        GType::Boolean => Ok(GType::Boolean),
        GType::Uint(bitwidth) => Ok(GType::Uint(bitwidth)),
        GType::Array(array_type) => Ok(GType::Array(try_from_g_array_type(array_type)?)),
        GType::Struct(struct_type) => Ok(GType::Struct(try_from_g_struct_type(struct_type)?)),
    }
}

impl<'ast, T> TryFrom<Type<'ast, T>> for ConcreteType {
    type Error = ();

    fn try_from(t: Type<'ast, T>) -> Result<Self, Self::Error> {
        try_from_g_type(t)
    }
}

impl<'ast> TryFrom<DeclarationType<'ast>> for ConcreteType {
    type Error = ();

    fn try_from(t: DeclarationType<'ast>) -> Result<Self, Self::Error> {
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

impl<'ast, T> From<DeclarationType<'ast>> for Type<'ast, T> {
    fn from(t: DeclarationType<'ast>) -> Self {
        try_from_g_type(t).unwrap()
    }
}

impl<S> GArrayType<S> {
    pub fn new(ty: GType<S>, size: S) -> Self {
        GArrayType {
            ty: Box::new(ty),
            size,
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
            GType::Array(ref array_type) => write!(f, "{}[{}]", array_type.ty, array_type.size),
            GType::Struct(ref struct_type) => write!(
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

impl<S: fmt::Debug> fmt::Debug for GType<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            GType::FieldElement => write!(f, "field"),
            GType::Boolean => write!(f, "bool"),
            GType::Uint(ref bitwidth) => write!(f, "u{:?}", bitwidth),
            GType::Array(ref array_type) => write!(f, "{:?}[{:?}]", array_type.ty, array_type.size),
            GType::Struct(ref struct_type) => write!(
                f,
                "{:?} {{{:?}}}",
                struct_type.name,
                struct_type
                    .members
                    .iter()
                    .map(|member| format!("{:?}: {:?}", member.id, member.ty))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

impl<S> GType<S> {
    pub fn array<U: Into<S>>(ty: GType<S>, size: U) -> Self {
        GType::Array(GArrayType::new(ty, size.into()))
    }

    pub fn struc(struct_ty: GStructType<S>) -> Self {
        GType::Struct(struct_ty)
    }

    pub fn uint<W: Into<UBitwidth>>(b: W) -> Self {
        GType::Uint(b.into())
    }
}

impl<S: fmt::Display + std::cmp::PartialEq> GType<S> {
    fn to_slug(&self) -> String {
        match self {
            GType::FieldElement => String::from("f"),
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
    pub id: FunctionIdentifier<'ast>,
    pub signature: GSignature<S>,
}

pub type DeclarationFunctionKey<'ast> = GFunctionKey<'ast, Constant<'ast>>;
pub type ConcreteFunctionKey<'ast> = GFunctionKey<'ast, usize>;
pub type FunctionKey<'ast, T> = GFunctionKey<'ast, UExpression<'ast, T>>;

impl<'ast, T> TryFrom<FunctionKey<'ast, T>> for ConcreteFunctionKey<'ast> {
    type Error = ();

    fn try_from(t: FunctionKey<'ast, T>) -> Result<Self, Self::Error> {
        unimplemented!()
    }
}

impl<'ast> TryFrom<DeclarationFunctionKey<'ast>> for ConcreteFunctionKey<'ast> {
    type Error = ();

    fn try_from(t: DeclarationFunctionKey<'ast>) -> Result<Self, Self::Error> {
        unimplemented!()
    }
}

impl<'ast, T> From<ConcreteFunctionKey<'ast>> for FunctionKey<'ast, T> {
    fn from(t: ConcreteFunctionKey<'ast>) -> Self {
        unimplemented!()
    }
}

impl<'ast> From<ConcreteFunctionKey<'ast>> for DeclarationFunctionKey<'ast> {
    fn from(t: ConcreteFunctionKey<'ast>) -> Self {
        unimplemented!()
    }
}

impl<'ast, T> From<DeclarationFunctionKey<'ast>> for FunctionKey<'ast, T> {
    fn from(t: DeclarationFunctionKey<'ast>) -> Self {
        unimplemented!()
    }
}

impl<'ast, S> GFunctionKey<'ast, S> {
    pub fn with_id<U: Into<Identifier<'ast>>>(id: U) -> Self {
        GFunctionKey {
            id: id.into(),
            signature: GSignature::new(),
        }
    }

    pub fn signature(mut self, signature: GSignature<S>) -> Self {
        self.signature = signature;
        self
    }

    pub fn id<U: Into<Identifier<'ast>>>(mut self, id: U) -> Self {
        self.id = id.into();
        self
    }
}

impl<'ast, S: fmt::Display + std::cmp::PartialEq> GFunctionKey<'ast, S> {
    pub fn to_slug(&self) -> String {
        format!("{}_{}", self.id, self.signature.to_slug())
    }
}

// impl<'ast, T: Clone> Clone for Type<'ast, T> {
//     fn clone(&self) -> Self {
//         unimplemented!()
//     }
// }

// impl<'ast> Clone for DeclarationType<'ast> {
//     fn clone(&self) -> Self {
//         unimplemented!()
//     }
// }

// impl Clone for ConcreteType {
//     fn clone(&self) -> Self {
//         unimplemented!()
//     }
// }

pub use self::signature::{ConcreteSignature, DeclarationSignature, GSignature, Signature};

pub mod signature {
    use super::*;
    use std::cmp::Ordering;
    use std::fmt;
    use std::hash::Hasher;

    #[derive(Clone, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub struct GSignature<S> {
        pub inputs: Vec<GType<S>>,
        pub outputs: Vec<GType<S>>,
    }

    pub type DeclarationSignature<'ast> = GSignature<Constant<'ast>>;
    pub type ConcreteSignature = GSignature<usize>;
    pub type Signature<'ast, T> = GSignature<UExpression<'ast, T>>;

    impl<'ast, T> TryFrom<Signature<'ast, T>> for ConcreteSignature {
        type Error = ();

        fn try_from(t: Signature<'ast, T>) -> Result<Self, Self::Error> {
            unimplemented!()
        }
    }

    impl<'ast> TryFrom<DeclarationSignature<'ast>> for ConcreteSignature {
        type Error = ();

        fn try_from(t: DeclarationSignature<'ast>) -> Result<Self, Self::Error> {
            unimplemented!()
        }
    }

    impl<'ast, T> From<ConcreteSignature> for Signature<'ast, T> {
        fn from(t: ConcreteSignature) -> Self {
            unimplemented!()
        }
    }

    impl<'ast> From<ConcreteSignature> for DeclarationSignature<'ast> {
        fn from(t: ConcreteSignature) -> Self {
            unimplemented!()
        }
    }

    impl<'ast, T> From<DeclarationSignature<'ast>> for Signature<'ast, T> {
        fn from(t: DeclarationSignature) -> Self {
            unimplemented!()
        }
    }

    impl<S: fmt::Debug> fmt::Debug for GSignature<S> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(
                f,
                "Signature(inputs: {:?}, outputs: {:?})",
                self.inputs, self.outputs
            )
        }
    }

    impl<S: fmt::Display> fmt::Display for GSignature<S> {
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

    impl<S> GSignature<S> {
        pub fn new() -> GSignature<S> {
            Self {
                inputs: vec![],
                outputs: vec![],
            }
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

    impl<S: fmt::Display + std::cmp::PartialEq> GSignature<S> {
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
            let to_slug = |types: &[GType<S>]| {
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
                    .map(|(n, t): (usize, &GType<S>)| {
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
                    ConcreteType::array(ConcreteType::FieldElement, 42usize),
                    ConcreteType::array(ConcreteType::FieldElement, 21usize),
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
}
