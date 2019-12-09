use std::fmt;

pub type Identifier<'ast> = &'ast str;

pub type MemberId = String;

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub struct StructMember {
    #[serde(rename = "name")]
    pub id: MemberId,
    #[serde(flatten)]
    pub ty: Box<Type>,
}

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub struct ArrayType {
    pub size: usize,
    #[serde(flatten)]
    pub ty: Box<Type>,
}

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
#[serde(tag = "type", content = "components")]
pub enum Type {
    #[serde(rename = "field")]
    FieldElement,
    #[serde(rename = "bool")]
    Boolean,
    #[serde(rename = "array")]
    Array(ArrayType),
    #[serde(rename = "struct")]
    Struct(Vec<StructMember>),
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
            Type::Array(ref array_type) => write!(f, "{}[{}]", array_type.ty, array_type.size),
            Type::Struct(ref members) => write!(
                f,
                "{{{}}}",
                members
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
            Type::Array(ref array_type) => write!(f, "{}[{}]", array_type.ty, array_type.size),
            Type::Struct(ref members) => write!(
                f,
                "{{{}}}",
                members
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

    fn to_slug(&self) -> String {
        match self {
            Type::FieldElement => String::from("f"),
            Type::Boolean => String::from("b"),
            Type::Array(array_type) => format!("{}[{}]", array_type.ty.to_slug(), array_type.size),
            Type::Struct(members) => format!(
                "{{{}}}",
                members
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
            Type::FieldElement => 1,
            Type::Boolean => 1,
            Type::Array(array_type) => array_type.size * array_type.ty.get_primitive_count(),
            Type::Struct(members) => members
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
            write!(f, ") -> (")?;
            for (i, t) in self.outputs.iter().enumerate() {
                write!(f, "{}", t)?;
                if i < self.outputs.len() - 1 {
                    write!(f, ", ")?;
                }
            }
            write!(f, ")")
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

            assert_eq!(s.to_string(), String::from("(field, bool) -> (bool)"));
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
