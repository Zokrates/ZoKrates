use absy::UnresolvedTypeNode;
use std::fmt;

pub type Identifier<'ast> = &'ast str;

pub type MemberId = String;

pub type UserTypeId = String;

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Type {
    FieldElement,
    Boolean,
    Array(Box<Type>, usize),
    Struct(Vec<(MemberId, Type)>),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::FieldElement => write!(f, "field"),
            Type::Boolean => write!(f, "bool"),
            Type::Array(ref ty, ref size) => write!(f, "{}[{}]", ty, size),
            Type::Struct(ref members) => write!(
                f,
                "{{{}}}",
                members
                    .iter()
                    .map(|(id, t)| format!("{}: {}", id, t))
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
            Type::Array(ref ty, ref size) => write!(f, "{}[{}]", ty, size),
            Type::Struct(ref members) => write!(
                f,
                "{{{}}}",
                members
                    .iter()
                    .map(|(id, t)| format!("{}: {}", id, t))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

impl Type {
    pub fn array(ty: Type, size: usize) -> Self {
        Type::Array(box ty, size)
    }

    fn to_slug(&self) -> String {
        match self {
            Type::FieldElement => String::from("f"),
            Type::Boolean => String::from("b"),
            Type::Array(box ty, size) => format!("{}[{}]", ty.to_slug(), size),
            Type::Struct(members) => unimplemented!(),
        }
    }

    // the number of field elements the type maps to
    pub fn get_primitive_count(&self) -> usize {
        match self {
            Type::FieldElement => 1,
            Type::Boolean => 1,
            Type::Array(ty, size) => size * ty.get_primitive_count(),
            Type::Struct(members) => members.iter().map(|(_, t)| t.get_primitive_count()).sum(),
        }
    }
}

#[derive(Clone, PartialEq, Hash, Eq)]
pub struct Variable<'ast> {
    pub id: Identifier<'ast>,
    pub _type: Type,
}

impl<'ast> fmt::Display for Variable<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self._type, self.id,)
    }
}

impl<'ast> fmt::Debug for Variable<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Variable(type: {:?}, id: {:?})", self._type, self.id,)
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

    #[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
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
            r#try!(write!(f, "("));
            for (i, t) in self.inputs.iter().enumerate() {
                r#try!(write!(f, "{}", t));
                if i < self.inputs.len() - 1 {
                    r#try!(write!(f, ", "));
                }
            }
            r#try!(write!(f, ") -> ("));
            for (i, t) in self.outputs.iter().enumerate() {
                r#try!(write!(f, "{}", t));
                if i < self.outputs.len() - 1 {
                    r#try!(write!(f, ", "));
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
        let t = Type::Array(box Type::FieldElement, 42);
        assert_eq!(t.get_primitive_count(), 42);
    }
}
