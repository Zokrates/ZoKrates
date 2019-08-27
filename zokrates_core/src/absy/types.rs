use absy::UnresolvedTypeNode;
use std::fmt;

pub type Identifier<'ast> = &'ast str;

pub type MemberId = String;

pub type UserTypeId = String;

#[derive(Clone, PartialEq, Serialize, Deserialize, Debug)]
pub enum UnresolvedType {
    FieldElement,
    Boolean,
    Array(Box<UnresolvedTypeNode>, usize),
    User(UserTypeId),
}

impl fmt::Display for UnresolvedType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            UnresolvedType::FieldElement => write!(f, "field"),
            UnresolvedType::Boolean => write!(f, "bool"),
            UnresolvedType::Array(ref ty, ref size) => write!(f, "{}[{}]", ty, size),
            UnresolvedType::User(i) => write!(f, "{}", i),
        }
    }
}

impl UnresolvedType {
    pub fn array(ty: UnresolvedTypeNode, size: usize) -> Self {
        UnresolvedType::Array(box ty, size)
    }
}

pub type FunctionIdentifier<'ast> = &'ast str;

pub use self::signature::UnresolvedSignature;

mod signature {
    use std::fmt;

    use absy::UnresolvedTypeNode;

    #[derive(Clone, PartialEq, Serialize, Deserialize)]
    pub struct UnresolvedSignature {
        pub inputs: Vec<UnresolvedTypeNode>,
        pub outputs: Vec<UnresolvedTypeNode>,
    }

    impl fmt::Debug for UnresolvedSignature {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(
                f,
                "Signature(inputs: {:?}, outputs: {:?})",
                self.inputs, self.outputs
            )
        }
    }

    impl fmt::Display for UnresolvedSignature {
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

    impl UnresolvedSignature {
        pub fn new() -> UnresolvedSignature {
            UnresolvedSignature {
                inputs: vec![],
                outputs: vec![],
            }
        }

        pub fn inputs(mut self, inputs: Vec<UnresolvedTypeNode>) -> Self {
            self.inputs = inputs;
            self
        }

        pub fn outputs(mut self, outputs: Vec<UnresolvedTypeNode>) -> Self {
            self.outputs = outputs;
            self
        }
    }
}
