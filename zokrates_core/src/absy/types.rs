use crate::absy::ExpressionNode;
use crate::absy::UnresolvedTypeNode;
use std::fmt;

pub type Identifier<'ast> = &'ast str;

pub type MemberId = String;

pub type UserTypeId = String;

#[derive(Clone, PartialEq, Debug)]
pub enum UnresolvedType<'ast> {
    FieldElement,
    Boolean,
    Uint(usize),
    Array(Box<UnresolvedTypeNode<'ast>>, ExpressionNode<'ast>),
    User(UserTypeId),
}

impl<'ast> fmt::Display for UnresolvedType<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            UnresolvedType::FieldElement => write!(f, "field"),
            UnresolvedType::Boolean => write!(f, "bool"),
            UnresolvedType::Uint(bitwidth) => write!(f, "u{}", bitwidth),
            UnresolvedType::Array(ref ty, ref size) => write!(f, "{}[{}]", ty, size),
            UnresolvedType::User(i) => write!(f, "{}", i),
        }
    }
}

impl<'ast> UnresolvedType<'ast> {
    pub fn array(ty: UnresolvedTypeNode<'ast>, size: ExpressionNode<'ast>) -> Self {
        UnresolvedType::Array(box ty, size)
    }
}

pub type FunctionIdentifier<'ast> = &'ast str;

pub use self::signature::UnresolvedSignature;

mod signature {
    use crate::absy::ConstantGenericNode;
    use std::fmt;

    use crate::absy::UnresolvedTypeNode;

    #[derive(Clone, PartialEq, Default)]
    pub struct UnresolvedSignature<'ast> {
        pub generics: Vec<ConstantGenericNode<'ast>>,
        pub inputs: Vec<UnresolvedTypeNode<'ast>>,
        pub outputs: Vec<UnresolvedTypeNode<'ast>>,
    }

    impl<'ast> fmt::Debug for UnresolvedSignature<'ast> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(
                f,
                "Signature(inputs: {:?}, outputs: {:?})",
                self.inputs, self.outputs
            )
        }
    }

    impl<'ast> fmt::Display for UnresolvedSignature<'ast> {
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

    impl<'ast> UnresolvedSignature<'ast> {
        pub fn new() -> UnresolvedSignature<'ast> {
            UnresolvedSignature::default()
        }

        pub fn generics(mut self, generics: Vec<ConstantGenericNode<'ast>>) -> Self {
            self.generics = generics;
            self
        }

        pub fn inputs(mut self, inputs: Vec<UnresolvedTypeNode<'ast>>) -> Self {
            self.inputs = inputs;
            self
        }

        pub fn outputs(mut self, outputs: Vec<UnresolvedTypeNode<'ast>>) -> Self {
            self.outputs = outputs;
            self
        }
    }
}
