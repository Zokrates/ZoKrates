use absy::ExpressionNode;
use absy::UnresolvedTypeNode;
use std::fmt;

pub type Identifier<'ast> = &'ast str;

pub type MemberId = String;

pub type UserTypeId = String;

#[derive(PartialEq, Debug, Clone)]
pub enum UnresolvedType<'ast, T> {
    FieldElement,
    Boolean,
    Uint(usize),
    Array(Box<UnresolvedTypeNode<'ast, T>>, ExpressionNode<'ast, T>),
    User(UserTypeId),
}

impl<'ast, T: fmt::Display> fmt::Display for UnresolvedType<'ast, T> {
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

impl<'ast, T> UnresolvedType<'ast, T> {
    pub fn array(ty: UnresolvedTypeNode<'ast, T>, size: ExpressionNode<'ast, T>) -> Self {
        UnresolvedType::Array(box ty, size)
    }
}

pub type FunctionIdentifier<'ast> = &'ast str;

pub use self::signature::UnresolvedSignature;

mod signature {
    use std::fmt;

    use absy::UnresolvedTypeNode;

    #[derive(Clone, PartialEq)]
    pub struct UnresolvedSignature<'ast, T> {
        pub inputs: Vec<UnresolvedTypeNode<'ast, T>>,
        pub outputs: Vec<UnresolvedTypeNode<'ast, T>>,
    }

    impl<'ast, T: fmt::Debug> fmt::Debug for UnresolvedSignature<'ast, T> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(
                f,
                "Signature(inputs: {:?}, outputs: {:?})",
                self.inputs, self.outputs
            )
        }
    }

    impl<'ast, T: fmt::Display> fmt::Display for UnresolvedSignature<'ast, T> {
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

    impl<'ast, T> UnresolvedSignature<'ast, T> {
        pub fn new() -> UnresolvedSignature<'ast, T> {
            UnresolvedSignature {
                inputs: vec![],
                outputs: vec![],
            }
        }

        pub fn inputs(mut self, inputs: Vec<UnresolvedTypeNode<'ast, T>>) -> Self {
            self.inputs = inputs;
            self
        }

        pub fn outputs(mut self, outputs: Vec<UnresolvedTypeNode<'ast, T>>) -> Self {
            self.outputs = outputs;
            self
        }
    }
}
