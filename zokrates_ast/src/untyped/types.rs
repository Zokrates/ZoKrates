use super::ExpressionNode;
use super::UnresolvedTypeNode;
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
    User(UserTypeId, Option<Vec<Option<ExpressionNode<'ast>>>>),
    Tuple(Vec<UnresolvedTypeNode<'ast>>),
}

impl<'ast> fmt::Display for UnresolvedType<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            UnresolvedType::FieldElement => write!(f, "field"),
            UnresolvedType::Boolean => write!(f, "bool"),
            UnresolvedType::Uint(bitwidth) => write!(f, "u{}", bitwidth),
            UnresolvedType::Array(ref ty, ref size) => write!(f, "{}[{}]", ty, size),
            UnresolvedType::Tuple(ref elements) => {
                write!(f, "(")?;
                match elements.len() {
                    1 => write!(f, "{},", elements[0]),
                    _ => write!(
                        f,
                        "{}",
                        elements
                            .iter()
                            .map(|e| e.to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                }?;
                write!(f, ")")
            }
            UnresolvedType::User(ref id, ref generics) => {
                write!(
                    f,
                    "{}{}",
                    id,
                    generics
                        .as_ref()
                        .map(|generics| {
                            format!(
                                "<{}>",
                                generics
                                    .iter()
                                    .map(|e| {
                                        e.as_ref()
                                            .map(|e| e.to_string())
                                            .unwrap_or_else(|| "_".to_string())
                                    })
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            )
                        })
                        .unwrap_or_default()
                )
            }
        }
    }
}

impl<'ast> UnresolvedType<'ast> {
    pub fn array(ty: UnresolvedTypeNode<'ast>, size: ExpressionNode<'ast>) -> Self {
        UnresolvedType::Array(box ty, size)
    }
}

pub use self::signature::UnresolvedSignature;

mod signature {
    use crate::untyped::ConstantGenericNode;
    use std::fmt;

    use crate::untyped::UnresolvedTypeNode;

    #[derive(Clone, PartialEq, Default)]
    pub struct UnresolvedSignature<'ast> {
        pub generics: Vec<ConstantGenericNode<'ast>>,
        pub inputs: Vec<UnresolvedTypeNode<'ast>>,
        pub output: Option<UnresolvedTypeNode<'ast>>,
    }

    impl<'ast> fmt::Debug for UnresolvedSignature<'ast> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(
                f,
                "Signature(inputs: {:?}, output: {:?})",
                self.inputs, self.output
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
            match &self.output {
                Some(ty) => write!(f, ") -> {}", ty),
                None => write!(f, ")"),
            }
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

        pub fn output(mut self, output: UnresolvedTypeNode<'ast>) -> Self {
            self.output = Some(output);
            self
        }
    }
}
