pub use crate::types::signature::Signature;
pub use crate::types::signature::UnresolvedSignature;
use std::fmt;

pub type Identifier<'ast> = &'ast str;

pub type MemberId = String;

pub type UserTypeId = String;

mod signature;

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Type {
    FieldElement,
    Boolean,
    Array(Box<Type>, usize),
    Struct(Vec<(MemberId, Type)>),
}

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Debug)]
pub enum UnresolvedType {
    FieldElement,
    Boolean,
    Array(Box<UnresolvedType>, usize),
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

impl UnresolvedType {
    pub fn array(ty: UnresolvedType, size: usize) -> Self {
        UnresolvedType::Array(box ty, size)
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

    pub fn to_slug(&self) -> String {
        format!("{}_{}", self.id, self.signature.to_slug())
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
