pub use crate::types::signature::Signature;
use std::fmt;

pub mod conversions;
mod signature;

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Type {
    FieldElement,
    Boolean,
    FieldElementArray(usize),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Type::FieldElement => write!(f, "field"),
            Type::Boolean => write!(f, "bool"),
            Type::FieldElementArray(size) => write!(f, "{}[{}]", Type::FieldElement, size),
        }
    }
}

impl fmt::Debug for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Type::FieldElement => write!(f, "field"),
            Type::Boolean => write!(f, "bool"),
            Type::FieldElementArray(size) => write!(f, "{}[{}]", Type::FieldElement, size),
        }
    }
}

impl Type {
    // the number of field elements the type maps to
    pub fn get_primitive_count(&self) -> usize {
        match self {
            Type::FieldElement => 1,
            Type::Boolean => 1,
            Type::FieldElementArray(size) => size * Type::FieldElement.get_primitive_count(),
        }
    }

    fn to_slug(&self) -> String {
        match *self {
            Type::FieldElement => String::from("f"),
            Type::Boolean => String::from("b"),
            Type::FieldElementArray(size) => format!("{}[{}]", Type::FieldElement.to_slug(), size), // TODO differentiate types?
        }
    }
}

#[derive(Serialize, Deserialize, Clone, PartialEq, Hash, Eq)]
pub struct Variable {
    pub id: Identifier,
    pub _type: Type,
}

impl Variable {
    pub fn new<S: Into<String>>(id: S, t: Type) -> Variable {
        Variable {
            id: id.into(),
            _type: t,
        }
    }

    pub fn field_element<S: Into<String>>(id: S) -> Variable {
        Variable {
            id: id.into(),
            _type: Type::FieldElement,
        }
    }

    pub fn boolean<S: Into<String>>(id: S) -> Variable {
        Variable {
            id: id.into(),
            _type: Type::Boolean,
        }
    }

    pub fn field_array<S: Into<String>>(id: S, size: usize) -> Variable {
        Variable {
            id: id.into(),
            _type: Type::FieldElementArray(size),
        }
    }

    pub fn get_type(&self) -> Type {
        self._type.clone()
    }
}

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self._type, self.id,)
    }
}

impl fmt::Debug for Variable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Variable(type: {:?}, id: {:?})", self._type, self.id,)
    }
}

type Identifier = String;

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct FunctionKey {
    pub id: Identifier,
    pub signature: Signature,
}

impl FunctionKey {
    pub fn with_id<S: Into<Identifier>>(id: S) -> Self {
        FunctionKey {
            id: id.into(),
            signature: Signature::new(),
        }
    }

    pub fn signature(mut self, signature: Signature) -> Self {
        self.signature = signature;
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn array() {
        let t = Type::FieldElementArray(42);
        assert_eq!(t.get_primitive_count(), 42);
        assert_eq!(t.to_slug(), "f[42]");
    }
}
