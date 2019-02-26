use absy;
use std::fmt;
use types::Type;

#[derive(Serialize, Deserialize, Clone, PartialEq, Hash, Eq)]
pub struct Variable {
    pub id: String,
    pub _type: Type,
}

impl Variable {
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

impl From<absy::Variable> for Variable {
    fn from(v: absy::Variable) -> Variable {
        Variable {
            id: v.id,
            _type: v._type,
        }
    }
}
