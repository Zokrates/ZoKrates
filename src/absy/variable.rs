use std::fmt;
use types::Type;

#[derive(Serialize, Deserialize, Clone, PartialEq, Hash, Eq)]
pub struct Variable {
    pub id: String,
    pub _type: Type
}

impl Variable {
    pub fn get_type(&self) -> Type {
        self._type.clone()
    }
}

impl<S: Into<String>> From<S> for Variable {
    fn from(s: S) -> Self {
        Variable {
            id: s.into(),
            _type: Type::FieldElement
        }
    }
}

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} {}",
            self._type,
            self.id,
        )
    }
}

impl fmt::Debug for Variable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Variable(type: {:?}, id: {:?})",
            self._type,
            self.id,
        )
    }
}