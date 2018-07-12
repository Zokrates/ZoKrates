use std::fmt;
use substitution::Substitution;
use absy::Variable;

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub struct Parameter {
    pub id: Variable,
    pub private: bool,
}

impl fmt::Display for Parameter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let visibility = if self.private { "private " } else { "" };
        write!(f, "{}{} {}", visibility, self.id._type, self.id.id)
    }
}

impl fmt::Debug for Parameter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Parameter(variable: {:?})", self.id)
    }
}

impl Parameter {
    pub fn apply_substitution(&self, substitution: &Substitution) -> Parameter {
        Parameter {
            id: Variable {
                id: substitution.get(&self.id.id).unwrap().to_string(),
                _type: self.id._type.clone()
            },
            private: self.private
        }
    }
}

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub struct FlatParameter {
    pub id: String,
    pub private: bool,
}

impl fmt::Display for FlatParameter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let visibility = if self.private { "private " } else { "" };
        write!(f, "{}{}", visibility, self.id)
    }
}

impl fmt::Debug for FlatParameter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Parameter(id: {:?})", self.id)
    }
}

impl FlatParameter {
    pub fn apply_substitution(&self, substitution: &Substitution) -> FlatParameter {
        FlatParameter {
            id: substitution.get(&self.id).unwrap().to_string(),
            private: self.private
        }
    }
}