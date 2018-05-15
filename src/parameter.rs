use std::fmt;
use substitution::Substitution;

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub struct Parameter {
    pub id: String,
    pub private: bool,
}

impl fmt::Display for Parameter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let visibility = if self.private { "private " } else { "" };
        write!(f, "{}{}", visibility, self.id)
    }
}

impl fmt::Debug for Parameter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Parameter(id: {:?})", self.id)
    }
}

impl Parameter {
    pub fn apply_substitution(&self, substitution: &Substitution) -> Parameter {
        Parameter {
            id: substitution.get(&self.id).unwrap().to_string(),
            private: self.private
        }
    }
}