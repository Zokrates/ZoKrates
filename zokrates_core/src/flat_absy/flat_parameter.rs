use flat_absy::flat_variable::FlatVariable;
use std::fmt;
use substitution::Substitution;

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub struct FlatParameter {
    pub id: FlatVariable,
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
        write!(f, "FlatParameter(id: {:?})", self.id)
    }
}

impl FlatParameter {
    pub fn apply_substitution(self, substitution: &Substitution) -> FlatParameter {
        FlatParameter {
            id: substitution.get(&self.id).unwrap(),
            private: self.private
        }
    }
}