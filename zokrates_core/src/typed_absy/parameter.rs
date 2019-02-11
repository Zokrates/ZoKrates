use absy;
use std::fmt;
use typed_absy::Variable;

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub struct Parameter {
    pub id: Variable,
    pub private: bool,
}

impl Parameter {
    #[cfg(test)]
    pub fn private(v: Variable) -> Self {
        Parameter {
            id: v,
            private: true,
        }
    }
}

impl fmt::Display for Parameter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let visibility = if self.private { "private " } else { "" };
        write!(f, "{}{} {}", visibility, self.id.get_type(), self.id.id)
    }
}

impl fmt::Debug for Parameter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Parameter(variable: {:?})", self.id)
    }
}

impl From<absy::Parameter> for Parameter {
    fn from(p: absy::Parameter) -> Parameter {
        Parameter {
            private: p.private,
            id: p.id.value.into(),
        }
    }
}
