use absy::{Node, VariableNode};
use std::fmt;

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub struct Parameter {
    pub id: VariableNode,
    pub private: bool,
}

impl Parameter {
    pub fn public(v: VariableNode) -> Self {
        Parameter {
            id: v,
            private: false,
        }
    }

    pub fn private(v: VariableNode) -> Self {
        Parameter {
            id: v,
            private: true,
        }
    }
}

pub type ParameterNode = Node<Parameter>;

impl fmt::Display for Parameter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let visibility = if self.private { "private " } else { "" };
        write!(
            f,
            "{}{} {}",
            visibility,
            self.id.value.get_type(),
            self.id.value.id
        )
    }
}

impl fmt::Debug for Parameter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Parameter(variable: {:?})", self.id)
    }
}
