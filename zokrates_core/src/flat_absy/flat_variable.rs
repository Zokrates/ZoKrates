use std::fmt;

#[derive(Serialize, Deserialize, Clone, PartialEq, Hash, Eq)]
pub struct FlatVariable {
    pub id: usize,
    pub binary: Option<usize>
}

impl FlatVariable {
    pub fn new(id: usize) -> Self {
        FlatVariable {
            id,
            binary: None
        }
    }

    pub fn binary(id: usize, bit: usize) -> Self {
        FlatVariable {
            id,
            binary: Some(bit)
        }
    }

    pub fn one() -> Self {
        Self::new(0)
    }
}

impl fmt::Display for FlatVariable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.binary {
            Some(b) => write!(f, "{}_b{}", self.id, b),
            None => write!(f, "{}", self.id),
        }
    }
}

impl fmt::Debug for FlatVariable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.binary {
            Some(b) => write!(f, "FlatVariable(id: {}, bit: {})", self.id, b),
            None => write!(f, "FlatVariable(id: {})", self.id),
        }
    }
}