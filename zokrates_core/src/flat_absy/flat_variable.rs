use std::fmt;

#[derive(Serialize, Deserialize, Clone, PartialEq, Hash, Eq, Ord, PartialOrd, Copy)]
pub struct FlatVariable {
    id: isize,
    binary: Option<usize>
}

impl FlatVariable {
    pub fn new(id: usize) -> Self {
        FlatVariable {
            id: id as isize,
            binary: None
        }
    }

    pub fn with_binary(mut self, bit: usize) -> Self {
        self.binary = Some(bit);
        self
    }

    pub fn with_id(mut self, id: usize) -> Self {
        self.id = id as isize;
        self
    }

    pub fn one() -> Self {
        Self::new(0)
    }

    pub fn public(id: usize) -> Self {
        FlatVariable {
            id: - (id as isize) - 1,
            binary: None
        }
    }

    pub fn binary(&self) -> Option<usize> {
        self.binary
    }

    pub fn id(&self) -> usize {
        assert!(self.id >= 0);
        self.id as usize
    }
}

impl fmt::Display for FlatVariable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.binary {
            Some(b) => write!(f, "_{}_b{}", self.id, b),
            None =>  match self.id >= 0 {
                true => write!(f, "_{}", self.id),
                false => write!(f, "~out_{}", - self.id - 1)
            }
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