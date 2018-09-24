use std::fmt;
use substitution::Substitution;

#[derive(Serialize, Deserialize, Clone, PartialEq, Hash, Eq, Ord, PartialOrd, Copy)]
pub struct FlatVariable {
    id: isize,
}

impl FlatVariable {
    pub fn new(id: usize) -> Self {
        FlatVariable {
            id: id as isize,
        }
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
        }
    }

    pub fn id(&self) -> usize {
        assert!(self.id >= 0);
        self.id as usize
    }
}

impl fmt::Display for FlatVariable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.id >= 0 {
            true => write!(f, "_{}", self.id),
            false => write!(f, "~out_{}", - self.id - 1)
        }
    }
}

impl fmt::Debug for FlatVariable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "FlatVariable(id: {})", self.id)
    }
}

impl FlatVariable {
    pub fn apply_substitution(self, substitution: &Substitution, should_fallback: bool) -> Self {
        match should_fallback {
            true => substitution.get(&self).unwrap_or(self),
            false => substitution.get(&self).unwrap()
        }
    }

    pub fn is_public(&self) -> bool {
        self.id < 0
    }
}