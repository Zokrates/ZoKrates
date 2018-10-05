use std::fmt;
use substitution::Substitution;


// A variable in a constraint system
// id > 0 for intermediate variables
// id == 0 for ~one
// id < 0 for public outputs
#[derive(Serialize, Deserialize, Clone, PartialEq, Hash, Eq, Ord, PartialOrd, Copy)]
pub struct FlatVariable {
    id: isize,
}

impl FlatVariable {
    pub fn new(id: usize) -> Self {
        FlatVariable {
            id: 1 + id as isize,
        }
    }

    pub fn one() -> Self {
        FlatVariable {
            id: 0,
        }
    }

    pub fn public(id: usize) -> Self {
        FlatVariable {
            id: - (id as isize) - 1,
        }
    }

    pub fn id(&self) -> usize {
        assert!(self.id > 0);
        (self.id as usize) - 1
    }
}

impl fmt::Display for FlatVariable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.id {
            0 => write!(f, "~one"),
            i if i > 0 => write!(f, "_{}", i + 1),
            i => write!(f, "~out_{}", - (i + 1))
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

    pub fn is_output(&self) -> bool {
        self.id < 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn one() {
        assert_eq!(FlatVariable::one().id, 0);
    }

    #[test]
    fn public() {
        assert_eq!(FlatVariable::public(0).id, - 1);
        assert_eq!(FlatVariable::public(42).id, - 43);
    }

    #[test]
    fn private() {
        assert_eq!(FlatVariable::new(0).id, 1);
        assert_eq!(FlatVariable::new(42).id, 43);
    }
}